/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import TauCeti.Geometry.Toric.Algebraic.Fan.Over

import TauCeti.AlgebraicGeometry.Morphisms.Separated

/-!
# Separatedness of toric fan schemes

The chart of the intersection of two cones represents the overlap of their affine charts.
Its morphism to the product of the charts over `ℂ` is a closed immersion, since the dual
semigroups of the two cones generate the dual semigroup of their intersection. These product
charts cover the target of the diagonal, so the structure morphism of the fan scheme is
separated. Together with density of the torus, this allows morphisms into a fan scheme
to be compared on the dense torus of a reduced toric source.

The proof uses Tau Ceti's `Fan.dualSemigroup_inf_eq_sup` and `IsSeparated.of_openCover`,
the affine-cover criterion of the Stacks Project, Lemma 26.21.7.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Multiplicative
open scoped TensorProduct

namespace TauCeti.Toric.Fan

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

/-- The chart of the intersection cone is the scheme-theoretic intersection of the two
affine charts in the realization of the fan. -/
theorem isPullback_affineToricOverlap (σ τ : Φ.cones) :
    IsPullback (Φ.affineToricOverlapLeft σ τ) (Φ.affineToricOverlapRight σ τ)
      (Φ.affineToricChartι σ) (Φ.affineToricChartι τ) := by
  have := Φ.isOpenImmersion_affineToricOverlapRight σ τ
  refine IsOpenImmersion.isPullback _ _ _ _
    (Φ.affineToricOverlap_comp_affineToricChartι σ τ).symm ?_
  apply SetLike.ext
  intro y
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange, Scheme.Hom.mem_opensRange]
  constructor
  · rintro ⟨x, hxy⟩
    obtain ⟨z, -, hz⟩ := (Φ.affineToricChartι_eq_affineToricChartι_iff x y).mp hxy
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, (Φ.affineToricChartι_eq_affineToricChartι_iff _ _).mpr ⟨z, rfl, rfl⟩⟩

/-- The coordinate ring map for the overlap inside the product of its two charts. -/
private noncomputable abbrev affineToricOverlapTensorMap (σ τ : Φ.cones) :
    affineCoordinateRing Φ.lattice σ.val ⊗[ℂ] affineCoordinateRing Φ.lattice τ.val →ₐ[ℂ]
      affineCoordinateRing Φ.lattice (σ.val ⊓ τ.val) :=
  Algebra.TensorProduct.lift
    (faceAffineCoordinateRingMap Φ.lattice (Φ.inf_isFaceOf_left σ.property τ.property))
    (faceAffineCoordinateRingMap Φ.lattice (Φ.inf_isFaceOf_right σ.property τ.property))
    (fun _ _ ↦ Commute.all _ _)

private theorem surjective_affineToricOverlapTensorMap (σ τ : Φ.cones) :
    Function.Surjective (Φ.affineToricOverlapTensorMap σ τ) := by
  let F := Φ.affineToricOverlapTensorMap σ τ
  intro f
  induction f using MonoidAlgebra.induction_on with
  | of m =>
    obtain ⟨a, ha, b, hb, hab⟩ := AddSubmonoid.mem_sup.mp
      ((Φ.dualSemigroup_inf_eq_sup σ.property τ.property).le (toAdd m).property)
    refine ⟨MonoidAlgebra.single (ofAdd ⟨a, ha⟩) 1 ⊗ₜ[ℂ]
      MonoidAlgebra.single (ofAdd ⟨b, hb⟩) 1, ?_⟩
    simp only [affineToricOverlapTensorMap, Algebra.TensorProduct.lift_tmul,
      faceAffineCoordinateRingMap_single,
      MonoidAlgebra.single_mul_single, one_mul, MonoidAlgebra.of_apply]
    congr 1
    apply ofAdd.injective
    exact Subtype.ext hab
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, F.map_add a b⟩
  | smul r x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨r • a, map_smul F r a⟩

/-- The intersection of two affine toric charts is a closed subscheme of their product over
`ℂ`. This map is the restriction of the diagonal to that product chart. -/
private theorem isClosedImmersion_mapDesc_affineToricChartι (σ τ : Φ.cones) :
    IsClosedImmersion (pullback.mapDesc (Φ.affineToricChartι σ) (Φ.affineToricChartι τ)
      Φ.algebraicRealizationStructureMap) := by
  let e := (Φ.isPullback_affineToricOverlap σ τ).isoPullback
  let q := pullback.congrHom (Φ.affineToricChartι_comp_algebraicRealizationStructureMap σ)
    (Φ.affineToricChartι_comp_algebraicRealizationStructureMap τ)
  let p := pullbackSpecIso ℂ (affineCoordinateRing Φ.lattice σ.val)
    (affineCoordinateRing Φ.lattice τ.val)
  let f := pullback.mapDesc (Φ.affineToricChartι σ) (Φ.affineToricChartι τ)
    Φ.algebraicRealizationStructureMap
  let F := Φ.affineToricOverlapTensorMap σ τ
  have h : (e.hom ≫ f ≫ q.hom) ≫ p.hom = Spec.map (CommRingCat.ofHom F.toRingHom) := by
    rw [← cancel_mono p.inv, Category.assoc, p.hom_inv_id, Category.comp_id]
    apply pullback.hom_ext
    · have hleft : F.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom (R := ℂ)) =
          (faceAffineCoordinateRingMap Φ.lattice
            (Φ.inf_isFaceOf_left σ.property τ.property)).toRingHom :=
        congrArg AlgHom.toRingHom (Algebra.TensorProduct.lift_comp_includeLeft _ _ _)
      simp only [Category.assoc, p, pullbackSpecIso_inv_fst, q, pullback.congrHom_hom,
        pullback.lift_fst, Category.comp_id, f, e, IsPullback.isoPullback_hom_fst,
        affineToricOverlapLeft_def, faceAffineToricSchemeMap_def, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      exact congrArg (fun φ ↦ Spec.map (CommRingCat.ofHom φ)) hleft.symm
    · simp [e, f, q, p, F, affineToricOverlapTensorMap, faceAffineToricSchemeMap_def,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← AlgHom.comp_toRingHom]
  have hclosed : IsClosedImmersion (Spec.map (CommRingCat.ofHom F.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _
      (Φ.surjective_affineToricOverlapTensorMap σ τ)
  rwa [← h, MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion,
    MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion,
    MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion] at hclosed

/-- The algebraic realization of any fan is separated over `ℂ`. -/
instance isSeparated_algebraicRealizationStructureMap :
    IsSeparated Φ.algebraicRealizationStructureMap := by
  refine @IsSeparated.of_openCover _ _ Φ.algebraicRealizationStructureMap
    Φ.affineToricOpenCover ?_ ?_
  · intro σ
    let cone : Φ.cones := σ
    -- The cover's bundled index is definitionally its cone type.
    suffices IsSeparated (Φ.affineToricChartι cone ≫ Φ.algebraicRealizationStructureMap) from this
    rw [Φ.affineToricChartι_comp_algebraicRealizationStructureMap cone]
    infer_instance
  · exact fun σ τ _ ↦ Φ.isClosedImmersion_mapDesc_affineToricChartι σ τ

/-- The underlying scheme of the algebraic realization of any fan is separated. -/
instance isSeparated_algebraicRealization : Φ.algebraicRealization.IsSeparated :=
  Scheme.IsSeparated.of_isSeparated Φ.algebraicRealizationStructureMap

end TauCeti.Toric.Fan
