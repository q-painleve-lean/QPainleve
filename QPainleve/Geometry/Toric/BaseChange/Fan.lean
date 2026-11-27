/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import QPainleve.Geometry.Toric.RegularChart
public import TauCeti.Geometry.Toric.Algebraic.BaseChange.Fan

import QPainleve.AlgebraicGeometry.Scheme.Factorial
import TauCeti.AlgebraicGeometry.Morphisms.Separated

/-!
# Separatedness and smoothness of toric fan schemes over a ring

The chart of the intersection of two cones represents the overlap of their affine charts.
Its morphism to the product of the charts over the coefficient ring is a closed immersion.
The dual semigroups of the two cones generate the dual semigroup of their intersection.
The product charts cover the target of the diagonal, so the structure morphism of the fan scheme is
separated. Together with density of the torus, this allows morphisms into a fan scheme
to be compared on the dense torus of a reduced toric source.

A regular fan is smooth over its coefficient ring, with relative dimension the lattice rank.
This follows from the polynomial and Laurent coordinates on its affine charts.

The proof uses Tau Ceti's `Fan.dualSemigroup_inf_eq_sup` and `IsSeparated.of_openCover`,
the affine-cover criterion of the Stacks Project, Lemma 26.21.7.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace TauCeti.Toric.Fan

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (R : Type u) [CommRing R]

local notation "left[" σ "," τ "]" =>
  faceAffineChartMap R Φ.lattice (Φ.inf_isFaceOf_left (Subtype.property σ) (Subtype.property τ))
local notation "right[" σ "," τ "]" =>
  faceAffineChartMap R Φ.lattice (Φ.inf_isFaceOf_right (Subtype.property σ) (Subtype.property τ))

/-- The affine chart of the intersection cone is the pullback of the two chart inclusions. -/
theorem isPullback_affineChartι_inf (σ τ : Φ.cones) :
    IsPullback left[σ,τ] right[σ,τ] (Φ.affineChartι R σ) (Φ.affineChartι R τ) := by
  have := (Φ.isToricCone τ.property).rational.isOpenImmersion_faceAffineChartMap R Φ.lattice
    (Φ.inf_isFaceOf_right σ.property τ.property)
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · rw [faceAffineChartMap_comp_affineChartι R (τ := σ ⊓ τ) (σ := σ),
      faceAffineChartMap_comp_affineChartι R (τ := σ ⊓ τ) (σ := τ)]
  · apply SetLike.ext
    intro y
    rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange, Scheme.Hom.mem_opensRange]
    constructor
    · rintro ⟨x, hxy⟩
      obtain ⟨z, -, hz⟩ := (Φ.affineChartι_apply_eq_affineChartι_apply_iff R x y).mp hxy
      exact ⟨z, hz⟩
    · rintro ⟨z, rfl⟩
      exact ⟨_, (Φ.affineChartι_apply_eq_affineChartι_apply_iff R _ _).mpr ⟨z, rfl, rfl⟩⟩

/-- The coordinate ring map for the overlap inside the product of its two charts. -/
private noncomputable abbrev affineChartOverlapTensorMap (σ τ : Φ.cones) :
    affineChartRing R Φ.lattice σ.val ⊗[R] affineChartRing R Φ.lattice τ.val →ₐ[R]
      affineChartRing R Φ.lattice (σ.val ⊓ τ.val) :=
  Algebra.TensorProduct.lift
    (faceAffineChartRingMap R Φ.lattice (Φ.inf_isFaceOf_left σ.property τ.property))
    (faceAffineChartRingMap R Φ.lattice (Φ.inf_isFaceOf_right σ.property τ.property))
    (fun _ _ ↦ Commute.all _ _)

private theorem surjective_affineChartOverlapTensorMap (σ τ : Φ.cones) :
    Function.Surjective (Φ.affineChartOverlapTensorMap R σ τ) := by
  let F := Φ.affineChartOverlapTensorMap R σ τ
  intro f
  induction f using AddMonoidAlgebra.induction_on with
  | of m =>
    obtain ⟨a, ha, b, hb, hab⟩ := AddSubmonoid.mem_sup.mp
      ((Φ.dualSemigroup_inf_eq_sup σ.property τ.property).le m.property)
    refine ⟨AddMonoidAlgebra.single ⟨a, ha⟩ 1 ⊗ₜ[R]
      AddMonoidAlgebra.single ⟨b, hb⟩ 1, ?_⟩
    simp only [affineChartOverlapTensorMap, Algebra.TensorProduct.lift_tmul,
      faceAffineChartRingMap_single,
      AddMonoidAlgebra.single_mul_single, one_mul, AddMonoidAlgebra.of_apply]
    congr 1
    exact Subtype.ext hab
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, F.map_add a b⟩
  | smul r x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨r • a, map_smul F r a⟩

/-- The intersection of two affine toric charts is a closed subscheme of their product over
the coefficient ring. This map is the restriction of the diagonal to that product chart. -/
private theorem isClosedImmersion_mapDesc_affineChartι (σ τ : Φ.cones) :
    IsClosedImmersion (pullback.mapDesc (Φ.affineChartι R σ) (Φ.affineChartι R τ)
      (Φ.finiteFanSchemeToSpec R)) := by
  let e := (Φ.isPullback_affineChartι_inf R σ τ).isoPullback
  let q := pullback.congrHom (Φ.affineChartι_finiteFanSchemeToSpec R σ)
    (Φ.affineChartι_finiteFanSchemeToSpec R τ)
  let p := pullbackSpecIso R (affineChartRing R Φ.lattice σ.val)
    (affineChartRing R Φ.lattice τ.val)
  let f := pullback.mapDesc (Φ.affineChartι R σ) (Φ.affineChartι R τ)
    (Φ.finiteFanSchemeToSpec R)
  let F := Φ.affineChartOverlapTensorMap R σ τ
  have h : (e.hom ≫ f ≫ q.hom) ≫ p.hom = Spec.map (CommRingCat.ofHom F.toRingHom) := by
    rw [← cancel_mono p.inv, Category.assoc, p.hom_inv_id, Category.comp_id]
    apply pullback.hom_ext
    · have hleft : F.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom (R := R)) =
          (faceAffineChartRingMap R Φ.lattice
            (Φ.inf_isFaceOf_left σ.property τ.property)).toRingHom :=
        congrArg AlgHom.toRingHom (Algebra.TensorProduct.lift_comp_includeLeft _ _ _)
      simp only [Category.assoc, p, pullbackSpecIso_inv_fst, q, pullback.congrHom_hom,
        pullback.lift_fst, Category.comp_id, f, e, IsPullback.isoPullback_hom_fst,
        faceAffineChartMap_def, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      exact congrArg (fun φ ↦ Spec.map (CommRingCat.ofHom φ)) hleft.symm
    · simp [e, f, q, p, F, affineChartOverlapTensorMap, faceAffineChartMap_def,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← AlgHom.comp_toRingHom]
  have hclosed : IsClosedImmersion (Spec.map (CommRingCat.ofHom F.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _
      (Φ.surjective_affineChartOverlapTensorMap R σ τ)
  rwa [← h, MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion,
    MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion,
    MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion] at hclosed

/-- A toric fan scheme is separated over its coefficient ring. -/
instance isSeparated_finiteFanSchemeToSpec :
    IsSeparated (Φ.finiteFanSchemeToSpec R) := by
  refine @IsSeparated.of_openCover _ _ (Φ.finiteFanSchemeToSpec R)
    (Φ.affineChartOpenCover R) ?_ ?_
  · intro σ
    let cone : Φ.cones := σ
    -- The cover's bundled index is definitionally its cone type.
    suffices IsSeparated (Φ.affineChartι R cone ≫ (Φ.finiteFanSchemeToSpec R)) from this
    rw [Φ.affineChartι_finiteFanSchemeToSpec R cone]
    infer_instance
  · exact fun σ τ _ ↦ Φ.isClosedImmersion_mapDesc_affineChartι R σ τ

/-- A toric fan scheme is separated as a scheme. -/
instance isSeparated_finiteFanScheme : (Φ.finiteFanScheme R).IsSeparated :=
  Scheme.IsSeparated.of_isSeparated (Φ.finiteFanSchemeToSpec R)

/-- The scheme of a regular fan is smooth over the coefficient ring of relative dimension the
lattice rank. -/
theorem smoothOfRelativeDimension_finiteFanSchemeToSpec {N : Type u}
    {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
    (Φ : Fan i) (R : Type u) [CommRing R] (hΦ : Φ.IsRegular) :
    SmoothOfRelativeDimension (Module.finrank ℤ N) (Φ.finiteFanSchemeToSpec R) := by
  let n := Module.finrank ℤ N
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (@RingHom.IsStandardSmoothOfRelativeDimension n))
  apply (IsZariskiLocalAtSource.iff_of_openCover
    (P := @SmoothOfRelativeDimension n) (Φ.affineChartOpenCover R)).2
  intro σ
  let cone : Φ.cones := σ
  suffices SmoothOfRelativeDimension n
    (Φ.affineChartι R cone ≫ Φ.finiteFanSchemeToSpec R) from this
  rw [Φ.affineChartι_finiteFanSchemeToSpec R cone]
  exact (isRegular_iff.mp hΦ cone.val cone.property).smoothOfRelativeDimension_affineChart
    Φ.lattice

/-- A regular fan defines a smooth scheme over its coefficient ring. -/
theorem smooth_finiteFanSchemeToSpec {N : Type u} {V : Type*}
    [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
    (Φ : Fan i) (R : Type u) [CommRing R] (hΦ : Φ.IsRegular) :
    Smooth (Φ.finiteFanSchemeToSpec R) := by
  let := Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec R hΦ
  exact SmoothOfRelativeDimension.smooth (Module.finrank ℤ N) _

/-- All stalks of a regular toric scheme over a factorial ring are factorial. -/
theorem uniqueFactorizationMonoid_stalk_finiteFanScheme {N R : Type u}
    {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
    [CommRing R] [UniqueFactorizationMonoid R] (Φ : Fan i) (hΦ : Φ.IsRegular)
    (x : Φ.finiteFanScheme R) :
    UniqueFactorizationMonoid ((Φ.finiteFanScheme R).presheaf.stalk x) := by
  obtain ⟨σ, y, rfl⟩ := Φ.exists_affineChartι_apply_eq R x
  let A := CommRingCat.of (affineChartRing R Φ.lattice σ.val)
  have : UniqueFactorizationMonoid A :=
    (isRegular_iff.mp hΦ σ.val σ.property).uniqueFactorizationMonoid_affineChartRing R Φ.lattice
  exact (asIso ((Φ.affineChartι R σ).stalkMap y)).commRingCatIsoToRingEquiv.toMulEquiv.symm
    |>.uniqueFactorizationMonoid (uniqueFactorizationMonoid_stalk_Spec A y)

end TauCeti.Toric.Fan
