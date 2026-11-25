/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.LineBundle.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra.DisjointSections
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.CoordinateMap

/-!
# Affine coordinates of line-quotient sections

In a polynomial projective-bundle chart, the section of a line quotient is
given by the coordinates of the quotient in the chosen frames. This identifies
a summand quotient with the corresponding coordinate section of a split ruled
surface. The section uses the quotient convention of [Stacks, Section 27.21][stacks-01OA].

[stacks-01OA]: https://stacks.math.columbia.edu/tag/01OA
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Proj CategoryTheory
open TauCeti.AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank

section Coordinates

variable {R M L : Type u} [CommRing R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid L] [Module R L]

local notation "𝒮[" M "]" => TauCeti.SymmetricAlgebra.homogeneousSubmodule R M

private theorem map_irrelevant_eq_top_of_lift_apply_eq_one
    (l : L →ₗ[R] R) (v : L) (hv : l v = 1) :
    (HomogeneousIdeal.irrelevant 𝒮[L]).toIdeal.map (SymmetricAlgebra.lift l).toRingHom = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← hv, ← SymmetricAlgebra.lift_ι_apply]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem 𝒮[L] one_pos
    (SymmetricAlgebra.ι_mem_homogeneousSubmodule R L v))

private theorem fromOfGlobalSections_lift_comp_projToSpec (l : L →ₗ[R] R)
    (hl : (HomogeneousIdeal.irrelevant 𝒮[L]).toIdeal.map
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (SymmetricAlgebra.lift l).toRingHom) = ⊤) :
    fromOfGlobalSections 𝒮[L]
        ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (SymmetricAlgebra.lift l).toRingHom) hl ≫
      TauCeti.SymmetricAlgebra.projToSpec R L = 𝟙 _ := by
  rw [TauCeti.SymmetricAlgebra.projToSpec_def, fromOfGlobalSections_toSpecZero_assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h :
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (SymmetricAlgebra.lift l).toRingHom).comp
        ((algebraMap (𝒮[L] 0) _).comp (algebraMap R (𝒮[L] 0))) =
      (Scheme.ΓSpecIso (.of R)).inv.hom := by
    ext r
    simp [← IsScalarTower.algebraMap_apply R (𝒮[L] 0) (SymmetricAlgebra R L)]
  rw [RingHom.comp_assoc, h]
  exact toSpecΓ_SpecMap_ΓSpecIso_inv _

private abbrev standardFrame (R : Type u) [CommRing R] :=
  (Pi.basisFun R (Fin 2)).reindex (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2))

private theorem lift_comp_gradedMap_eq_pointCoordinates
    (b : Module.Basis (ULift.{u} (Fin 2)) R M)
    (d : Module.Basis (ULift.{u} (Fin 1)) R L) (f : M →ₗ[R] L) (i : Fin 2) (a : R)
    (hi : f (b ⟨i⟩) = d ⟨0⟩) (hj : f (b ⟨i.rev⟩) = a • d ⟨0⟩) :
    (SymmetricAlgebra.lift (d.coord ⟨0⟩)).toRingHom.comp
        (SymmetricAlgebra.gradedMap R f).toRingHom =
      (projectiveLine.pointCoordinates R (RingHom.id R) i a).comp
        ((standardFrame R).fromPolynomialGradedHom.comp b.toPolynomialGradedHom).toRingHom := by
  let e := (SymmetricAlgebra.equivMvPolynomial (standardFrame R)).symm.toAlgHom.comp
    (SymmetricAlgebra.equivMvPolynomial b).toAlgHom
  let p : SymmetricAlgebra R (Fin 2 → R) →ₐ[R] R :=
    { toRingHom := projectiveLine.pointCoordinates R (RingHom.id R) i a
      commutes' := projectiveLine.pointCoordinates_algebraMap R _ i a }
  have h : (SymmetricAlgebra.lift (d.coord ⟨0⟩)).comp (SymmetricAlgebra.map R f) =
      p.comp e := by
    apply SymmetricAlgebra.algHom_ext
    apply b.ext
    intro j
    obtain ⟨j⟩ := j
    have he : e (SymmetricAlgebra.ι R M (b ⟨j⟩)) = projectiveLine.coord R j := by
      simp only [e, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
        SymmetricAlgebra.equivMvPolynomial_ι_apply, SymmetricAlgebra.equivMvPolynomial_symm_X]
      simp only [standardFrame, Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.ulift_apply,
        Pi.basisFun_apply]
      rw [projectiveLine.ι_eq_smul_coord_add_smul_coord R j]
      have hrev : j.rev ≠ j := by fin_cases j <;> decide
      simp [Pi.single_eq_of_ne hrev]
    have h : j = i ∨ j = i.rev := by fin_cases i <;> fin_cases j <;> decide
    -- Both compositions are evaluated on the generators determined by the source frame.
    change (SymmetricAlgebra.lift (d.coord ⟨0⟩))
        (SymmetricAlgebra.map R f (SymmetricAlgebra.ι R M (b ⟨j⟩))) =
      projectiveLine.pointCoordinates R (RingHom.id R) i a
        (e (SymmetricAlgebra.ι R M (b ⟨j⟩)))
    rw [SymmetricAlgebra.map_apply_ι, SymmetricAlgebra.lift_ι_apply, he]
    rcases h with rfl | rfl <;> simp [hi, hj, Module.Basis.coord_apply]
  refine RingHom.ext fun x ↦ ?_
  simpa only [RingHom.comp_apply, GradedRingHom.coe_toRingHom, SymmetricAlgebra.gradedMap_apply,
    GradedRingHom.comp_apply, Module.Basis.fromPolynomialGradedHom_apply,
    Module.Basis.toPolynomialGradedHom_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgHom.comp_apply, e, p, AlgHom.coe_mk, AlgEquiv.coe_toAlgHom] using
    DFunLike.congr_fun h x

end Coordinates

variable {X : Scheme.{u}} (E : FixedRank X 1) {F : QuasicoherentSheaf X}
  (q : F ⟶ (FiniteLocallyFreeSheaf.toQuasicoherent X).obj E.obj) [Epi q.hom]
  (U : X.AffineZariskiSite)

local notation "R[" U "]" => CommRingCat.carrier (Functor.obj
  (PresheafedSpace.presheaf (SheafedSpace.toPresheafedSpace
    (LocallyRingedSpace.toSheafedSpace (Scheme.toLocallyRingedSpace X))))
  (Opposite.op (Scheme.AffineZariskiSite.toOpens U)))
local notation "S[" M "]" =>
  ModuleCat.carrier (Functor.obj
    (Scheme.Modules.sectionsFunctor (Scheme.AffineZariskiSite.toOpens U)) M)
local notation "A[" F "]" =>
  ObjectProperty.FullSubcategory.obj (Functor.obj (gradedSymmetricAlgebra X) F)

/-- If a quotient takes one basis vector to the line frame and the other to a scalar times
that frame, its section in the polynomial projective-bundle chart is the point with
that normalized coordinate. In particular, a summand projection has coordinate zero. -/
theorem polynomialPoint_comp_relativeProjPolynomialChart_eq
    (b : Module.Basis (ULift.{u} (Fin 2)) R[U] S[F.obj])
    (d : Module.Basis (ULift.{u} (Fin 1)) R[U] S[E.obj.obj])
    (i : Fin 2) (a : R[U])
    (hi : ((Scheme.Modules.sectionsFunctor U.toOpens).map q.hom).hom (b ⟨i⟩) = d ⟨0⟩)
    (hj : ((Scheme.Modules.sectionsFunctor U.toOpens).map q.hom).hom (b ⟨i.rev⟩) =
      a • d ⟨0⟩) :
    projectiveLine.polynomialPoint R[U] (RingHom.id R[U]) i a ≫
      ((Pi.basisFun R[U] (Fin 2)).reindex
        (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2))).polynomialProjIso.inv ≫
      F.relativeProjPolynomialChart U b =
      U.property.fromSpec ≫ E.relativeProjSectionOfQuotient q := by
  let G := (FiniteLocallyFreeSheaf.toQuasicoherent X).obj E.obj
  let qΓ := ((Scheme.Modules.sectionsFunctor U.toOpens).map q.hom).hom
  let l := d.coord ⟨0⟩
  let φ := (Scheme.ΓSpecIso (.of R[U])).inv.hom.comp (SymmetricAlgebra.lift l).toRingHom
  have hφ : (HomogeneousIdeal.irrelevant
      (TauCeti.SymmetricAlgebra.homogeneousSubmodule R[U] S[E.obj.obj])).toIdeal.map φ = ⊤ := by
    rw [← Ideal.map_map, map_irrelevant_eq_top_of_lift_apply_eq_one l (d ⟨0⟩)
      (by
        dsimp only [l]
        exact (congrArg (fun g ↦ g ⟨0⟩) (d.repr_self ⟨0⟩)).trans Finsupp.single_eq_same),
      Ideal.map_top]
  let t := fromOfGlobalSections _ φ hφ
  let incl : QuasicoherentSheaf X ⥤ X.Modules := ObjectProperty.ι _
  have : Epi (incl.map q) := ‹Epi q.hom›
  have : (incl.obj F).IsQuasicoherent := F.property
  have : (incl.obj G).IsQuasicoherent := G.property
  have hsurj : Function.Surjective qΓ :=
    (incl.map q).app_surjective_of_epi_of_isAffineOpen U.toOpens U.property
  let f := SymmetricAlgebra.gradedMap R[U] qΓ
  have hf := SymmetricAlgebra.irrelevant_le_map_gradedMap_of_surjective qΓ hsurj
  have hproj : t ≫ (G.projSymmetricAlgebraSectionsIso U).hom ≫
      A[G].relativeProjCover.f U ≫ A[G].relativeProjToBase = U.property.fromSpec := by
    have hbase := A[G].relativeProjCover_f_relativeProjToBase U
    have hcoeff := G.projSymmetricAlgebraSectionsIso_hom_toSpecCoeff U
    -- These comparisons use the underlying modules of the bundled quasicoherent sheaves.
    erw [hbase, ← Category.assoc (G.projSymmetricAlgebraSectionsIso U).hom, hcoeff,
      ← Category.assoc t, fromOfGlobalSections_lift_comp_projToSpec l hφ, Category.id_comp]
  have hpoint :
      projectiveLine.polynomialPoint R[U] (RingHom.id R[U]) i a ≫
        (standardFrame R[U]).polynomialProjIso.inv ≫ b.polynomialProjIso.hom =
      t ≫ Proj.map f hf := by
    rw [projectiveLine.polynomialPoint_eq_fromGlobalSections,
      Module.Basis.polynomialProjIso_inv, Module.Basis.polynomialProjIso_hom,
      ← Proj.map_comp, Proj.fromOfGlobalSections_map, Proj.fromOfGlobalSections_map]
    congr 1
    simp only [φ, RingHom.comp_assoc]
    exact congrArg (Scheme.ΓSpecIso (.of R[U])).inv.hom.comp
      (lift_comp_gradedMap_eq_pointCoordinates b d qΓ i a hi hj).symm
  rw [F.relativeProjPolynomialChart_def, ← Category.assoc _ b.polynomialProjIso.hom,
    ← Category.assoc _ _ ((F.projSymmetricAlgebraSectionsIso U).hom ≫ A[F].relativeProjCover.f U),
    hpoint, Category.assoc]
  have hsection := E.projSymmetricAlgebraSectionsIso_hom_comp_relativeProjSectionOfQuotient q U hf
  exact (congrArg (t ≫ ·) hsection).trans
    ((Category.assoc t _ _).symm.trans (congrArg (· ≫ E.relativeProjSectionOfQuotient q) hproj))

/-- In the corresponding projective-line chart, the ideal of the quotient section is
the ideal of the normalized point. This identifies the section scheme-theoretically. -/
theorem ker_polynomialPoint_eq_comap_relativeProjSectionOfQuotient
    (b : Module.Basis (ULift.{u} (Fin 2)) R[U] S[F.obj])
    (d : Module.Basis (ULift.{u} (Fin 1)) R[U] S[E.obj.obj])
    (i : Fin 2) (a : R[U])
    (hi : ((Scheme.Modules.sectionsFunctor U.toOpens).map q.hom).hom (b ⟨i⟩) = d ⟨0⟩)
    (hj : ((Scheme.Modules.sectionsFunctor U.toOpens).map q.hom).hom (b ⟨i.rev⟩) =
      a • d ⟨0⟩) :
    (projectiveLine.polynomialPoint R[U] (RingHom.id R[U]) i a).ker =
      (E.relativeProjSectionOfQuotient q).ker.comap
        (((Pi.basisFun R[U] (Fin 2)).reindex
          (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2))).polynomialProjIso.inv ≫
          F.relativeProjPolynomialChart U b) := by
  let e := (standardFrame R[U]).polynomialProjIso.symm
  let p := projectiveLine R[U] ↘ Spec (.of R[U])
  let j := F.relativeProjPolynomialChart U b
  let P := MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) R[U]
  have he : e.hom ≫ toSpecCoeff P = p := by
    have h := (standardFrame R[U]).polynomialProjIso_hom_over
    calc
      _ = e.hom ≫ e.inv ≫ p := congrArg (e.hom ≫ ·) h.symm
      _ = p := e.hom_inv_id_assoc p
  have H : IsPullback (e.hom ≫ j) p A[F].relativeProjToBase U.property.fromSpec := by
    refine (F.isPullback_relativeProjPolynomialChart U b).flip.of_iso' e (Iso.refl _)
      U.property.isoSpec.symm (Iso.refl _) (by simp [j]) ?_ (by simp) ?_
    · exact (Category.assoc ..).symm.trans (congrArg (· ≫ U.property.isoSpec.inv) he)
    · simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id] using U.property.isoSpec_inv_ι
  have hpoint : projectiveLine.polynomialPoint R[U] (RingHom.id R[U]) i a ≫ p = 𝟙 _ := by
    rw [projectiveLine.polynomialPoint_over]
    exact Spec.map_id _
  exact H.ker_eq_comap_of_comp_eq_id (E.relativeProjSectionOfQuotient_toBase q) hpoint
    (E.polynomialPoint_comp_relativeProjPolynomialChart_eq q U b d i a hi hj)

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank
