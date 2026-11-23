/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import TauCeti.AlgebraicGeometry.Blowup.BaseChange
public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
public import TauCeti.AlgebraicGeometry.IdealSheaf.Conductor.Basic

import QPainleve.AlgebraicGeometry.IdealSheaf.Conductor
import TauCeti.AlgebraicGeometry.IdealSheaf.Conductor.BaseChange

/-!
# Conductors of finite affine blowups

When a two-generated ideal has a principal reduction of reduction number at
most one, the corresponding affine chart covers the blowup. The conductor of a
finite blowup in this situation is computed by the conductor of the chart algebra.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry reesAlgebra

universe u

namespace Ideal

/-- If `I = (a, b)` and `b² ∈ aI`, the conductor of the finite blowup of `Spec R`
along `I` is the ideal sheaf of the conductor of `R[I/a]`. -/
theorem conductor_toSpecCoeff_eq_of_span_pair {R : Type u} [CommRing R]
    {I : Ideal R} {a b : R} [IsFinite (Proj.toSpecCoeff (grade I))]
    (hI : Ideal.span {a, b} = I) (hb : b ^ 2 ∈ Ideal.span {a} * I) :
    (Proj.toSpecCoeff (grade I)).conductor = Scheme.IdealSheafData.ofIdealTop
      ((TauCeti.Algebra.conductor R (I.affineBlowup a (Localization.Away a))).map
        (Scheme.ΓSpecIso (.of R)).inv.hom) := by
  let B := I.affineBlowup a (Localization.Away a)
  have ha : a ∈ I := hI ▸ Ideal.subset_span (Set.mem_insert a _)
  let c := affineBlowupι (Localization.Away a) ha
  have : IsIso c := isIso_affineBlowupι_of_sq_mem _ ha hI hb
  have hchart : c ≫ Proj.toSpecCoeff (grade I) = Spec.algebraMap R B := by
    dsimp only [c, Spec.algebraMap]
    rw [toSpecCoeff_reesAlgebra, affineBlowupι_toSpecZero]
  have hpb : IsPullback c (Spec.algebraMap R B) (Proj.toSpecCoeff (grade I)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨hchart.trans (Category.comp_id _).symm⟩
  have : IsFinite (Spec.algebraMap R B) := MorphismProperty.of_isPullback hpb inferInstance
  have h := Scheme.Hom.conductor_eq_comap_of_isPullback hpb
  rw [Scheme.IdealSheafData.comap_id] at h
  rw [← h]
  unfold Spec.algebraMap
  rw [Scheme.Hom.conductor_Spec_map, CommRingCat.hom_ofHom, toAlgebra_algebraMap]

end Ideal

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Over a flat algebra on an affine open, the conductor of a finite blowup is computed
in the single chart of the extended ideal when its two generators satisfy `b² ∈ aI`. -/
theorem conductor_comap_Spec_algebraMap_fromSpec_eq_of_span_pair
    {X : Scheme.{u}} (J : X.IdealSheafData) [IsFinite J.blowupToBase] (U : X.affineOpens)
    {A : Type u} [CommRing A] [Algebra Γ(X, U) A] [Module.Flat Γ(X, U) A] {a b : A}
    (hI : Ideal.span {a, b} = (J.ideal U).map (algebraMap Γ(X, U) A))
    (hb : b ^ 2 ∈ Ideal.span {a} * (J.ideal U).map (algebraMap Γ(X, U) A)) :
    J.blowupToBase.conductor.comap (Spec.algebraMap Γ(X, U) A ≫ U.property.fromSpec) =
      ofIdealTop ((TauCeti.Algebra.conductor A
        (((J.ideal U).map (algebraMap Γ(X, U) A)).affineBlowup a (Localization.Away a))).map
          (Scheme.ΓSpecIso (.of A)).inv.hom) := by
  have : IsOpenImmersion U.property.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.property
  have : Flat (Spec.algebraMap Γ(X, U) A) := by
    unfold Spec.algebraMap
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : Flat (Spec.algebraMap Γ(X, U) A ≫ U.property.fromSpec) := Flat.comp _ _
  have hpb := (isPullback_affineBlowup_of_flat (J.ideal U) A).paste_horiz
    (J.isPullback_blowupChart_fromSpec U.property).flip
  have : IsFinite (Proj.toSpecCoeff (grade ((J.ideal U).map (algebraMap Γ(X, U) A)))) :=
    MorphismProperty.of_isPullback hpb inferInstance
  exact (Hom.conductor_eq_comap_of_isPullback hpb).symm.trans
    (Ideal.conductor_toSpecCoeff_eq_of_span_pair hI hb)

end AlgebraicGeometry.Scheme.IdealSheafData
