/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Pullback
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Blowups under isomorphisms

An isomorphism identifying the center ideals lifts uniquely to an isomorphism of the blowups
and identifies their exceptional divisors. The construction uses Tau Ceti's
`Scheme.IdealSheafData.isPullback_blowupMap_of_flat` and the universal property of the blowup.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y Z : Scheme.{u}} {I : X.IdealSheafData} {J : Y.IdealSheafData}
  {K : Z.IdealSheafData}

/-- A scheme isomorphism identifying two center ideals induces an isomorphism of their blowups. -/
def blowupIso (J : Y.IdealSheafData) {I : X.IdealSheafData} (e : X ≅ Y)
    (h : J.comap e.hom = I) :
    I.blowup ≅ J.blowup :=
  letI := (J.isPullback_blowupMap_of_flat e.hom).isIso_snd_of_isIso
  eqToIso (congrArg blowup h.symm) ≪≫ asIso (J.blowupMap e.hom)

/-- For the inverse-image center, the forward morphism of the isomorphism is the native
morphism of blowups. -/
@[simp]
theorem blowupIso_hom_comap (J : Y.IdealSheafData) (e : X ≅ Y) :
    (J.blowupIso e rfl).hom = J.blowupMap e.hom := by
  simp [blowupIso]

/-- The lifted isomorphism commutes with the blowup projections. -/
@[reassoc (attr := simp)]
theorem blowupIso_hom_blowupToBase (e : X ≅ Y) (h : J.comap e.hom = I) :
    (J.blowupIso e h).hom ≫ J.blowupToBase = I.blowupToBase ≫ e.hom := by
  subst I
  simp

/-- The lifted isomorphism is the unique morphism over the specified base isomorphism. -/
theorem eq_blowupIso_hom (e : X ≅ Y) (h : J.comap e.hom = I) {f : I.blowup ⟶ J.blowup}
    (hf : f ≫ J.blowupToBase = I.blowupToBase ≫ e.hom) :
    f = (J.blowupIso e h).hom := by
  subst I
  rw [blowupIso_hom_comap]
  exact J.eq_blowupMap e.hom hf

/-- The lifted identity is the identity. -/
@[simp]
theorem blowupIso_refl (I : X.IdealSheafData) :
    I.blowupIso (Iso.refl X) (comap_id I) = Iso.refl I.blowup := by
  apply Iso.ext
  exact (eq_blowupIso_hom _ _ (by simp)).symm

/-- Lifting isomorphisms commutes with composition. -/
theorem blowupIso_trans (e : X ≅ Y) (f : Y ≅ Z)
    (h : J.comap e.hom = I) (k : K.comap f.hom = J) :
    K.blowupIso (e ≪≫ f) (by simp [h, k]) = J.blowupIso e h ≪≫ K.blowupIso f k := by
  apply Iso.ext
  exact (eq_blowupIso_hom _ _ (by simp)).symm

/-- Lifting the inverse base isomorphism gives the inverse of the lift. -/
theorem blowupIso_symm (e : X ≅ Y) (h : J.comap e.hom = I) :
    I.blowupIso e.symm (by rw [← h, ← comap_comp]; simp) = (J.blowupIso e h).symm := by
  apply Iso.ext
  apply Eq.symm
  apply eq_blowupIso_hom
  rw [Iso.symm_hom, ← cancel_epi (J.blowupIso e h).hom]
  simp

/-- The lift pulls the target exceptional ideal back to the source exceptional ideal. -/
@[simp]
theorem comap_exceptional_blowupIso_hom (e : X ≅ Y) (h : J.comap e.hom = I) :
    (J.comap J.blowupToBase).comap (J.blowupIso e h).hom = I.comap I.blowupToBase := by
  subst I
  rw [blowupIso_hom_comap]
  exact J.comap_comap_blowupMap e.hom

/-- The Picard class of the exceptional divisor of a blowup. -/
def blowupExceptionalClass (I : X.IdealSheafData) : LineBundleClass I.blowup :=
  (LineBundleClass.mk I.isEffectiveCartier_comap_blowupToBase.toInvertibleSheaf)⁻¹

/-- The exceptional class is the inverse of the class of the exceptional ideal sheaf. -/
theorem blowupExceptionalClass_def (I : X.IdealSheafData) :
    I.blowupExceptionalClass =
      (LineBundleClass.mk I.isEffectiveCartier_comap_blowupToBase.toInvertibleSheaf)⁻¹ :=
  (rfl)

/-- The lift pulls the target exceptional class back to the source exceptional class. -/
@[simp]
theorem pullback_blowupExceptionalClass (e : X ≅ Y) (h : J.comap e.hom = I) :
    LineBundleClass.pullback (J.blowupIso e h).hom J.blowupExceptionalClass =
      I.blowupExceptionalClass := by
  rw [J.blowupExceptionalClass_def, I.blowupExceptionalClass_def, LineBundleClass.pullback_inv,
    J.isEffectiveCartier_comap_blowupToBase.pullback_mk_toInvertibleSheaf
    (J.isEffectiveCartier_comap_blowupToBase.comap _)]
  exact congrArg Inv.inv
    (LineBundleClass.mk_toInvertibleSheaf_congr _ _ (comap_exceptional_blowupIso_hom e h))

end AlgebraicGeometry.Scheme.IdealSheafData
