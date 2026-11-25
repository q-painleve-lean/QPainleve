/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Isomorphism
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Picard class of the exceptional divisor

The lift of a center-preserving isomorphism identifies the classes of the exceptional divisors.
-/

public section

noncomputable section

open CategoryTheory TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- The Picard class of the exceptional divisor, inverse to the class of its ideal sheaf. -/
def blowupExceptionalClass (I : X.IdealSheafData) : LineBundleClass I.blowup :=
  (LineBundleClass.mk I.isEffectiveCartier_comap_blowupToBase.toInvertibleSheaf)⁻¹

/-- The exceptional class is the inverse of the class of the exceptional ideal sheaf. -/
theorem blowupExceptionalClass_def (I : X.IdealSheafData) :
    I.blowupExceptionalClass =
      (LineBundleClass.mk I.isEffectiveCartier_comap_blowupToBase.toInvertibleSheaf)⁻¹ := (rfl)

/-- If a Cartier divisor is the sum of the source and pulled-back target exceptional
divisors, the pulled-back target class is the quotient of its class by the source class. -/
theorem pullback_blowupExceptionalClass_eq_div_of_eq_mul (J : Y.IdealSheafData)
    {I : X.IdealSheafData} (f : I.blowup ⟶ J.blowup) {D : I.blowup.IdealSheafData}
    (hD : D.IsEffectiveCartier) (hf : ((J.comap J.blowupToBase).comap f).IsEffectiveCartier)
    (h : D = (I.comap I.blowupToBase) * ((J.comap J.blowupToBase).comap f)) :
    LineBundleClass.pullback f J.blowupExceptionalClass =
      (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ / I.blowupExceptionalClass := by
  let hI := I.isEffectiveCartier_comap_blowupToBase
  have hclass := LineBundleClass.mk_toInvertibleSheaf_congr hD
    (TauCeti.isEffectiveCartier_mul hI hf) h
  rw [LineBundleClass.mk_toInvertibleSheaf_mul hI hf] at hclass
  apply eq_div_iff_mul_eq'.mpr
  rw [blowupExceptionalClass_def, LineBundleClass.pullback_inv,
    J.isEffectiveCartier_comap_blowupToBase.pullback_mk_toInvertibleSheaf hf,
    blowupExceptionalClass_def, hclass, mul_inv_rev]

/-- The exceptional line bundle pulls back to the trivial class along a morphism
that avoids the center after composition with the blowup projection. -/
theorem pullback_blowupExceptionalClass_eq_one (I : X.IdealSheafData) (g : Y ⟶ I.blowup)
    (hg : I.comap (g ≫ I.blowupToBase) = ⊤) :
    LineBundleClass.pullback g I.blowupExceptionalClass = 1 := by
  let hE := I.isEffectiveCartier_comap_blowupToBase
  have heq : (I.comap I.blowupToBase).comap g = ⊤ := by rw [← I.comap_comp, hg]
  rw [blowupExceptionalClass_def, LineBundleClass.pullback_inv,
    hE.pullback_mk_toInvertibleSheaf_eq_one_of_comap_eq_top heq, inv_one]

/-- The exceptional class pulls back along the blowup comparison to the exceptional
class of the base-changed center. -/
@[simp]
theorem pullback_blowupExceptionalClass_blowupMap (I : X.IdealSheafData) (f : Y ⟶ X) :
    LineBundleClass.pullback (I.blowupMap f) I.blowupExceptionalClass =
      (I.comap f).blowupExceptionalClass := by
  have heq := I.comap_comap_blowupMap f
  let h := (I.comap f).isEffectiveCartier_comap_blowupToBase
  simp only [blowupExceptionalClass_def, LineBundleClass.pullback_inv]
  rw [I.isEffectiveCartier_comap_blowupToBase.pullback_mk_toInvertibleSheaf (heq.symm ▸ h)]
  exact congrArg Inv.inv (LineBundleClass.mk_toInvertibleSheaf_congr _ _ heq)

/-- The lift pulls the target exceptional class back to the source exceptional class. -/
@[simp]
theorem pullback_blowupExceptionalClass (J : Y.IdealSheafData) (e : X ≅ Y)
    {I : X.IdealSheafData} (h : J.comap e.hom = I) :
    LineBundleClass.pullback (blowupIso e h.symm).hom J.blowupExceptionalClass =
      I.blowupExceptionalClass := by
  let hJ := J.isEffectiveCartier_comap_blowupToBase
  simp only [blowupExceptionalClass, LineBundleClass.pullback_inv]
  rw [hJ.pullback_mk_toInvertibleSheaf (hJ.comap (blowupIso e h.symm).hom)]
  exact congrArg Inv.inv
    (LineBundleClass.mk_toInvertibleSheaf_congr _ _ (J.comap_blowupIso_hom e h))

end AlgebraicGeometry.Scheme.IdealSheafData
