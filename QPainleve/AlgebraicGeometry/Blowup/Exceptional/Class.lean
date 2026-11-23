/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Isomorphism
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

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

/-- The exceptional line bundle pulls back to the trivial class along a morphism
that avoids the center after composition with the blowup projection. -/
theorem pullback_blowupExceptionalClass_eq_one (I : X.IdealSheafData) (g : Y ⟶ I.blowup)
    (hg : I.comap (g ≫ I.blowupToBase) = ⊤) :
    LineBundleClass.pullback g I.blowupExceptionalClass = 1 := by
  let hE := I.isEffectiveCartier_comap_blowupToBase
  have heq : (I.comap I.blowupToBase).comap g = ⊤ := by rw [← I.comap_comp, hg]
  rw [blowupExceptionalClass_def, LineBundleClass.pullback_inv,
    hE.pullback_mk_toInvertibleSheaf (heq.symm ▸ isEffectiveCartier_top Y),
    LineBundleClass.mk_toInvertibleSheaf_congr _ (isEffectiveCartier_top Y) heq,
    LineBundleClass.mk_toInvertibleSheaf_top, inv_one]

/-- The lift pulls the target exceptional class back to the source exceptional class. -/
@[simp]
theorem pullback_blowupExceptionalClass (J : Y.IdealSheafData) (e : X ≅ Y)
    {I : X.IdealSheafData} (h : J.comap e.hom = I) :
    LineBundleClass.pullback (J.blowupIso e h).hom J.blowupExceptionalClass =
      I.blowupExceptionalClass := by
  let hJ := J.isEffectiveCartier_comap_blowupToBase
  simp only [blowupExceptionalClass, LineBundleClass.pullback_inv]
  rw [hJ.pullback_mk_toInvertibleSheaf (hJ.comap (J.blowupIso e h).hom)]
  exact congrArg Inv.inv
    (LineBundleClass.mk_toInvertibleSheaf_congr _ _ (J.comap_blowupIso_hom e h))

end AlgebraicGeometry.Scheme.IdealSheafData
