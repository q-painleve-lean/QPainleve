/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.LineBundle.Dual
public import TauCeti.AlgebraicGeometry.LineBundle.Power

/-!
# Twisting a line bundle by a Cartier divisor

Canceling the invertible Cartier ideal against its dual identifies
maps `M(-D) ⟶ W` with maps `M ⟶ W(D)`. The cancellation uses the evaluation
of the ideal sheaf against its dual.
-/

public noncomputable section

open CategoryTheory MonoidalCategory
open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- Cancel the Cartier ideal against its dual in the twist `W(D)(-D)`. -/
def IsEffectiveCartier.tensorDualCancelIso (hI : I.IsEffectiveCartier) (W : InvertibleSheaf X) :
    (W.tensorProduct hI.toInvertibleSheaf.dual).obj ⊗ I.sheaf ≅ W.obj :=
  let L := hI.toInvertibleSheaf
  let e := (tensorLeft L.dual.obj).mapIso (eqToIso hI.toInvertibleSheaf_obj.symm) ≪≫
    β_ L.dual.obj L.obj ≪≫ L.evaluationDualIso
  (tensorRight I.sheaf).mapIso (InvertibleSheaf.tensorProductObjIso W L.dual) ≪≫
    α_ W.obj L.dual.obj I.sheaf ≪≫ (tensorLeft W.obj).mapIso e ≪≫ ρ_ W.obj

/-- Tensoring `𝒪_X(D)^{⊗(n + 1)}` with the Cartier ideal `𝒪_X(-D)` cancels one copy of
`𝒪_X(D)`. -/
def IsEffectiveCartier.tensorPowSuccIdealIso (hI : I.IsEffectiveCartier) (n : ℕ) :
    (hI.toInvertibleSheaf.dual.tensorPow (n + 1)).obj ⊗ I.sheaf ≅
      (hI.toInvertibleSheaf.dual.tensorPow n).obj :=
  (tensorRight I.sheaf).mapIso (eqToIso
    (congrArg (fun L : InvertibleSheaf X ↦ L.obj) (hI.toInvertibleSheaf.dual.tensorPow_succ n))) ≪≫
    hI.tensorDualCancelIso _

private def IsEffectiveCartier.tensorRightFullyFaithful (hI : I.IsEffectiveCartier) :
    (tensorRight I.sheaf).FullyFaithful := by
  rw [← hI.toInvertibleSheaf_obj, ← InvertibleSheaf.tensorRightDualEquivalence_inverse]
  exact hI.toInvertibleSheaf.tensorRightDualEquivalence.fullyFaithfulInverse

/-- A map `M(-D) ⟶ W`, or equivalently a section of its `W`-valued dual, twisted
by the inverse Cartier ideal to give a map `M ⟶ W(D)`. -/
def IsEffectiveCartier.dualSectionTwist (hI : I.IsEffectiveCartier)
    (M : X.Modules) (W : InvertibleSheaf X) :
    (M ⊗ I.sheaf ⟶ W.obj) ≃
      (M ⟶ (W.tensorProduct hI.toInvertibleSheaf.dual).obj) :=
  ((Iso.refl _).homCongr (hI.tensorDualCancelIso W).symm).trans
    hI.tensorRightFullyFaithful.homEquiv.symm

/-- Twisting the dual section and then evaluating against the Cartier ideal recovers its
original map. -/
@[reassoc (attr := simp)]
theorem IsEffectiveCartier.dualSectionTwist_whiskerRight (hI : I.IsEffectiveCartier)
    (M : X.Modules) (W : InvertibleSheaf X) (a : M ⊗ I.sheaf ⟶ W.obj) :
    hI.dualSectionTwist M W a ▷ I.sheaf ≫ (hI.tensorDualCancelIso W).hom = a := by
  apply (Iso.eq_comp_inv _).mp
  exact hI.tensorRightFullyFaithful.map_preimage
    (a ≫ (hI.tensorDualCancelIso W).inv)

end AlgebraicGeometry.Scheme.IdealSheafData
