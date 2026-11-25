/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IdealSheaf.Tensor.Inclusion
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

/-- Tensoring `L((n + 1)D)` with the Cartier ideal gives `L(nD)`. -/
def IsEffectiveCartier.tensorProductTensorPowSuccIdealIso (hI : I.IsEffectiveCartier)
    (L : InvertibleSheaf X) (n : ℕ) :
    (L.tensorProduct (hI.toInvertibleSheaf.dual.tensorPow (n + 1))).obj ⊗ I.sheaf ≅
      (L.tensorProduct (hI.toInvertibleSheaf.dual.tensorPow n)).obj :=
  (tensorRight I.sheaf).mapIso (L.tensorProductObjIso _) ≪≫
    α_ L.obj (hI.toInvertibleSheaf.dual.tensorPow (n + 1)).obj I.sheaf ≪≫
    (tensorLeft L.obj).mapIso (hI.tensorPowSuccIdealIso n) ≪≫
    (L.tensorProductObjIso _).symm

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

variable (hI : I.IsEffectiveCartier)

/-- Twisting a section precomposed with the Cartier inclusion gives the original
section followed by the inclusion into the positively twisted target line bundle. -/
theorem IsEffectiveCartier.dualSectionTwist_comp_inclusion
    {M : X.Modules} (W : InvertibleSheaf X) (b : M ⟶ W.obj) :
    hI.dualSectionTwist M W (I.tensorIdealInclusion M ≫ b) =
      b ≫ (hI.tensorDualCancelIso W).inv ≫
        I.tensorIdealInclusion (W.tensorProduct hI.toInvertibleSheaf.dual).obj := by
  let N := W.tensorProduct hI.toInvertibleSheaf.dual
  let e := hI.tensorDualCancelIso W
  let t := hI.dualSectionTwist M W
  let c := b ≫ e.inv
  have : Mono (I.tensorIdealInclusion N.obj) := mono_tensorIdealInclusion I N.obj
  have hshift : I.tensorIdealInclusion N.obj ▷ I.sheaf =
      I.tensorIdealInclusion (N.obj ⊗ I.sheaf) :=
    (cancel_mono (I.tensorIdealInclusion N.obj)).mp
      (I.tensorIdealInclusion_naturality (I.tensorIdealInclusion N.obj)).symm
  have hcomp : (c ≫ I.tensorIdealInclusion N.obj) ▷ I.sheaf ≫ e.hom =
      I.tensorIdealInclusion M ≫ b := by
    rw [comp_whiskerRight, hshift, Category.assoc, ← tensorIdealInclusion_naturality_assoc]
    simp [c]
  have he (a : M ⟶ N.obj) : t.symm a = a ▷ I.sheaf ≫ e.hom := by
    rw [← IsEffectiveCartier.dualSectionTwist_whiskerRight hI M W (t.symm a),
      Equiv.apply_symm_apply]
  exact t.symm.injective ((t.symm_apply_apply _).trans ((he _).trans hcomp).symm)

/-- Twisted dual sections vanishing on the divisor are exactly those obtained by
precomposing an ambient dual section with the Cartier inclusion. -/
theorem IsEffectiveCartier.pullback_dualSectionTwist_eq_zero_iff
    (M : X.Modules) (W : InvertibleSheaf X) (a : M ⊗ I.sheaf ⟶ W.obj) :
    (Scheme.Modules.pullback I.subschemeι).map (hI.dualSectionTwist M W a) = 0 ↔
      ∃ b : M ⟶ W.obj, a = I.tensorIdealInclusion M ≫ b := by
  let N := W.tensorProduct hI.toInvertibleSheaf.dual
  let e := hI.tensorDualCancelIso W
  rw [I.pullback_map_eq_zero_iff_exists_comp_tensorIdealInclusion N]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c ≫ e.hom, (hI.dualSectionTwist M W).injective ?_⟩
    refine hc.trans ?_
    simp only [hI.dualSectionTwist_comp_inclusion, Category.assoc, e, Iso.hom_inv_id_assoc]
    rfl
  · rintro ⟨b, rfl⟩
    exact ⟨b ≫ e.inv, by rw [hI.dualSectionTwist_comp_inclusion, Category.assoc]⟩

include hI in
/-- Precomposition with the Cartier inclusion is injective on morphisms into a line bundle. -/
theorem IsEffectiveCartier.injective_precomp_inclusion
    (M : X.Modules) (W : InvertibleSheaf X) :
    Function.Injective (fun b : M ⟶ W.obj ↦ I.tensorIdealInclusion M ≫ b) := by
  let N := W.tensorProduct hI.toInvertibleSheaf.dual
  let e := hI.tensorDualCancelIso W
  have : Mono (I.tensorIdealInclusion N.obj) := mono_tensorIdealInclusion I N.obj
  intro b c h
  have ht := congrArg (hI.dualSectionTwist M W) h
  simp only [hI.dualSectionTwist_comp_inclusion, ← Category.assoc] at ht
  exact (cancel_mono e.inv).mp ((cancel_mono (I.tensorIdealInclusion N.obj)).mp ht)

end AlgebraicGeometry.Scheme.IdealSheafData
