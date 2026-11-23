/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Dual
public import TauCeti.AlgebraicGeometry.LineBundle.Dual

/-!
# Dual evaluation and sections of tensor products

The tensor adjunction for the exact pairing of a finite locally free sheaf with its dual
identifies maps from the dual to a sheaf with sections of the tensor product. At the
structure sheaf this recovers Tau Ceti's `Scheme.Modules.dualHomUnitEquiv`.
-/

public noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed
open TauCeti

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}
variable (M : X.Modules) [M.IsLocallyFree] [M.IsFiniteType]

/-- A map from the dual of a finite locally free module to `N` corresponds to a global
section of `N ⊗ M`. -/
def dualHomTensorEquiv (N : X.Modules) :
    ((ihom M).obj (𝟙_ X.Modules) ⟶ N) ≃ (𝟙_ X.Modules ⟶ N ⊗ M) :=
  let D := (ihom M).obj (𝟙_ X.Modules)
  let : ExactPairing D M := exactPairingOfIsIsoDualTensorIhom
  ((λ_ D).homCongr (Iso.refl N)).symm.trans (tensorRightHomEquiv (𝟙_ X.Modules) D M N)

/-- The dual correspondence tensors a map with the identity after coevaluation. -/
theorem dualHomTensorEquiv_apply {N : X.Modules} (ψ : (ihom M).obj (𝟙_ X.Modules) ⟶ N) :
    dualHomTensorEquiv M N ψ =
      (MonoidalClosed.id M ≫ inv ((dualTensorIhom M).app M)) ≫ ψ ▷ M := by
  let D := (ihom M).obj (𝟙_ X.Modules)
  let : ExactPairing D M := exactPairingOfIsIsoDualTensorIhom
  rw [← exactPairingOfIsIsoDualTensorIhom_coevaluation]
  simp only [dualHomTensorEquiv, Equiv.trans_apply, Iso.homCongr, Equiv.symm_mk, Equiv.coe_fn_mk,
    Iso.refl_inv, Category.comp_id, tensorRightHomEquiv, comp_whiskerRight]
  monoidal

/-- The dual correspondence is natural in the target of the functional. -/
theorem dualHomTensorEquiv_comp {N P : X.Modules} (ψ : (ihom M).obj (𝟙_ X.Modules) ⟶ N)
    (i : N ⟶ P) :
    dualHomTensorEquiv M P (ψ ≫ i) = dualHomTensorEquiv M N ψ ≫ i ▷ M := by
  simp only [dualHomTensorEquiv_apply, comp_whiskerRight, Category.assoc]

/-- The case of a functional to the structure sheaf recovers dual evaluation. -/
@[reassoc]
theorem dualHomTensorEquiv_comp_leftUnitor (φ : (ihom M).obj (𝟙_ X.Modules) ⟶ 𝟙_ X.Modules) :
    dualHomTensorEquiv M (𝟙_ X.Modules) φ ≫ (λ_ M).hom = dualHomUnitEquiv M φ := by
  rw [dualHomTensorEquiv_apply, dualHomUnitEquiv_apply, Category.assoc]

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (L : InvertibleSheaf X)

/-- Coevaluation of an invertible sheaf and its internal-Hom dual is an isomorphism. -/
theorem isIso_dualCoevaluation :
    IsIso (MonoidalClosed.id L.obj ≫ inv ((dualTensorIhom L.obj).app L.obj)) := by
  let D := (ihom L.obj).obj (𝟙_ X.Modules)
  let : ExactPairing D L.obj := TauCeti.exactPairingOfIsIsoDualTensorIhom
  have h : IsIso (ε_ D L.obj) := by
    rw [TauCeti.exactPairingOfIsIsoDualTensorIhom_evaluation]
    exact SheafOfModules.isIso_evaluation_dual_of_isInvertible (R := X.sheaf) L.obj
  have hcomp : IsIso ((η_ D L.obj ▷ D) ≫ (α_ D L.obj D).hom ≫ D ◁ ε_ D L.obj) := by
    rw [ExactPairing.evaluation_coevaluation]
    infer_instance
  have hw : IsIso (η_ D L.obj ▷ D) :=
    IsIso.of_isIso_comp_right _ ((α_ D L.obj D).hom ≫ D ◁ ε_ D L.obj)
  let E := L.tensorRightDualEquivalence.functor
  have hE (f : 𝟙_ X.Modules ⟶ D ⊗ L.obj) :
      IsIso (E.map f) ↔ IsIso (f ▷ D) := by
    dsimp only [E]
    rw [tensorRightDualEquivalence_functor, dual_obj]
    rfl
  have : IsIso (E.map (η_ D L.obj)) := (hE _).mpr hw
  rw [← TauCeti.exactPairingOfIsIsoDualTensorIhom_coevaluation]
  exact isIso_of_reflects_iso _ E

/-- For an invertible sheaf, a functional is an isomorphism exactly when the corresponding
section trivializes its tensor product with the target. -/
@[simp]
theorem isIso_dualHomTensorEquiv_iff {M : X.Modules}
    (ψ : (ihom L.obj).obj (𝟙_ X.Modules) ⟶ M) :
    IsIso (dualHomTensorEquiv L.obj M ψ) ↔ IsIso ψ := by
  have := isIso_dualCoevaluation L
  rw [dualHomTensorEquiv_apply]
  let E := L.tensorRightDualEquivalence.inverse
  have hE : IsIso (E.map ψ) ↔ IsIso (ψ ▷ L.obj) := by
    dsimp only [E]
    rw [tensorRightDualEquivalence_inverse]
    rfl
  constructor
  · intro h
    have hψ : IsIso (ψ ▷ L.obj) := IsIso.of_isIso_comp_left (MonoidalClosed.id L.obj ≫
      inv ((dualTensorIhom L.obj).app L.obj)) _
    have := hE.mpr hψ
    exact isIso_of_reflects_iso ψ E
  · intro h
    have := hE.mp (inferInstance : IsIso (E.map ψ))
    infer_instance

end TauCeti.AlgebraicGeometry.InvertibleSheaf
