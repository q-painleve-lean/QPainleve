/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.StarFactorization

import QPainleve.AlgebraicGeometry.Modules.Differentials.PoleIdeal
import QPainleve.Geometry.Toric.Fan.Boundary.Equiv
import QPainleve.Geometry.Toric.Fan.Equiv
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# Changing the target lattice of a logarithmic projection

A fan equivalence transports a logarithmic projection to a new toric frame.
It preserves the pole ideal and the modification property. Two specified toric
contractions can therefore be compared on one lattice.

The toric change of target is used in the proof of [Lutz's Theorem 8.4][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection

universe u

variable {K : Type u} [Field K] {N V N' V' : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}

local notation "S" => Spec (CommRingCat.of K)
local notation "X[" Φ "]" => Fan.finiteFanScheme K Φ

section Reframe

variable {Z : Scheme} [Z.Over (Spec (.of K))] [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of K))]
  {D : Z.IdealSheafData} (A : LogarithmicProjection K i D) {Ψ : Fan i'}
  (e : FanEquiv A.fan Ψ) (hN : Module.finrank ℤ N = 2)

/-- Postcompose a specified logarithmic projection with the toric isomorphism of
a fan equivalence. The resulting projection has the same pole boundary. -/
def reframe : LogarithmicProjection K i' D := by
  have hreg := e.isRegular_iff.mpr A.isRegular
  have hc := e.isComplete_iff.mpr A.isComplete
  let : Nonempty Ψ.cones := hc.nonempty_cones
  let : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have hN' : Module.finrank ℤ N' = 2 := e.latticeEquiv.toIntLinearEquiv.finrank_eq.symm.trans hN
  let : SmoothOfRelativeDimension 2 (X[A.fan] ↘ S) := by
    rw [A.fan.finiteFanScheme_over K, ← hN]
    exact A.fan.smoothOfRelativeDimension_finiteFanSchemeToSpec K A.isRegular
  let : SmoothOfRelativeDimension 2 (X[Ψ] ↘ S) := by
    rw [Ψ.finiteFanScheme_over K, ← hN']
    exact Ψ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hreg
  let : Smooth (X[A.fan] ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : Smooth (X[Ψ] ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let k := e.toFanHom.finiteFanSchemeHom K
  have hp : (Ψ.toricBoundaryIdeal K hc.nonempty_cones).comap k =
      (A.fan.toricBoundaryIdeal K A.isComplete.nonempty_cones) * ramificationIdealSheaf K k := by
    rw [ramificationIdealSheaf_eq_top_of_isOpenImmersion, mul_top]
    exact e.comap_toricBoundaryIdeal_finiteFanSchemeHom K _ _
  exact ⟨Ψ, hreg, hc, A.hom ≫ k, inferInstance, inferInstance,
    comap_eq_mul_ramificationIdealSheaf_comp K A.hom k 2 hp A.comap_boundaryIdeal⟩

/-- The target fan of the reframed projection is the target of the fan equivalence. -/
@[simp]
theorem reframe_fan : (A.reframe e hN).fan = Ψ := (rfl)

/-- The map of a reframed logarithmic projection is the specified composite. -/
theorem reframe_hom : (A.reframe e hN).hom ≍ A.hom ≫ e.toFanHom.finiteFanSchemeHom K := (HEq.rfl)

/-- Composing the reframed projection with the inverse frame change recovers the
original morphism on the whole resolving surface. -/
theorem reframe_hom_comp_symm :
    let e' : FanEquiv (A.reframe e hN).fan A.fan := (A.reframe_fan e hN).symm ▸ e.symm
    (A.reframe e hN).hom ≫ e'.toFanHom.finiteFanSchemeHom K = A.hom := by
  -- Unfold the transported projection and the cast of the inverse fan equivalence.
  change (A.hom ≫ e.toFanHom.finiteFanSchemeHom K) ≫ e.symm.toFanHom.finiteFanSchemeHom K = A.hom
  simp only [Category.assoc, e.finiteFanSchemeHom_comp_symm K, Category.comp_id]

/-- Postcomposing a logarithmic projection with a toric isomorphism preserves
and reflects the modification property. -/
@[simp]
theorem isModification_reframe_iff :
    IsModification (A.reframe e hN).hom ↔ IsModification A.hom := by
  constructor
  · intro h
    let : IsModification (A.reframe e hN).hom := h
    rw [← A.reframe_hom_comp_symm e hN]
    infer_instance
  · intro h
    let : IsModification A.hom := h
    rw [eq_of_heq (A.reframe_hom e hN)]
    let : IsModification (e.toFanHom.finiteFanSchemeHom K) := IsModification.of_isIso _
    exact IsModification.comp A.hom (e.toFanHom.finiteFanSchemeHom K)

end Reframe

section FixedLattice

variable {Z : Scheme} [Z.Over (Spec (.of K))] [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of K))]
  {D : Z.IdealSheafData}

/-- A specified logarithmic contraction can be transported into any prescribed
rank-two lattice frame. The inverse frame change induces the basis identification
and recovers the original contraction as an equality of morphisms. -/
theorem exists_reframed_target (B : LogarithmicProjection K i' D) [IsModification B.hom]
    (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
    (hi : IsIntegralLattice i) :
    ∃ (C : LogarithmicProjection K i D) (e : FanEquiv C.fan B.fan),
      e.latticeEquiv = (b.equiv b' (Equiv.refl _)).toAddEquiv ∧
      C.hom ≫ e.toFanHom.finiteFanSchemeHom K = B.hom ∧ IsModification C.hom := by
  let e := B.fan.mapEquivIso hi (b.equiv b' (Equiv.refl _)).symm.toAddEquiv
  have hN' := (Module.finrank_eq_card_basis b').trans (Fintype.card_fin 2)
  let e' : FanEquiv (B.reframe e hN').fan B.fan := (B.reframe_fan e hN').symm ▸ e.symm
  refine ⟨B.reframe e hN', e', ?_, B.reframe_hom_comp_symm e hN',
    (B.isModification_reframe_iff e hN').mpr inferInstance⟩
  -- The fan equality used in the cast is reflexive for the image fan.
  change e.symm.latticeEquiv = _
  simp [e]

end FixedLattice

end TauCeti.Toric.Fan.LogarithmicProjection
