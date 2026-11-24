/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Agreement

/-!
# Marked actions from evaluations on a resolution

A specified pair isomorphism can be compared with a realization of a cluster
word at a common center by testing its X-evaluation square on a dominating
surface. The generic domain condition descends along the projection. For targets
from one toric presentation, `ContractedToricFiber.marked_actions_of_comp_evaluation_eq`
then identifies the full Picard pullback and the action on the ordered branches.
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup.FiberRealization

open MarkedSurface (surfaceIso boundaryIso)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" r "]" => Spec (CommRingCat.of (LaurentRing ℂ (Fin r)))
local notation "D[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n] {L₀ L₁ : Type}
  [AddCommGroup L₀] [AddCommGroup L₁]
  {B₀ : LinearMap.BilinForm ℤ L₀} {B₁ : LinearMap.BilinForm ℤ L₁}
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}
  [PrestableFamily (D[Φ,h₀] ↘ S)] {γ : Type} {a : γ → (D[Φ,h₀] ↘ S).smoothLocus}
  {T : Scheme.NodalCycleNumbering a m} {origin : ZMod m}
  {ι : L₁ →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin r → ℤ)}
  {c d : Multiplicative (Fin r → ℤ) →* ℂˣ}
  {Y W : Scheme} [IsIntegral Y] [Y.IsSeparated] [IsIntegral W]
  {M : MarkedSurface ℂ n B₀ Y} {P Q : MarkedSurface ℂ n B₁ X[r]}
  {F : Y ⤏ X[r]} {I : B₁.IsometryEquiv B₀} {g : DihedralGroup n}

/-- Suppose a specified pair isomorphism and a fixed-center realization carry
the same source X evaluation to their respective target evaluations, as tested
on a dominating surface. When both targets are contracted fibers of one toric
presentation of finite charge index, their marked Picard pullbacks and their
actions on all ordered branches agree. -/
theorem marked_actions_eq_of_compOfDefined_on_resolution
    (R : FiberRealization M P F I g)
    (p : ContractedToricFiber b s hΦ T origin ι c P)
    (q : ContractedToricFiber b s hΦ T origin ι d Q)
    (e : M.pair ≅ Q.pair) (π : W ⤏ M.surface) [π.IsDominant]
    (hc : Φ.IsComplete) (hι : Function.Injective ι)
    (hindex : (Fan.rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    (he : ∃ h, (π.comp M.evaluation).compOfDefined F h =
      π.comp ((surfaceIso e).hom.toRationalMap.comp Q.evaluation)) :
    (∀ a, M.picardMarking (I a) =
      Additive.ofMul (LineBundleClass.pullback (surfaceIso e).hom (Q.picardMarking a).toMul)) ∧
    (let : PrestableFamily (M.boundary ↘ S) := M.prestable
     let : PrestableFamily (Q.boundary ↘ S) := Q.prestable
     (boundaryIso e).boundaryCycleAction M.cycle Q.cycle = g) := by
  have he' := (π.compOfDefined_eq_iff_of_dominant M.evaluation F _).mp he
  let t := R.iso.symm ≪≫ e
  obtain ⟨hpic, hbranch⟩ := p.marked_actions_of_comp_evaluation_eq q t hc hι hindex
    (R.comp_targetEvaluation_of_evaluation_eq e he')
  have ht : R.iso ≪≫ t = e := by simp [t]
  refine ⟨fun a ↦ ?_, ?_⟩
  · rw [R.picard_eq, ← hpic a, LineBundleClass.pullback_comp, ← Iso.trans_hom,
      ← MarkedSurface.surfaceIso_trans, ht]
  · let : PrestableFamily (M.boundary ↘ S) := M.prestable
    let : PrestableFamily (P.boundary ↘ S) := P.prestable
    let : PrestableFamily (Q.boundary ↘ S) := Q.prestable
    simpa only [← MarkedSurface.boundaryIso_trans, ht, hbranch, R.boundaryAction_eq, one_mul]
      using (boundaryIso R.iso).boundaryCycleAction_trans M.cycle P.cycle (boundaryIso t) Q.cycle

end QPainleve.SignedClusterModularGroup.FiberRealization
