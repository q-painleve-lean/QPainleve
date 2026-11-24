/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision
public import QPainleve.Geometry.Toric.Fan.InternalBlowup

import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Pullback

/-!
# Internal toric blowups under fan subdivision

A subdivision retains all old ray charts, so the corresponding binomial centers and
their order can be transported to the refined fan. The resulting internal blowup model
is the scheme-theoretic pullback of the original model, with a compatible map of the
strict boundaries. This compares the internal models on two fans with a common refinement.

The ordered centers and strict boundary are as in Gross, Hacking and Keel,
[*Moduli of surfaces with an anti-canonical cycle*, Definition 1.2][GHK].

[GHK]: https://arxiv.org/abs/1211.6367
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan.IsSubdivision

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ)
  [hΦ : Nonempty Φ.cones] [hΨ : Nonempty Ψ.cones] (b : Module.Basis (Fin 2) ℤ N)

local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "χ(" ρ ")" => LinearMap.toAddMonoidHom (b.detDualEquiv (Ray.primitiveGenerator ρ))

/-- Subdivision pulls back the ordered internal model with the same center parameters.
The lift intertwines the strict-transform boundary embeddings and pulls back each
total exceptional class to the corresponding class on the refined model. -/
theorem exists_isPullback_internalBlowupTower {n : ℕ} (ρ : Fin n → Ψ.Ray) (c : Fin n → ℂˣ) :
    let A := internalBlowupTower b ρ c
    let A' := internalBlowupTower b (h.liftRay ∘ ρ) c
    ∃ g : A'.1 ⟶ A.1, IsPullback g A'.2.toTower.toBase A.2.toTower.toBase h.toFanHom.algebraicMap ∧
      A'.2.boundaryι ≫ g = h.boundaryMap hΦ hΨ ≫ A.2.boundaryι ∧
      ∀ j, LineBundleClass.pullback g (A.2.toTower.exceptionalClass j) =
        A'.2.toTower.exceptionalClass j := by
  let s (j : Fin n) : Spec (.of ℂ) ⟶ (Ψ.boundaryIdeal hΨ).subscheme :=
    (ρ j).binomialCenterOnBoundary rankTwo (m := χ(ρ j)) (b.detDualEquiv_self _)
      ((ρ j).surjective_detCharacter b) (c j)
  let s' (j : Fin n) : Spec (.of ℂ) ⟶ (Φ.boundaryIdeal hΦ).subscheme :=
    (h.liftRay (ρ j)).binomialCenterOnBoundary rankTwo (m := χ(h.liftRay (ρ j)))
      (b.detDualEquiv_self _) ((h.liftRay (ρ j)).surjective_detCharacter b) (c j)
  have hs (j : Fin n) : s' j ≫ h.boundaryMap hΦ hΨ = s j := by
    dsimp only [s', s]
    simpa only [primitiveGenerator_liftRay] using
      h.binomialCenterOnBoundary_comp_boundaryMap (ρ j) rankTwo (m := χ(ρ j))
        (b.detDualEquiv_self _) ((ρ j).surjective_detCharacter b) (c j)
  have hC (j : Fin n) : (s j).ker.IsEffectiveCartier := by
    simpa only [s, ← Ray.internalCenter_val] using ((ρ j).internalCenter b (c j)).property
  have hC' (j : Fin n) : (s' j).ker.IsEffectiveCartier := by
    simpa only [s', ← Ray.internalCenter_val] using
      ((h.liftRay (ρ j)).internalCenter b (c j)).property
  have hi (j : Fin n) :
      Set.range (s j ≫ (Ψ.boundaryIdeal hΨ).subschemeι) ⊆ h.toFanHom.algebraicMap.isoLocus := by
    have hcomp : s j ≫ (Ψ.boundaryIdeal hΨ).subschemeι =
        (ρ j).binomialCenter rankTwo (m := χ(ρ j)) (b.detDualEquiv_self _)
          ((ρ j).surjective_detCharacter b) (c j) :=
      (ρ j).binomialCenterOnBoundary_comp_subschemeι rankTwo (b.detDualEquiv_self _)
        ((ρ j).surjective_detCharacter b) (c j)
    rw [hcomp]
    exact h.range_binomialCenter_subset_isoLocus (ρ j) rankTwo (b.detDualEquiv_self _)
      ((ρ j).surjective_detCharacter b) (c j)
  have (j : Fin n) : IsClosedImmersion (s j) := by
    exact (ρ j).isClosedImmersion_binomialCenterOnBoundary rankTwo (b.detDualEquiv_self _)
      ((ρ j).surjective_detCharacter b) (c j)
  have hA : (fun j ↦ ⟨(s j).ker, hC j⟩) = fun j ↦ (ρ j).internalCenter b (c j) := by
    funext j
    exact Subtype.ext (Ray.internalCenter_val _ _ _).symm
  have hA' : (fun j ↦ ⟨(s' j).ker, hC' j⟩) = fun j ↦ (h.liftRay (ρ j)).internalCenter b (c j) := by
    funext j
    exact Subtype.ext (Ray.internalCenter_val _ _ _).symm
  have hp := exists_isPullback_alongBoundary (h.boundaryMap_comp_subschemeι hΦ hΨ).symm
    s s' hs hC hC' hi
  dsimp only at hp ⊢
  rw [hA, hA'] at hp
  rw [internalBlowupTower_eq_alongBoundary, internalBlowupTower_eq_alongBoundary]
  exact hp

/-- A specified common subdivision with matching labeled primitive generators gives one
ordered internal model projecting cartesianly to both endpoint models. Both projections
respect the strict boundary. -/
theorem exists_common_internalBlowupTower {Ω : Fan i} [hΩ : Nonempty Ω.cones]
    (h' : Φ.IsSubdivision Ω) {n : ℕ} (ρ : Fin n → Ψ.Ray) (τ : Fin n → Ω.Ray) (c : Fin n → ℂˣ)
    (hρτ : ∀ j, (ρ j).primitiveGenerator = (τ j).primitiveGenerator) :
    let A := internalBlowupTower b (h.liftRay ∘ ρ) c
    let B := internalBlowupTower b ρ c
    let C := internalBlowupTower b τ c
    ∃ (g : A.1 ⟶ B.1) (g' : A.1 ⟶ C.1),
      IsPullback g A.2.toTower.toBase B.2.toTower.toBase h.toFanHom.algebraicMap ∧
      IsPullback g' A.2.toTower.toBase C.2.toTower.toBase h'.toFanHom.algebraicMap ∧
      A.2.boundaryι ≫ g = h.boundaryMap hΦ hΨ ≫ B.2.boundaryι ∧
      A.2.boundaryι ≫ g' = h'.boundaryMap hΦ hΩ ≫ C.2.boundaryι := by
  have hmatch := h.liftRay_comp_eq_of_primitiveGenerator_eq h' ρ τ hρτ
  obtain ⟨g, hg, hb, -⟩ := h.exists_isPullback_internalBlowupTower b ρ c
  have hsecond := h'.exists_isPullback_internalBlowupTower b τ c
  dsimp only at hsecond
  rw [← hmatch] at hsecond
  obtain ⟨g', hg', hb', -⟩ := hsecond
  exact ⟨g, g', hg, hg', hb, hb'⟩

end TauCeti.Toric.Fan.IsSubdivision
