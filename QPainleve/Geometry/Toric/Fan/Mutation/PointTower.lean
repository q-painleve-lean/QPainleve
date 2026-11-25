/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import QPainleve.Geometry.Toric.Fan.Mutation.Blowup

import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# Projected point centers under mutation

A labeled point center off the pivot fiber projects on the target to its
image under the mutation isomorphism of the two fiber complements. This
comparison detects first occurrences in a transported tower, even if other
centers are infinitely near or lie on the pivot fiber.
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone
open QPainleve QPainleve.BlowupTower

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (ρ : Φ.Ray) (b : Basis (Fin 2) ℤ N)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : ℂˣ) {n : ℕ}

local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "X" => Φ.algebraicRealization
local notation "X'" => Fan.algebraicRealization Ψ
local notation "I₀" => ρ.mutationSourceCenterIdeal b c
local notation "I₁" => ρ.mutationTargetCenterIdeal b hOpp c
local notation "E" => ρ.mutationBlowupIso b hOpp c
local notation "k" => Fin.castAdd n (0 : Fin 1)
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "reverseRay" => Φ.mutationFanCenterRays b (fun _ : Unit ↦ ρ) () hOpp ()
local notation "reverseCenter" =>
  Ray.binomialCenter (reverseRay) rankTwo
    (b.detDualEquiv_self (Ray.primitiveGenerator (reverseRay)))
    (Ray.surjective_detCharacter (reverseRay) b) c⁻¹

local notation "sourceOpen" => Φ.mutationComplement b
  (Φ.detCharacter_nonneg_or_nonpos b hv hp hOpp) (c : ℂ)
local notation "targetOpen" => Fan.mutationComplement Ψ b
  (Φ.mutationDetCharacter_nonneg_or_nonpos b hv hp hOpp) (c : ℂ)
local notation "complementIso" => Φ.mutationComplementIso b (c : ℂ) hv hp hOpp

/-- In the tower transported across a mutation, a retained center off the pivot fiber
projects to its image under the isomorphism of fiber complements. If this center
was the first over its point in the original tower, it remains the first over
its image in the new tower. -/
theorem Ray.baseCenter_of_mutation_of_mem_complement {W Z : Scheme}
    {T : BlowupTower X (n + 1) W} {U : BlowupTower X' (1 + n) Z}
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower X' U)
    (j : Fin (n + 1)) (l : Fin n)
    (hreverse : hU.baseCenter k = reverseCenter (IsLocalRing.closedPoint ℂ))
    (hcenters : ∀ a : Fin n, ∃ p : (I₀).blowup,
      (I₀).blowupToBase p = hT.baseCenter (j.succAbove a) ∧
      (I₁).blowupToBase ((E).hom p) = hU.baseCenter (a.natAdd 1))
    (hl : hT.baseCenter (j.succAbove l) ∈ sourceOpen) :
    let x : (sourceOpen).toScheme := ⟨hT.baseCenter (j.succAbove l), hl⟩
    hU.baseCenter (l.natAdd 1) = (targetOpen).ι ((complementIso).hom x) ∧
      ((∀ a < j.succAbove l, hT.baseCenter a ≠ hT.baseCenter (j.succAbove l)) →
        ∀ a < l.natAdd 1, hU.baseCenter a ≠ hU.baseCenter (l.natAdd 1)) := by
  intro x
  obtain ⟨p, hp₀, hp₁⟩ := hcenters l
  have htarget := hp₁.symm.trans
    (ρ.mutationBlowupIso_apply_over_complement b hOpp c p x hp₀)
  refine ⟨htarget, fun hfirst a ha heq ↦ ?_⟩
  induction a using Fin.addCases with
  | left a =>
    rw [Subsingleton.elim a (0 : Fin 1), hreverse, htarget] at heq
    have hmem : reverseCenter (IsLocalRing.closedPoint ℂ) ∈ (I₁).support := by
      rw [ρ.mutationTargetCenterIdeal_eq]
      exact (reverseCenter).range_subset_ker_support ⟨_, rfl⟩
    have hdis := (Scheme.IdealSheafData.comap_eq_top_iff (I₁) (targetOpen).ι).mp
      (ρ.mutationTargetCenterIdeal_comap_complement b hOpp c)
    have hout : (complementIso).hom x ∈ (targetOpen).ι ⁻¹ᵁ (I₁).support.compl := by
      rw [hdis]
      trivial
    exact hout (heq ▸ hmem)
  | right a =>
    obtain ⟨z, hz₀, hz₁⟩ := hcenters a
    have hqp := (ρ.mutationBlowupIso_projected_eq_iff b hOpp c
      (q := p) (hp₀.symm ▸ hl)).mp (hz₁.trans (heq.trans hp₁.symm))
    exact hfirst _ (Fin.strictMono_succAbove _ ((Fin.natAdd_lt_natAdd_iff 1).mp ha))
      (hz₀.symm.trans (hqp.trans hp₀))

end TauCeti.Toric.Fan
