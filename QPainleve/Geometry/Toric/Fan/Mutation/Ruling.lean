/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Mutation.Blowup

import QPainleve.Geometry.Toric.Fan.Ruling.Negation
import QPainleve.Geometry.Toric.Fan.Ruling.Torus

/-!
# Invariant fibers under mutation

The two projections from a common mutation blowup agree on the invariant
fiber of a marked point in either sign convention for the ruling. These
points lie in the complement of the fiber contracted by the mutation.
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric.Fan

variable (k₀ : Type) [Field k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (ρ : Φ.Ray) (b : Basis (Fin 2) ℤ N)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : k₀ˣ)

local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "I₀" => ρ.mutationSourceCenterIdeal b c
local notation "I₁" => ρ.mutationTargetCenterIdeal b hOpp c
local notation "χ" => LinearMap.toAddMonoidHom (b.detDualEquiv (Fan.Ray.primitiveGenerator ρ))
local notation "hχ" => Φ.detCharacter_nonneg_or_nonpos b hv hp hOpp
local notation "hχ'" => Φ.mutationDetCharacter_nonneg_or_nonpos b hv hp hOpp
local notation "q₀" => Φ.characterRuling k₀ χ hχ
local notation "q₁" => Fan.characterRuling k₀ Ψ χ hχ'
local notation "p[" j "," a "]" => projectiveLine.polynomialPoint k₀ (RingHom.id k₀) j a
local notation "pt" => (IsLocalRing.closedPoint k₀ : Spec (CommRingCat.of k₀))
local notation "sourceOpen" => Φ.mutationComplement b hχ (c : k₀)

private theorem coordinatePoint_mem_mutationRulingComplement (j : Fin 2) :
    p[j,0] pt ∈ mutationRulingComplement (c : k₀) := by
  have htorus (z : Spec (CommRingCat.of k₀)) :
      p[0,-(↑c⁻¹ : k₀)] z ∈ Set.range (projectiveLineTorusι k₀) := by
    refine ⟨projectiveLineTorusPoint k₀ (-c⁻¹) z, ?_⟩
    have he : projectiveLineTorusPoint k₀ (-c⁻¹) ≫ projectiveLineTorusι k₀ = p[0,-(↑c⁻¹ : k₀)] := by
      rw [projectiveLineTorusPoint_comp_projectiveLineTorusι, Units.val_neg]
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun f : Spec (.of k₀) ⟶ projectiveLine k₀ ↦ f z) he
  rw [mutationRulingComplement_eq_compl_support, ← SetLike.mem_coe,
    TopologicalSpace.Closeds.coe_compl, projectiveLine.support_ker_polynomialPoint,
    Set.mem_compl_iff, Set.mem_singleton_iff]
  exact fun he ↦ polynomialPoint_zero_notMem_range_projectiveLineTorusι k₀ j pt
    (he.symm ▸ htorus pt)

/-- A pair of points projected from the common mutation blowup have the same
invariant ruling value. If the source projection is on the selected
invariant fiber, the source point lies outside the pivot fiber. -/
theorem Ray.mutationBlowupIso_apply_ruling_eq_coordinatePoint (m : N →+ ℤ)
    (hm : m = χ ∨ m = -χ)
    (h₀ : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)
    (h₁ : ∀ σ : (Ψ).cones, (∀ x ∈ σ.val, 0 ≤ (Ψ).lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, (Ψ).lattice.realCharacter m x ≤ 0)
    (z : (I₀).blowup) (j : Fin 2) :
    let x := (I₀).blowupToBase z
    let y := (I₁).blowupToBase ((ρ.mutationBlowupIso b hOpp c).hom z)
    Φ.characterRuling k₀ m h₀ x = p[j,0] pt →
      (Ψ).characterRuling k₀ m h₁ y = p[j,0] pt ∧ x ∈ sourceOpen := by
  intro x y hx
  have hval : q₁ y = q₀ x := by
    have he := congrArg (fun f ↦ f z) (ρ.mutationBlowupIso_hom_comp_ruling b hOpp c)
    simpa only [x, y, Scheme.Hom.comp_apply] using he
  have hmem (k : Fin 2) (he : q₀ x = p[k,0] pt) : x ∈ sourceOpen := by
    rw [mutationComplement_eq, Scheme.Hom.mem_preimage, he]
    rw [projectiveLine.basicOpen_coord_add_smul_eq_compl_support c]
    simpa only [mutationRulingComplement_eq_compl_support] using
      coordinatePoint_mem_mutationRulingComplement k₀ c k
  rcases hm with hm | hm <;> subst m
  · exact ⟨hval.trans hx, hmem j hx⟩
  · have h₀eq := Φ.comap_ker_coordinatePoint_characterRuling_neg k₀ χ hχ h₀ j
    have h₁eq := (Ψ).comap_ker_coordinatePoint_characterRuling_neg k₀ χ hχ' h₁ j
    have hsrc := (projectiveLine.mem_support_comap_ker_polynomialPoint_iff k₀ _ x j 0).mpr hx
    rw [h₀eq] at hsrc
    have hxe := (projectiveLine.mem_support_comap_ker_polynomialPoint_iff k₀ _ x j.rev 0).mp hsrc
    refine ⟨(projectiveLine.mem_support_comap_ker_polynomialPoint_iff k₀ _ y j 0).mp ?_,
      hmem j.rev hxe⟩
    rw [h₁eq]
    exact (projectiveLine.mem_support_comap_ker_polynomialPoint_iff k₀ _ y j.rev 0).mpr
      (hval.trans hxe)

end TauCeti.Toric.Fan
