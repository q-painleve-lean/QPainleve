/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.PlanePivot
public import QPainleve.Geometry.Toric.Fan.Boundary.SmoothPoint
public import QPainleve.Geometry.Toric.Fan.Smooth

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Boundary.Component
import QPainleve.Geometry.Toric.Fan.Boundary.Node
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective

/-!
# Greedy pivots on toric boundary components

A largest positive order on the successive strict transforms of a specified
ray divisor in a plane resolution is a proper center on that ray. It is a
corner on a cone containing the ray or a binomial point on the open orbit.
For the positive section of a Hirzebruch surface, these give the two kinds of
elementary transformation in [Lutz, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry TauCeti.SymmetricAlgebra
open LineBundleClass Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "X" => Φ.algebraicRealization
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "f" => (X ↘ S)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "rankTwo" => (Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "D" => Φ.boundaryIdeal hc.nonempty_cones
local notation "z" => (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ))
local notation "p[" ρ "," c "]" =>
  (Ray.binomialCenter ρ rankTwo (b.detDualEquiv_self (Ray.primitiveGenerator ρ))
    (Ray.surjective_detCharacter ρ b) c) z

/-- In a plane resolution, the earliest maximal positive order on the
successive strict transforms of a specified ray divisor determines a proper pivot.
It is either the distinguished point of a two-ray cone containing the ray, or
the binomial point of that ray for a nonzero parameter. -/
theorem exists_first_max_base_order_on_ray (ρ : Φ.Ray) {Y : Scheme} {n : ℕ}
    {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)
    (g : Y ⟶ P) (hg : g ≫ P ↘ S = T.toBase ≫ f) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X := by
      let : Smooth f := SmoothOfRelativeDimension.smooth 2 f
      exact isNoetherian_of_finiteType f
    let C := Φ.rayBoundaryIdeal hΦ ρ
    let v := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    (∃ j, hT.strictTransformCoefficients C j ≠ 0 ∧ 0 < -v.2 j) →
    ∃ a : Fin n, hT.strictTransformCoefficients C a ≠ 0 ∧ 0 < -v.2 a ∧
      (∀ j, hT.strictTransformCoefficients C j ≠ 0 → -v.2 j ≤ -v.2 a) ∧
      (∀ j < a, hT.strictTransformCoefficients C j ≠ 0 → -v.2 j < -v.2 a) ∧
      (∀ j < a, hT.baseCenter j ≠ hT.baseCenter a) ∧
      ((∃ σ : Φ.cones, Nat.card (ToricRay σ.val) = 2 ∧ ρ.toCone ≤ σ ∧
          Φ.distinguishedPointHom σ z = hT.baseCenter a) ∨
        ∃ c : ℂˣ, hT.baseCenter a = p[ρ,c]) := by
  intro hcones hSmooth hNoetherian C v hne
  let := hcones
  let := hSmooth
  let := hNoetherian
  let : (X).IsProjectiveOver ℂ := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
  obtain ⟨a, ha, hpos, hmax, hleast, hfirst, hmem⟩ :=
    hT.exists_first_max_base_order_on_strict_transform (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ)
      g hg hne
  refine ⟨a, ha, hpos, hmax, hleast, hfirst, ?_⟩
  by_cases hn : (D).IsNodeOfReducedBoundary Φ.algebraicRealizationStructureMap (hT.baseCenter a)
  · obtain ⟨σ, ⟨hσ, hp⟩, -⟩ :=
      (Φ.isNodeOfReducedBoundary_iff_existsUnique_twoRayCone hΦ hc rankTwo).mp hn
    exact Or.inl ⟨σ, hσ, (Φ.distinguishedPoint_mem_support_rayBoundaryIdeal_iff hΦ σ ρ).mp
      (hp.symm ▸ hmem), hp⟩
  · have hd : hT.baseCenter a ∈ (D).support :=
      support_antitone (boundaryIdeal_le_rayBoundaryIdeal ρ hΦ) hmem
    obtain ⟨⟨τ, c⟩, hτ, -⟩ := Φ.existsUnique_internalCenter_of_mem_boundary_of_not_isNode
      b hΦ hc (hT.isClosed_baseCenter a) hd hn
    rw [Ray.map_internalCenter_subschemeι, Scheme.Hom.ker_eq_ker_fromSpecResidueField,
      Scheme.ker_fromSpecResidueField_inj] at hτ
    have heq : τ = ρ := (τ.binomialCenter_mem_support_rayBoundaryIdeal_iff
      hΦ rankTwo (b.detDualEquiv_self _) (τ.surjective_detCharacter b) c ρ).mp (hτ.symm ▸ hmem)
    exact Or.inr ⟨c, heq ▸ hτ.symm⟩

end TauCeti.Toric.Fan
