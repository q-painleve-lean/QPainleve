/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.SmoothPoint

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Boundary.Component
import QPainleve.Geometry.Toric.Fan.Boundary.Node

/-!
# Closed points of a toric ray divisor

On a complete regular toric surface, a closed point of a ray divisor is a
binomial center in its open orbit or the distinguished point of a corner
containing the ray. This recovers the center of a boundary blowup from its
projected point on the toric surface.
-/

public section

open AlgebraicGeometry Module PointedCone
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "z" => (IsLocalRing.closedPoint k : Spec (CommRingCat.of k))
local notation "center[" ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ k rankTwo (b.detDualEquiv_self (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c z

include hc in
/-- The closed points of a ray divisor are its open-orbit points and the
distinguished points of the two-dimensional cones containing that ray. -/
theorem mem_support_rayBoundaryIdeal_iff (ρ : Φ.Ray) {p : (Φ.finiteFanScheme k)}
    (hp : IsClosed ({p} : Set (Φ.finiteFanScheme k))) :
    p ∈ (Φ.rayDivisorIdeal k hΦ ρ).support ↔
      (∃ c : kˣ, p = center[ρ,c]) ∨
      ∃ σ : Φ.cones, Nat.card (ToricRay σ.val) = 2 ∧ ρ.toCone ≤ σ ∧
        p = Φ.distinguishedSection (R := k) σ z := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  let D := Φ.toricBoundaryIdeal k hc.nonempty_cones
  constructor
  · intro hmem
    by_cases hn : D.IsNodeOfReducedBoundary (Φ.finiteFanSchemeToSpec k) p
    · obtain ⟨σ, ⟨hσ, hpoint⟩, -⟩ :=
        (Φ.isNodeOfReducedBoundary_iff_existsUnique_twoRayCone k hΦ hc rankTwo).mp hn
      exact Or.inr ⟨σ, hσ, (Φ.distinguishedPoint_mem_support_rayBoundaryIdeal_iff k hΦ σ ρ).mp
        (hpoint.symm ▸ hmem), hpoint.symm⟩
    · have hD : p ∈ D.support :=
        support_antitone (boundaryIdeal_le_rayBoundaryIdeal k ρ hΦ) hmem
      obtain ⟨⟨τ, c⟩, hτ, -⟩ :=
        Φ.existsUnique_internalCenter_of_mem_boundary_of_not_isNode k b hΦ hc hp hD hn
      rw [Ray.map_internalCenter_subschemeι, Scheme.Hom.ker_eq_ker_fromSpecResidueField,
        Scheme.ker_fromSpecResidueField_inj] at hτ
      have heq : τ = ρ := (τ.binomialCenter_mem_support_rayBoundaryIdeal_iff k
        hΦ rankTwo (b.detDualEquiv_self _) (τ.surjective_detCharacter b) c ρ).mp (hτ.symm ▸ hmem)
      exact Or.inl ⟨c, heq ▸ hτ.symm⟩
  · rintro (⟨c, rfl⟩ | ⟨σ, -, hρ, rfl⟩)
    · exact (ρ.binomialCenter_mem_support_rayBoundaryIdeal_iff k hΦ rankTwo
        (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) c ρ).mpr rfl
    · exact (Φ.distinguishedPoint_mem_support_rayBoundaryIdeal_iff k hΦ σ ρ).mpr hρ

end TauCeti.Toric.Fan
