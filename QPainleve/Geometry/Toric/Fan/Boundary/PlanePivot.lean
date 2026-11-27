/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.PlanePivot
public import QPainleve.Geometry.Toric.Fan.Boundary.RayPoint

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

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] {N V : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "X" => Φ.finiteFanScheme k
local notation "S" => Spec (CommRingCat.of k)
local notation "f" => (X ↘ S)
local notation "P" => Proj (homogeneousSubmodule k (Fin 3 → k))
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) 1)
local notation "rankTwo" => (Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "z" => (IsLocalRing.closedPoint k : Spec (CommRingCat.of k))
local notation "p[" ρ "," c "]" =>
  (Ray.binomialCenter ρ k rankTwo (b.detDualEquiv_self (Ray.primitiveGenerator ρ))
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
      (Φ.finiteFanScheme_over k).symm ▸
        (rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ)
    let : IsNoetherian X := by
      let : Smooth f := SmoothOfRelativeDimension.smooth 2 f
      exact isNoetherian_of_finiteType f
    let C := Φ.rayDivisorIdeal k hΦ ρ
    let v := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    (∃ j, hT.strictTransformCoefficients C j ≠ 0 ∧ 0 < -v.2 j) →
    ∃ a : Fin n, hT.strictTransformCoefficients C a ≠ 0 ∧ 0 < -v.2 a ∧
      (∀ j, hT.strictTransformCoefficients C j ≠ 0 → -v.2 j ≤ -v.2 a) ∧
      (∀ j < a, hT.strictTransformCoefficients C j ≠ 0 → -v.2 j < -v.2 a) ∧
      (∀ j < a, hT.baseCenter j ≠ hT.baseCenter a) ∧
      ((∃ σ : Φ.cones, Nat.card (ToricRay σ.val) = 2 ∧ ρ.toCone ≤ σ ∧
          Φ.distinguishedSection (R := k) σ z = hT.baseCenter a) ∨
        ∃ c : kˣ, hT.baseCenter a = p[ρ,c]) := by
  intro hcones hSmooth hNoetherian C v hne
  let := hcones
  let := hSmooth
  let := hNoetherian
  let : (X).IsProjectiveOver k := Φ.isProjectiveOver_finiteFanScheme_of_isComplete k hΦ hc b
  obtain ⟨a, ha, hpos, hmax, hleast, hfirst, hmem⟩ :=
    hT.exists_first_max_base_order_on_strict_transform (Φ.isEffectiveCartier_rayDivisorIdeal k hΦ ρ)
      g hg hne
  refine ⟨a, ha, hpos, hmax, hleast, hfirst, ?_⟩
  rcases (Φ.mem_support_rayBoundaryIdeal_iff k b hΦ hc ρ (hT.isClosed_baseCenter a)).mp hmem with
    ⟨c, hp⟩ | ⟨σ, hσ, hρ, hp⟩
  · exact Or.inr ⟨c, hp⟩
  · exact Or.inl ⟨σ, hσ, hρ, hp.symm⟩

end TauCeti.Toric.Fan
