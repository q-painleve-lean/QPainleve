/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.PlaneResolution
public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.BaseMultiplicity

/-!
# Proper pivots in a plane resolution

A largest positive order on the successive strict transforms of a divisor
in a specified plane resolution is realized by a proper center on that
divisor. Breaking ties by tower order selects an actual blowup that can be
moved to the front with the total exceptional marking. The order of a proper
center dominates orders infinitely near it, as in [Lutz, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=71
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open TauCeti.SymmetricAlgebra LineBundleClass

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} {n : ℕ}
  {T : BlowupTower X n Y} [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "f" => (X ↘ S)
local notation "P" => Proj (homogeneousSubmodule k (Fin 3 → k))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) 1)

/-- In a specified plane resolution, if a center on a successive strict transform
has positive base order, the earliest one of largest order has positive order
and is the first blowup over a point on the original divisor. The order at
each center is read from the total exceptional coordinates of the specified
pullback of the plane hyperplane class. -/
theorem exists_first_max_base_order_on_strict_transform (hT : IsClosedPointTower X T)
    {C : X.IdealSheafData} (hC : C.IsEffectiveCartier)
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f) :
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let v := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    (∃ j, hT.strictTransformCoefficients C j ≠ 0 ∧ 0 < -v.2 j) →
    ∃ i : Fin n, hT.strictTransformCoefficients C i ≠ 0 ∧ 0 < -v.2 i ∧
      (∀ j, hT.strictTransformCoefficients C j ≠ 0 → -v.2 j ≤ -v.2 i) ∧
      (∀ j < i, hT.strictTransformCoefficients C j ≠ 0 → -v.2 j < -v.2 i) ∧
      (∀ j < i, hT.baseCenter j ≠ hT.baseCenter i) ∧ hT.baseCenter i ∈ C.support := by
  intro hNoetherian v ⟨j, hj, hpos⟩
  let := hNoetherian
  obtain ⟨_, J, -, -, hJ, -, -, horder⟩ := hT.exists_moving_base_ideal_of_plane_resolution g hg
  obtain ⟨i, hi, hmax, hleast, hfirst, hmem⟩ :=
    hT.exists_first_max_baseMultiplicity_on_strictTransform f hC hJ ⟨j, hj⟩
  have hle (l) (hl : hT.strictTransformCoefficients C l ≠ 0) : -v.2 l ≤ -v.2 i := by
    rw [horder l, horder i]
    exact Int.ofNat_le.mpr (hmax l hl)
  refine ⟨i, hi, hpos.trans_le (hle j hj), hle, ?_, hfirst, hmem⟩
  intro l hl hlC
  rw [horder l, horder i]
  exact Int.ofNat_lt.mpr (hleast l hl hlC)

end QPainleve.BlowupTower.IsClosedPointTower
