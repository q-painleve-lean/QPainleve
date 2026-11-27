/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Homaloidal

import QPainleve.SignedClusterModularGroup.SarkisovDegree.Multiplicity

/-!
# High multiplicities on Hirzebruch resolutions

On a specified resolution of a birational map from a Hirzebruch surface to the
plane, the pullback of the line class is nef. Its base coordinates give a positive
fiber degree and nonnegative degree on the section of square `-e`. The homaloidal
identities then force a base order greater than half the fiber degree, except
in the cases of the quadric and the first Hirzebruch surface where ruling exchange
and section contraction apply.

This is the Hirzebruch case of Lemma 8.8 in
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry LineBundleClass Chow TauCeti.SymmetricAlgebra
open TauCeti.Toric

namespace QPainleve.BlowupTower.IsClosedPointTower

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [(Φ.finiteFanScheme k₀).IsProjectiveOver k₀]
  (b : Basis (Fin 2) ℤ N) (e : ℕ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])

local notation "S" => Spec (CommRingCat.of k₀)
local notation "X" => (Φ.finiteFanScheme k₀)
local notation "f" => (X ↘ S)
local notation "P" => Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k₀ (Fin 3 → k₀) 1)
local notation "C" => Fan.hirzebruchPicardBasis k₀ b e hΦ r hr

variable {Y : Scheme.{0}} {n : ℕ} {T : BlowupTower (Φ.finiteFanScheme k₀) n Y}

/-- Every specified Hirzebruch resolution of a birational map to the plane either
has a base order greater than half the fiber degree or falls into one of the two
lower-index cases. With all orders at most half the fiber degree, the quadric
has smaller degree after exchange of rulings, and on the first Hirzebruch surface
the plane degree after section contraction is less than three halves of the
original fiber degree. -/
theorem exists_fiber_degree_lt_two_mul_or_of_hirzebruch_resolution
    (hT : IsClosedPointTower X T) (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f)
    (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f :=
      (by simpa using Module.finrank_eq_card_basis b : Module.finrank ℤ N = 2) ▸
        Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let v : Additive (LineBundleClass X) × (Fin n → ℤ) :=
      (T.picardMarking (k := k₀) hT f).symm (Additive.ofMul (pullback g H))
    let a := (C).repr v.1 0
    let d := (C).repr v.1 1
    (∃ j, d < 2 * (-v.2 j)) ∨
      ((∀ j, 2 * (-v.2 j) ≤ d) ∧ (e = 0 ∧ a < d ∨ e = 1 ∧ 2 * a < 3 * d)) := by
  intro hcones hdim hnoeth v a d
  let := hcones
  let := hdim
  let := hnoeth
  by_cases hhigh : ∃ j, d < 2 * (-v.2 j)
  · exact Or.inl hhigh
  push Not at hhigh
  refine Or.inr ⟨hhigh, ?_⟩
  obtain ⟨hd, ha, hm⟩ := hirzebruch_resolution_degree_bounds k₀ b e hΦ hc r hr hT g hg hbir
  obtain ⟨hsq, hsum⟩ :=
    hT.homaloidal_intersection_identities_of_hirzebruch k₀ b e hΦ hc r hr g hg hbir
  have h := exists_fiber_degree_lt_two_mul_or_of_hirzebruch_homaloidal (Int.natCast_nonneg e)
    hd ha hm (by simpa only [neg_sq] using hsq) hsum
  rcases h with ⟨j, hj⟩ | ⟨he, hlt⟩ | ⟨he, hlt⟩
  · exact (not_lt_of_ge (hhigh j) hj).elim
  · exact Or.inl ⟨by exact_mod_cast he, hlt⟩
  · exact Or.inr ⟨by exact_mod_cast he, hlt⟩

end QPainleve.BlowupTower.IsClosedPointTower
