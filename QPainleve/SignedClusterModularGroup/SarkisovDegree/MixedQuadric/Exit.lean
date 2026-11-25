/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.MixedQuadric.Path

import QPainleve.Geometry.Toric.Fan.Picard.Quadric

/-!
# Mixed two-center exit in the original quadric ruling

A corner on one invariant fiber and a smooth point on the other determine an
exit from a resolved quadric to a new quadric. The new fiber degree is the sum
of the two old ruling coefficients minus the two chosen orders. The comparison
is made in the original ruling so that selected orders can be used directly
after preparation. The link construction follows
[Lutz, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry TauCeti.Toric LineBundleClass TauCeti.SymmetricAlgebra
open Fan (LogarithmicProjection)
open Fan.LogarithmicProjection
open scoped Sarkisov

namespace QPainleve.BlowupTower.IsClosedPointTower

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "fP" => (P ↘ S)
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "f[" Δ "]" => (X[Δ] ↘ S)
local notation "B[" Δ "," h "]" => Fan.boundaryIdeal Δ (Fan.IsComplete.nonempty_cones h)
local notation "rankTwo(" b ")" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "pt" => IsLocalRing.closedPoint ℂ
local notation "center[" b "," ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ rankTwo(b) (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c pt
local notation "mark[" U "," hU "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking U hU f) (Additive.ofMul (pullback g H))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular)
  (hc : Φ.IsComplete) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

variable {Y : Scheme} {n : ℕ} {T : BlowupTower X[Φ] (n + 2) Y}
  (hT : IsClosedPointTower X[Φ] T) (g : Y ⟶ P)
  (hg : g ≫ fP = T.toBase ≫ f[Φ]) (hbir : Scheme.BirationalOver g (𝟙 P))
  {D : Y.IdealSheafData}

local notation "C" => Fan.hirzebruchPicardBasis b 0 hΦ r hr
local notation "x" => mark[T,hT,f[Φ],g]
local notation "β" => Basis.repr (C) (Prod.fst x) 1
local notation "order[" k "]" => -(Prod.snd x) k

include hg hbir in
/-- The first center at a corner on the opposite invariant fiber and the first
center at a smooth point on the retained fiber give a resolved path to a quadric.
The final point tower carries the same plane target. Its fiber degree is positive
and is the sum of the original ruling coefficients minus the two chosen orders. -/
theorem exists_sarkisov_path_of_quadric_opposite_corner_and_smooth_center
    (j l : Fin (n + 2)) (c : ℂˣ)
    (hl : hT.baseCenter l = center[b,r 1,c])
    (hlfirst : ∀ k < l, hT.baseCenter k ≠ hT.baseCenter l)
    (σ : Φ.cones) (hσ : Nat.card (ToricRay σ.val) = 2)
    (hopp : (r 3).toCone ≤ σ)
    (hj : hT.baseCenter j = Φ.distinguishedPointHom σ pt)
    (hjfirst : ∀ k < j, hT.baseCenter k ≠ hT.baseCenter j) :
    letI : Nonempty Φ.cones := hc.nonempty_cones
    letI : SmoothOfRelativeDimension 2 f[Φ] := by
      rw [Fan.algebraicRealization_over, ← rankTwo(b)]
      exact Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    letI : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    letI : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    letI : IsIntegral Y := hT.isIntegral f[Φ]
    ∀ (A : LogarithmicProjection i D), A.fan = Φ → A.hom ≍ T.toBase →
      ∃ (Q : LogarithmicProjection i D) (_ : SarkisovPath A Q)
        (d : Basis (Fin 2) ℤ N) (t : Fin 4 ≃ Q.fan.Ray)
        (ht : (fun k ↦ (t k).primitiveGenerator) = ![d 0, d 1, -d 0, (0 : ℤ) • d 0 - d 1])
        (Z : Scheme) (U : BlowupTower X[Q.fan] (1 + (1 + n)) Z)
        (hU : IsClosedPointTower X[Q.fan] U) (e : Y ≅ Z),
        Q.hom = e.hom ≫ U.toBase ∧ X[Q.fan].IsProjectiveOver ℂ ∧
        (e.inv ≫ g) ≫ fP = U.toBase ≫ f[Q.fan] ∧ Scheme.BirationalOver (e.inv ≫ g) (𝟙 P) ∧
        letI : SmoothOfRelativeDimension 2 f[Q.fan] := by
          rw [Fan.algebraicRealization_over, ← rankTwo(b)]
          exact Q.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Q.isRegular
        B[Q.fan,Q.isComplete].comap U.toBase =
          D.comap e.inv * hU.ramificationIdealSheafToBase ℂ ∧
        let y := mark[U,hU,f[Q.fan],e.inv ≫ g]
        let β' := (Q.fan.hirzebruchPicardBasis d 0 Q.isRegular t ht).repr y.1 1
        0 < β' ∧ β' = β + (C).repr (x).1 0 - order[j] - order[l] := by
  intro A hA hAh
  let : Nonempty Φ.cones := hc.nonempty_cones
  obtain ⟨d, s, hs, hcone, hs₂, hPic⟩ :=
    Φ.exists_exchanged_marking_at_opposite_corner b hΦ hc r hr σ hσ hopp
  obtain ⟨a, ha⟩ := (r 1).exists_binomialCenter_eq_of_basis d b c
  have hl' : hT.baseCenter l = center[d,s 2,a] := by rwa [hs₂, ha]
  obtain ⟨Q, path, d', t, ht, Z, U, hU, e, _, _, hQ, hProj, hg', hbir', hpole,
    _, hdegree, _, hpos⟩ :=
    hT.exists_sarkisov_path_of_quadric_corner_and_smooth_centers d hΦ hc s hs σ hcone
      g hg hbir j l hj (hj ▸ hjfirst) a hl' (hl' ▸ hlfirst) A hA hAh
  refine ⟨Q, path, d', t, ht, Z, U, hU, e, hQ, hProj, hg', hbir', hpole, hpos, ?_⟩
  simpa only [hPic, Basis.repr_reindex_apply, Equiv.symm_swap, Equiv.swap_apply_left,
    Equiv.swap_apply_right] using hdegree

end QPainleve.BlowupTower.IsClosedPointTower
