/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.MixedQuadric.Path

import QPainleve.Geometry.Toric.Fan.Picard.FiberDegree
import QPainleve.Geometry.Toric.Fan.Picard.Homaloidal
import QPainleve.Geometry.Toric.Fan.Picard.Quadric
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Pivots

/-!
# Mixed continuation of a Hirzebruch preparation

The prepared ruling has a high center in the interior of a retained invariant
fiber. If the other high center lies at an endpoint of the opposite fiber, a
corner transformation and a mutation decrease the primary Sarkisov degree.
The inequality is independent of the total base order accumulated during
preparation. This is the mixed continuation in
[Lutz, Proposition 8.11, Case C][HKL].

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

include hg hbir hr in
/-- A high proper corner and a distinct high proper smooth fiber center give a
resolved path to a quadric of strictly smaller fiber degree when all other orders
are at most half the original degree. The two centers lie on opposite fibers.
The new marked tower carries the same map to the target plane and its pole
factorization. -/
theorem exists_sarkisov_path_primary_decrease_of_prepared_quadric
    (j l : Fin (n + 2)) (hjl : j ≠ l) (c : ℂˣ)
    (hl : hT.baseCenter l = center[b,r 1,c])
    (hlfirst : ∀ k < l, hT.baseCenter k ≠ hT.baseCenter l)
    (σ : Φ.cones) (hσ : Nat.card (ToricRay σ.val) = 2)
    (hj : hT.baseCenter j = Φ.distinguishedPointHom σ pt)
    (hjfirst : ∀ k < j, hT.baseCenter k ≠ hT.baseCenter j) :
    letI : Nonempty Φ.cones := hc.nonempty_cones
    letI : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo(b) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    letI : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    letI : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    letI : IsIntegral Y := hT.isIntegral f[Φ]
    ∀ (A : LogarithmicProjection i D), A.fan = Φ → A.hom ≍ T.toBase →
      β < 2 * order[j] → β < 2 * order[l] →
      (∀ k, k ≠ j → k ≠ l → 2 * order[k] ≤ β) →
      ∃ (Q : LogarithmicProjection i D) (_ : SarkisovPath A Q)
        (d : Basis (Fin 2) ℤ N) (t : Fin 4 ≃ Q.fan.Ray)
        (ht : (fun k ↦ (t k).primitiveGenerator) = ![d 0, d 1, -d 0, (0 : ℤ) • d 0 - d 1])
        (Z : Scheme) (a : ℕ) (U : BlowupTower X[Q.fan] a Z)
        (hU : IsClosedPointTower X[Q.fan] U) (e : Y ≅ Z),
        Q.hom = e.hom ≫ U.toBase ∧ X[Q.fan].IsProjectiveOver ℂ ∧
        (e.inv ≫ g) ≫ fP = U.toBase ≫ f[Q.fan] ∧ Scheme.BirationalOver (e.inv ≫ g) (𝟙 P) ∧
        letI : SmoothOfRelativeDimension 2 f[Q.fan] :=
          rankTwo(b) ▸ Q.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Q.isRegular
        B[Q.fan,Q.isComplete].comap U.toBase =
          D.comap e.inv * hU.ramificationIdealSheafToBase ℂ ∧
        let y := mark[U,hU,f[Q.fan],e.inv ≫ g]
        let β' := (Q.fan.hirzebruchPicardBasis d 0 Q.isRegular t ht).repr y.1 1
        0 < β' ∧ β' < β := by
  intro A hA hAh hjlarge hllarge hsmall
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : SmoothOfRelativeDimension 2 f[Φ] :=
    rankTwo(b) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
  let : IsIntegral Y := hT.isIntegral f[Φ]
  let : X[Φ].IsProjectiveOver ℂ := Φ.isProjectiveOver_quadric b hΦ hc r hr
  have hlog : B[Φ,hc].comap T.toBase ≤ hT.ramificationIdealSheafToBase ℂ := by
    rcases A with ⟨Ψ, hreg, hcomplete, f, hover, hdom, hpole⟩
    dsimp only at hA hAh
    subst Ψ
    obtain rfl : f = T.toBase := eq_of_heq hAh
    rw [hT.ramificationIdealSheafToBase_def ℂ, hpole]
    exact mul_le_of_le_one_left' le_top
  have hopp := hT.opposite_hirzebruch_fiber_le_of_high_corner b 0 hΦ hc r hr g hg σ hσ
    hlog c hl hj hllarge hjlarge hjl
  obtain ⟨d, s, hs, hcone, hs₂, hPic⟩ :=
    Φ.exists_exchanged_marking_at_opposite_corner b hΦ hc r hr σ hσ hopp
  obtain ⟨a, ha⟩ := (r 1).exists_binomialCenter_eq_of_basis d b c
  have hl' : hT.baseCenter l = center[d,s 2,a] := by rwa [hs₂, ha]
  have hβ : (Φ.hirzebruchPicardBasis d 0 hΦ s hs).repr (x).1 0 = β := by
    rw [hPic, Basis.repr_reindex_apply]
    rfl
  have hu := hT.base_order_le_hirzebruch_fiber_degree b 0 hΦ r hr hc g hg
  have hb := hT.hirzebruch_resolution_degree_bounds b 0 hΦ hc r hr g hg hbir
  obtain ⟨Q, path, d', t, ht, Z, U, hU, e, _, _, hQ, hProj, hg', hbir', hpole,
      _, _, _, hpos, hlt, _⟩ :=
    hT.exists_sarkisov_path_decrease_of_quadric_corner_and_smooth_centers d hΦ hc s hs σ hcone
      g hg hbir j l hj (hj ▸ hjfirst) a hl' (hl' ▸ hlfirst) A hA hAh
      (hβ.symm ▸ hjlarge) (hβ.symm ▸ hu j) (hβ.symm ▸ hllarge) (hβ.symm ▸ hu l)
      (fun k hkj hkl ↦ ⟨hb.2.2 k, hβ.symm ▸ hsmall k hkj hkl⟩)
  refine ⟨Q, path, d', t, ht, Z, _, U, hU, e, hQ, hProj, hg', hbir', hpole, ?_⟩
  exact ⟨hpos, hβ ▸ hlt⟩

end QPainleve.BlowupTower.IsClosedPointTower
