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

include hc hr in
private theorem exists_exchanged_marking_at_opposite_corner [Nonempty Φ.cones]
    (σ : Φ.cones) (hσ : Nat.card (ToricRay σ.val) = 2) (hopp : (r 3).toCone ≤ σ) :
    ∃ (d : Basis (Fin 2) ℤ N) (s : Fin 4 ≃ Φ.Ray)
      (hs : (fun j ↦ (s j).primitiveGenerator) = ![d 0, d 1, -d 0, (0 : ℤ) • d 0 - d 1]),
      σ.val = hull ℝ (Set.range (i ∘ d)) ∧ s 2 = r 1 ∧
      Φ.hirzebruchPicardBasis d 0 hΦ s hs =
        (Φ.hirzebruchPicardBasis b 0 hΦ r hr).reindex (Equiv.swap 0 1) := by
  obtain ⟨a, u, hu, hu₀, hu₂, hpic⟩ := Φ.exists_quadric_picardBasis_of_fiber b hΦ r hr 1
  have ha : (u 0).toCone ≤ σ := hu₀.symm ▸ hopp
  obtain ⟨d, e, s, hcone, he, hfib, hsec⟩ :=
    Φ.exists_hirzebruch_corner_basis a 0 u hu hΦ hc σ hσ
  have hgen₀ : (s 0).primitiveGenerator = d 0 := congrFun he 0
  have hmem : i ((s 0).primitiveGenerator) ∈ σ.val := by
    rw [hgen₀, hcone]
    exact subset_hull ⟨0, rfl⟩
  have hs₀ : s 0 = u 0 ∧ e = 0 := by
    rcases hsec with h | ⟨h, he'⟩
    · exact h
    · have hpos : i (a 0) ∈ σ.val := ha (by
        rw [Fan.Ray.toCone_eq_hull_primitiveGenerator]
        exact subset_hull (by simp [congrFun hu 0]))
      have hneg : -(i (a 0)) ∈ σ.val := by
        have hu₂' : (u 2).primitiveGenerator = -a 0 := congrFun hu 2
        simpa only [h, hu₂', map_neg] using hmem
      have hn : i (a 0) ≠ 0 :=
        fun hz ↦ (a.ne_zero 0) (Φ.lattice.injective (hz.trans (map_zero i).symm))
      exact ((Φ.isToricCone σ.property).salient _ hpos hn hneg).elim
  obtain ⟨hs₀, rfl⟩ := hs₀
  refine ⟨d, s, he, hcone, ?_, ?_⟩
  · have h : d 0 = a 0 :=
      hgen₀.symm.trans ((congrArg Fan.Ray.primitiveGenerator hs₀).trans (congrFun hu 0))
    exact hu₂ ▸ Fan.Ray.primitiveGenerator_injective
      ((congrFun he 2).trans ((congrArg Neg.neg h).trans (congrFun hu 2).symm))
  · rw [← hpic]
    apply DFunLike.ext
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [Fan.hirzebruchPicardBasis_apply_zero]
      rcases hfib with h | h
      · rw [h, ← Fan.hirzebruchPicardBasis_apply_zero a 0 hΦ u hu]
      · rw [h, ← Fan.hirzebruchPicardBasis_apply_zero_eq_ray_three a 0 hΦ u hu]
    · rw [Fan.hirzebruchPicardBasis_apply_one, hs₀,
        ← Fan.hirzebruchPicardBasis_apply_one a 0 hΦ u hu]

variable {Y : Scheme} {n : ℕ} {T : BlowupTower X[Φ] (n + 2) Y}
  (hT : IsClosedPointTower X[Φ] T) (g : Y ⟶ P)
  (hg : g ≫ fP = T.toBase ≫ f[Φ]) (hbir : Scheme.BirationalOver g (𝟙 P))
  {D : Y.IdealSheafData}

local notation "C" => Fan.hirzebruchPicardBasis b 0 hΦ r hr
local notation "x" => mark[T,hT,f[Φ],g]
local notation "β" => Basis.repr (C) (Prod.fst x) 1
local notation "order[" k "]" => -(Prod.snd x) k

include hg hbir hr in
/-- A high proper corner on the fiber opposite a high proper smooth center
gives a resolved path to a quadric of strictly smaller fiber degree. Both
orders are measured in the original ruling. The new marked tower carries the
same map to the target plane and its pole factorization. -/
theorem exists_sarkisov_path_primary_decrease_of_prepared_quadric
    (j l : Fin (n + 2)) (c : ℂˣ)
    (hl : hT.baseCenter l = center[b,r 1,c])
    (hlfirst : ∀ k < l, hT.baseCenter k ≠ hT.baseCenter l)
    (σ : Φ.cones) (hσ : Nat.card (ToricRay σ.val) = 2) (hopp : (r 3).toCone ≤ σ)
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
  obtain ⟨d, s, hs, hcone, hs₂, hPic⟩ :=
    exists_exchanged_marking_at_opposite_corner b hΦ hc r hr σ hσ hopp
  obtain ⟨a, ha⟩ := (r 1).exists_binomialCenter_eq_of_basis d b c
  have hl' : hT.baseCenter l = center[d,s 2,a] := by rwa [hs₂, ha]
  have hβ : (Φ.hirzebruchPicardBasis d 0 hΦ s hs).repr (x).1 0 = β := by
    rw [hPic, Basis.repr_reindex_apply]
    rfl
  let : X[Φ].IsProjectiveOver ℂ := Φ.isProjectiveOver_quadric b hΦ hc r hr
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
