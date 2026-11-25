/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Quadric.PlanePath
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Quadric.SelectedCenters

import QPainleve.Geometry.Toric.Fan.Picard.FiberDegree
import QPainleve.Geometry.Toric.Fan.Picard.Quadric
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Decrease

/-!
# Sarkisov decrease at smooth points of the quadric fibers

When the high base orders are over the interiors of distinct invariant fibers,
the one-center and two-center links apply in the exchanged ruling. In both cases
the path starts at the specified projection, and its terminal point tower resolves
the same map to the plane with strictly smaller bidegree.

The link blocks are the smooth-center cases of Proposition 8.11 in
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public section

open AlgebraicGeometry CategoryTheory Module TauCeti.Toric
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData TauCeti.SymmetricAlgebra
open Fan Fan.LogarithmicProjection
open scoped Sarkisov

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular)
  (hc : Φ.IsComplete) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "f[" Δ "]" => (X[Δ] ↘ S)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "fP" => (P ↘ S)
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "degree" => Basis.picardTwistEquiv (Pi.basisFun ℂ (Fin 3))
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "B[" Δ "," h "]" => Fan.boundaryIdeal Δ (Fan.IsComplete.nonempty_cones h)
local notation "Π[" d "]" => Fan.projectiveSpace d (Fan.lattice Φ)
local notation "hcΠ[" d "]" => Fan.isComplete_projectiveSpace d (Fan.lattice Φ)
local notation "planeIso[" d "]" =>
  Fan.projectivePlaneIso d (Fan.lattice Φ) ≪≫ Basis.polynomialProjIso (Pi.basisFun ℂ (Fin 3))
local notation "fiberRay[" t "]" => r ((![1, 3] : Fin 2 → Fin 4) t)
local notation "center[" a "," ρ "," c "]" => Fan.Ray.binomialCenter ρ
  (Eq.trans (finrank_eq_card_basis a) (Fintype.card_fin 2))
  (Basis.detDualEquiv_self a (Fan.Ray.primitiveGenerator ρ)) (Fan.Ray.surjective_detCharacter ρ a)
  c (IsLocalRing.closedPoint ℂ)
local notation "mark[" U "," hU "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking U hU f) (Additive.ofMul (pullback g H))

variable {Y : Scheme} {n : ℕ} {T : BlowupTower X[Φ] n Y}
  (hT : IsClosedPointTower X[Φ] T) (g : Y ⟶ P)

private theorem two_mul_plane_degree_lt_of_unique_high_order
    [Φ.algebraicRealization.IsProjectiveOver ℂ]
    (hg : g ≫ fP = T.toBase ≫ f[Φ]) (hbir : Scheme.BirationalOver g (𝟙 P))
    (j : Fin n) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let x := mark[T,hT,f[Φ],g]
    let β := (Φ.hirzebruchPicardBasis b 0 hΦ r hr).repr x.1 0
    let α := (Φ.hirzebruchPicardBasis b 0 hΦ r hr).repr x.1 1
    let m := fun k ↦ -x.2 k
    β < 2 * m j → (∀ k ≠ j, 2 * m k ≤ β) → 2 * (β + α - m j) < 3 * β := by
  intro hcones hdim x β α m hhigh hsmall
  let := hcones
  let := hdim
  have hUpper : m j ≤ β := hT.base_order_le_quadric_exchanged_fiber_degree b hΦ hc r hr g hg j
  have hNonneg : ∀ k, 0 ≤ m k :=
    (hT.hirzebruch_resolution_degree_bounds b 0 hΦ hc r hr g hg hbir).2.2
  obtain ⟨hsq, hsum⟩ := hT.homaloidal_intersection_identities_of_hirzebruch b 0 hΦ hc r hr g hg hbir
  have hsq' : ∑ k, m k ^ 2 = 2 * α * β - 1 := by
    simpa only [m, neg_sq, Nat.cast_zero, zero_mul, sub_zero, mul_right_comm 2 α β] using hsq
  have hsum' : ∑ k, m k = 2 * α + 2 * β - 3 := by
    simpa only [m, Nat.cast_zero, sub_zero, add_comm (2 * α) (2 * β)] using hsum
  exact (quadric_sarkisov_degree_decrease_of_single (by omega) j hsq' hsum' hhigh.le hUpper
    (fun k hk ↦ ⟨hNonneg k, hsmall k hk⟩)).2

private theorem transverse_degree_lt_sum_of_two_high_orders
    [X[Φ].IsProjectiveOver ℂ]
    (hg : g ≫ fP = T.toBase ≫ f[Φ]) (hbir : Scheme.BirationalOver g (𝟙 P))
    {j l : Fin n} (hjl : j ≠ l) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let x := mark[T,hT,f[Φ],g]
    let β := (Φ.hirzebruchPicardBasis b 0 hΦ r hr).repr x.1 1
    let α := (Φ.hirzebruchPicardBasis b 0 hΦ r hr).repr x.1 0
    let m := fun k ↦ -x.2 k
    β < 2 * m j → β < 2 * m l → (∀ k, k ≠ j → k ≠ l → 2 * m k ≤ β) →
      α < m j + m l := by
  intro hcones hdim x β α m hj hl hsmall
  let := hcones
  let := hdim
  have hUpper := hT.base_order_le_hirzebruch_fiber_degree b 0 hΦ r hr hc g hg
  obtain ⟨hβ, -, hn⟩ := hT.hirzebruch_resolution_degree_bounds b 0 hΦ hc r hr g hg hbir
  obtain ⟨hsq, hsum⟩ := hT.homaloidal_intersection_identities_of_hirzebruch b 0 hΦ hc r hr g hg hbir
  have hlt : β + α - m j - m l < β := (quadric_sarkisov_degree_decrease_of_pair hβ hjl
    (by simpa only [m, neg_sq, Nat.cast_zero, zero_mul, sub_zero] using hsq)
    (by simpa only [m, Nat.cast_zero, sub_zero] using hsum)
    hj.le (hUpper j) hl.le (hUpper l) (fun k hkj hkl ↦ ⟨hn k, hsmall k hkj hkl⟩)).2
  omega

/-- Suppose the high base orders of a logarithmic quadric-to-plane resolution
are first centers over the interiors of distinct invariant fibers and there is
at least one such center. There is a resolved Sarkisov path from the specified
projection to a plane or quadric resolution of strictly smaller Sarkisov degree.
The endpoint is identified with its ordered point tower, with the same map to
the target plane and the transported pole factorization. -/
theorem exists_sarkisov_path_decrease_of_quadric_high_fiber_centers
    (hg : g ≫ fP = T.toBase ≫ f[Φ]) (hbir : Scheme.BirationalOver g (𝟙 P))
    {D : Y.IdealSheafData} :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : IsIntegral Y := hT.isIntegral f[Φ]
    let x := mark[T,hT,f[Φ],g]
    let β := (Φ.hirzebruchPicardBasis b 0 hΦ r hr).repr x.1 1
    let m := fun j ↦ -x.2 j
    let high := Finset.univ.filter (fun j ↦ β < 2 * m j)
    B[Φ,hc].comap T.toBase = D * hT.ramificationIdealSheafToBase ℂ →
    high.Nonempty →
    (∃ fiber : (↑high : Type) ↪ Fin 2, ∀ j : high,
      (∀ k < j.val, hT.baseCenter k ≠ hT.baseCenter j) ∧
      ∃ c : ℂˣ, hT.baseCenter j = center[b,fiberRay[fiber j],c]) →
    ∃ (A B : LogarithmicProjection i D) (_ : SarkisovPath A B),
      A.fan = Φ ∧ A.hom ≍ T.toBase ∧
      ((∃ (d : Basis (Fin 2) ℤ N) (Z : Scheme) (l : ℕ) (U : BlowupTower P l Z)
        (hU : IsClosedPointTower P U) (e : Y ≅ Z),
        B.fan = Π[d] ∧ B.hom ≍ e.hom ≫ U.toBase ≫ (planeIso[d]).inv ∧
        (e.inv ≫ g) ≫ fP = U.toBase ≫ fP ∧ Scheme.BirationalOver (e.inv ≫ g) (𝟙 P) ∧
        (B[Π[d],hcΠ[d]].comap (planeIso[d]).inv).comap U.toBase =
          D.comap e.inv * hU.ramificationIdealSheafToBase ℂ ∧
        let y := mark[U,hU,fP,e.inv ≫ g]
        0 < degree y.1 ∧ ∀ M' M, planeSarkisovBidegree (degree y.1).toNat M' <
          hirzebruchSarkisovBidegree β.toNat M) ∨
      (∃ (Ω : Fan i) (hΩ : Ω.IsRegular) (hcΩ : Ω.IsComplete) (d : Basis (Fin 2) ℤ N)
        (s : Fin 4 ≃ Ω.Ray)
        (hs : (fun j ↦ (s j).primitiveGenerator) = ![d 0, d 1, -d 0, (0 : ℤ) • d 0 - d 1])
        (Z : Scheme) (l : ℕ) (U : BlowupTower X[Ω] l Z)
        (hU : IsClosedPointTower X[Ω] U) (e : Y ≅ Z),
        B.fan = Ω ∧ B.hom ≍ e.hom ≫ U.toBase ∧ X[Ω].IsProjectiveOver ℂ ∧
        (e.inv ≫ g) ≫ fP = U.toBase ≫ f[Ω] ∧ Scheme.BirationalOver (e.inv ≫ g) (𝟙 P) ∧
        let : Nonempty Ω.cones := hcΩ.nonempty_cones
        let : SmoothOfRelativeDimension 2 f[Ω] :=
          rankTwo ▸ Ω.smoothOfRelativeDimension_algebraicRealizationStructureMap hΩ
        B[Ω,hcΩ].comap U.toBase = D.comap e.inv * hU.ramificationIdealSheafToBase ℂ ∧
        let y := mark[U,hU,f[Ω],e.inv ≫ g]
        let β' := (Ω.hirzebruchPicardBasis d 0 hΩ s hs).repr y.1 1
        0 < β' ∧ ∀ M' M, hirzebruchSarkisovBidegree β'.toNat M' <
          hirzebruchSarkisovBidegree β.toNat M)) := by
  classical
  intro hcones hdim hY hSmooth hIntegral x β m high hpole hhigh
  rintro ⟨fiber, hfiber⟩
  let : X[Φ].IsProjectiveOver ℂ := Φ.isProjectiveOver_quadric b hΦ hc r hr
  obtain ⟨j, hj⟩ := hhigh
  let j₀ : high := ⟨j, hj⟩
  have hlarge (k : high) : β < 2 * m k := (Finset.mem_filter.mp k.property).2
  have hsmall (k : Fin n) (hk : k ∉ high) : 2 * m k ≤ β := by
    simpa only [high, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hk
  by_cases hex : ∃ l : high, l.val ≠ j
  · obtain ⟨l, hne⟩ := hex
    -- Any second high order lies on the opposite fiber. The embedding excludes
    -- a third high order.
    have opposite : ∀ a b : Fin 2, a ≠ b → a = Equiv.swap 0 1 b := by decide
    have hfl (k : high) (hk : k.val ≠ j) : fiber k = Equiv.swap 0 1 (fiber j₀) :=
      opposite _ _ (fun he ↦ hk (congrArg Subtype.val (fiber.injective he)))
    obtain ⟨c, hjc⟩ := (hfiber j₀).2
    obtain ⟨d, hld⟩ := (hfiber l).2
    have hlc : hT.baseCenter l = center[b,fiberRay[Equiv.swap 0 1 (fiber j₀)],d] := by
      rw [hld, hfl l hne]
    have hnothigh (k : Fin n) (hkj : k ≠ j) (hkl : k ≠ l) : k ∉ high := by
      intro hk
      exact hkl (congrArg Subtype.val (fiber.injective ((hfl ⟨k, hk⟩ hkj).trans (hfl l hne).symm)))
    have hsum := hT.transverse_degree_lt_sum_of_two_high_orders b hΦ hc r hr g hg hbir
      hne.symm (hlarge j₀) (hlarge l) (fun k hk hl ↦ hsmall k (hnothigh k hk hl))
    obtain ⟨A, B, p, e, t, ht, Z, _, U, hU, f, -, hA, hAh, hBh, hProj, hg', hbir', hpole',
      hpos, -, hlt⟩ :=
      hT.exists_sarkisov_path_of_quadric_two_smooth_fiber_centers b hΦ hc r hr g hg hbir
        j l hne.symm (fiber j₀) c d hjc hlc (hfiber j₀).1 (hfiber l).1 hpole hsum
    refine ⟨A, B, p, hA, hAh, Or.inr ⟨_, B.isRegular, B.isComplete, e, t, ht,
      Z, _, U, hU, f, rfl, heq_of_eq hBh, hProj, hg', hbir', hpole', hpos, fun M' M ↦ ?_⟩⟩
    simp only [Prod.Lex.lt_iff, ofLex_hirzebruchSarkisovBidegree]
    have hβpos : 0 < β := hpos.trans hlt
    exact Or.inl (Nat.mul_lt_mul_of_pos_left ((Int.toNat_lt_toNat hβpos).mpr hlt) (by decide))
  · have hnothigh (k : Fin n) (hkj : k ≠ j) : k ∉ high := fun hk ↦ hex ⟨⟨k, hk⟩, hkj⟩
    obtain ⟨d, s, hs, h₀, -, hpic⟩ :=
      Φ.exists_quadric_picardBasis_of_fiber b hΦ r hr (fiber j₀)
    obtain ⟨c, hcenter⟩ := (hfiber j₀).2
    obtain ⟨a, ha⟩ := (fiberRay[fiber j₀]).exists_binomialCenter_eq_of_basis d b c
    have hjc : hT.baseCenter j = center[d,s 0,a] := by rw [h₀, ha, hcenter]
    have hβ : (Φ.hirzebruchPicardBasis d 0 hΦ s hs).repr x.1 0 = β := by
      rw [hpic, Basis.repr_reindex_apply]
      rfl
    have hn : 1 ≤ n := by have := j.isLt; omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
    have hlt :=
      hT.two_mul_plane_degree_lt_of_unique_high_order d hΦ hc s hs g hg hbir j
        (hβ.symm ▸ hlarge j₀) (fun u hu ↦ hβ.symm ▸ hsmall u (hnothigh u hu))
    obtain ⟨e, -, A, B, p, Z, U, hU, f, hA, hAh, hB, hBh, -, -, hg', hbir', hpole',
      hdegree, -, -, -, hpos⟩ :=
      hT.exists_sarkisov_path_of_quadric_smooth_center d hΦ hc s hs g hg hbir
        a j hjc (hjc ▸ (hfiber j₀).1) D hpole
    refine ⟨A, B, p, hA, hAh, Or.inl ⟨e, Z, _, U, hU, f, hB, hBh, hg', hbir', hpole', hpos,
      fun M' M ↦ ?_⟩⟩
    rw [Prod.Lex.lt_iff, ofLex_planeSarkisovBidegree, ofLex_hirzebruchSarkisovBidegree]
    refine Or.inl ?_
    have hLess : 2 * degree (mark[U,hU,fP,f.inv ≫ g]).1 < 3 * β := by
      rw [hdegree, ← hβ]
      exact hlt
    omega

end QPainleve.BlowupTower.IsClosedPointTower
