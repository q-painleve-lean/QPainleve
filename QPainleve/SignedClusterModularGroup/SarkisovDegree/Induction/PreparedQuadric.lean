/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.Marking

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Blowup.Tower.Proximity
import QPainleve.Geometry.Toric.Fan.Picard.FiberDegree
import QPainleve.SignedClusterModularGroup.SarkisovDegree.MixedQuadric.Continuation
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Pivots.OppositeFiber
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Quadric.HighMultiplicity

/-!
# Primary Sarkisov decrease on a prepared quadric

With a high order on the retained open fiber orbit and low orders on the open sections,
the smooth and mixed quadric links give a primary Sarkisov decrease when at most one
other order is high. The only remaining configuration has high orders at both the first
and a later center over one opposite corner. On the first blowup of that corner,
all remaining high orders above it project to a single point of the exceptional curve.
The comparison preserves the marked plane target independently of the total
order introduced by the preparation in
[Lutz, Proposition 8.11, Case C][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData TauCeti.SymmetricAlgebra
open scoped Sarkisov

namespace TauCeti.Toric.Fan.LogarithmicProjection

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "fP" => (P ↘ S)
local notation "coords" => Pi.basisFun ℂ (Fin 3)
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "plane[" d "," hi "]" => Fan.projectiveSpace d hi
local notation "planeIso[" d "," hi "]" =>
  (Fan.projectivePlaneIso d hi ≪≫ Basis.polynomialProjIso coords)
local notation "mark[" U "," hU "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking U hU f) (Additive.ofMul (pullback g H))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
  {Y : Scheme} {n : ℕ} {T : BlowupTower Φ.algebraicRealization n Y}
  (hT : IsClosedPointTower Φ.algebraicRealization T) (g : Y ⟶ P)
  (hg : g ≫ fP = T.toBase ≫ (Φ.algebraicRealization ↘ S))
  (hbir : Scheme.BirationalOver g (𝟙 P))
  {b' : Basis (Fin 2) ℤ N} {hi : IsIntegralLattice i} {D : Y.IdealSheafData}

local notation "f[" Δ "]" => (Fan.algebraicRealization Δ ↘ S)
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "pt" => IsLocalRing.closedPoint ℂ
local notation "center[" u "," c "]" =>
  Fan.Ray.binomialCenter u rankTwo (b.detDualEquiv_self (Fan.Ray.primitiveGenerator u))
    (Fan.Ray.surjective_detCharacter u b) c pt
local notation "x" => mark[T,hT,f[Φ],g]
local notation "β" => Basis.repr (Φ.hirzebruchPicardBasis b 0 hΦ r hr) (Prod.fst x) 1
local notation "pointIdeal[" p "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ p)
local notation "high" => Finset.univ.filter (fun j ↦ β < 2 * (-(Prod.snd x) j))

local notation "decreasingPath[" L "," R "]" =>
  (∃ next : ℕ ×ₗ ℕ, Prod.fst (ofLex next) < 3 * Int.toNat β ∧
    ∃ C, Nonempty (SarkisovPath L C) ∧ HasPlaneTargetMarking C R next)

include hg hbir in
private theorem primary_decrease_of_smooth_fiber_pivots :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] := by
      rw [Fan.algebraicRealization_over, ← rankTwo]
      exact Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : IsIntegral Y := hT.isIntegral f[Φ]
    ∀ {A B : LogarithmicProjection i D}, A.fan = Φ → A.hom ≍ T.toBase →
      B.fan = plane[b',hi] → B.hom ≍ g ≫ (planeIso[b',hi]).inv →
      (Φ.boundaryIdeal hc.nonempty_cones).comap T.toBase = D * hT.ramificationIdealSheafToBase ℂ →
      (high).Nonempty →
      (∃ fiber : (↑high : Type) ↪ Fin 2, ∀ j : high,
        (∀ k < j.val, hT.baseCenter k ≠ hT.baseCenter j) ∧
        ∃ c : ℂˣ, hT.baseCenter j = center[r ((![1, 3] : Fin 2 → Fin 4) (fiber j)),c]) →
      decreasingPath[A,B] := by
  intro hcones hdim hOver hSmooth hIntegral A B hA hAh hB hBh hpole h hfiber
  let := hcones
  let := hdim
  let := hOver
  let := hSmooth
  let := hIntegral
  obtain ⟨L, C, p, hL, hLh, hresult⟩ :=
    hT.exists_sarkisov_path_decrease_of_quadric_high_fiber_centers b hΦ hc r hr g hg hbir
      hpole h hfiber
  have hStart : L = A := LogarithmicProjection.ext (hL.trans hA.symm) (hLh.trans hAh.symm)
  have targetHom {Z : Scheme} (e : Y ≅ Z) :
      B.hom ≍ e.hom ≫ (e.inv ≫ g) ≫ (planeIso[b',hi]).inv := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hBh
  rcases hresult with ⟨d, Z, l, U, hU, e, hC, hCh, hgo, hgb, -, -, hlt⟩ |
    ⟨Ω, hΩ, hcΩ, d, t, ht, Z, l, U, hU, e, hC, hCh, -, hgo, hgb, -, -, hlt⟩
  · refine ⟨_, ?_, C, ⟨hStart ▸ p⟩, .plane d b' _ hC hB U hU e (e.inv ≫ g)
      hCh (targetHom e) hgo hgb⟩
    simpa only [Prod.Lex.lt_iff, ofLex_planeSarkisovBidegree, ofLex_hirzebruchSarkisovBidegree,
      lt_self_iff_false, and_false, or_false] using hlt 0 0
  · subst Ω
    refine ⟨_, ?_, C, ⟨hStart ▸ p⟩, .hirzebruch d b' 0 _ t ht hB U hU e (e.inv ≫ g)
      (eq_of_heq hCh) (targetHom e) hgo hgb⟩
    simpa only [Nat.cast_zero, Prod.Lex.lt_iff, ofLex_hirzebruchSarkisovBidegree, lt_self_iff_false,
      and_false, or_false] using hlt 0 0

include hg hbir in
private theorem primary_decrease_of_mixed_fiber_pivots
    {j k : Fin n} (hjk : j ≠ k) (c : ℂˣ) (hj : hT.baseCenter j = center[r 1,c])
    (hjfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
    (σ : Φ.cones) (hσ : Nat.card (ToricRay σ.val) = 2)
    (hk : hT.baseCenter k = Φ.distinguishedPointHom σ pt)
    (hkfirst : ∀ l < k, hT.baseCenter l ≠ hT.baseCenter k) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] := by
      rw [Fan.algebraicRealization_over, ← rankTwo]
      exact Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : IsIntegral Y := hT.isIntegral f[Φ]
    ∀ {A B : LogarithmicProjection i D}, A.fan = Φ → A.hom ≍ T.toBase →
      B.fan = plane[b',hi] → B.hom ≍ g ≫ (planeIso[b',hi]).inv →
      β < 2 * (-x.2 j) → β < 2 * (-x.2 k) →
      (∀ l, l ≠ j → l ≠ k → 2 * (-x.2 l) ≤ β) →
      decreasingPath[A,B] := by
  intro hcones hdim hOver hSmooth hIntegral A B hA hAh hB hBh hjhigh hkhigh hsmall
  let := hcones
  let := hdim
  let := hOver
  let := hSmooth
  let := hIntegral
  have hn : 2 ≤ n := by
    have hd : 1 < Fintype.card (Fin n) := Fintype.one_lt_card_iff.mpr ⟨j, k, hjk⟩
    exact Nat.succ_le_of_lt (by simpa only [Fintype.card_fin] using hd)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨C, p, d, t, ht, Z, l, U, hU, e, hCh, -, hgo, hgb, -, hpos, hlt⟩ :=
    hT.exists_sarkisov_path_primary_decrease_of_prepared_quadric b hΦ hc r hr g hg hbir
      k j hjk.symm c hj hjfirst σ hσ hk hkfirst A hA hAh hkhigh hjhigh
      (fun l hlk hlj ↦ hsmall l hlj hlk)
  have targetHom : B.hom ≍ e.hom ≫ (e.inv ≫ g) ≫ (planeIso[b',hi]).inv := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hBh
  refine ⟨_, ?_, C, ⟨p⟩, .hirzebruch d b' 0 _ t ht hB U hU e (e.inv ≫ g)
    hCh targetHom hgo hgb⟩
  -- Compare just the primary coordinates, since preparation can change the total order.
  simp only [ofLex_hirzebruchSarkisovBidegree]
  exact Nat.mul_lt_mul_of_pos_left ((Int.toNat_lt_toNat (by omega)).mpr hlt) (by decide : 0 < 3)

-- Assign the two distinct high centers to the two fibers in the original frame.
private theorem exists_fiber_embedding_of_two_high_pivots
    [Nonempty Φ.cones] [SmoothOfRelativeDimension 2 f[Φ]] {j k : Fin n} {c a : ℂˣ}
    (hj : hT.baseCenter j = center[r 1,c]) (ha : hT.baseCenter k = center[r 3,a])
    (hjfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
    (hkfirst : ∀ l < k, hT.baseCenter l ≠ hT.baseCenter k)
    (heq : ∀ l : high, l.val ≠ j → l.val = k) :
    ∃ fiber : (↑high : Type) ↪ Fin 2, ∀ l : high,
      (∀ k < l.val, hT.baseCenter k ≠ hT.baseCenter l) ∧
      ∃ c : ℂˣ, hT.baseCenter l = center[r ((![1, 3] : Fin 2 → Fin 4) (fiber l)),c] := by
  classical
  let fiber : (↑high : Type) ↪ Fin 2 := ⟨fun l ↦ if l.val = j then 0 else 1, by
    intro l m h
    apply Subtype.ext
    by_cases hl : l.val = j <;> by_cases hm : m.val = j <;> simp [hl, hm] at h
    · exact hl.trans hm.symm
    · exact (heq l hl).trans (heq m hm).symm⟩
  refine ⟨fiber, fun l ↦ ?_⟩
  by_cases h : l.val = j
  · have hf : fiber l = 0 := ite_eq_left h
    rw [hf, h]
    exact ⟨hjfirst, c, hj⟩
  · have hf : fiber l = 1 := ite_eq_right h
    rw [hf, heq l h]
    exact ⟨hkfirst, a, ha⟩

include hg hbir in
/-- A quadric-to-plane resolution with a high order on the open orbit of the
retained fiber and low first orders on the two open section orbits admits
one of two continuations. Either there is a resolved path with strictly smaller
primary bidegree for the same prescribed plane target, or the opposite fiber
has a toric corner with both a high first order and a high infinitely near order.
Every high order other than the retained one then lies over that corner. After
extracting its first blowup, all the later high orders above the corner
project to a single point on the exceptional curve. The decrease compares against
any secondary degree of the original ruling. -/
theorem exists_sarkisov_path_primary_decrease_or_infinitely_near_high_corner
    (j : Fin n) (c : ℂˣ) (hj : hT.baseCenter j = center[r 1,c]) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] := by
      rw [Fan.algebraicRealization_over, ← rankTwo]
      exact Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : IsIntegral Y := hT.isIntegral f[Φ]
    ∀ (A B : LogarithmicProjection i D), A.fan = Φ → A.hom ≍ T.toBase →
      B.fan = plane[b',hi] → B.hom ≍ g ≫ (planeIso[b',hi]).inv →
      β < 2 * (-x.2 j) →
      (∀ (l : Fin n), (∀ k < l, hT.baseCenter k ≠ hT.baseCenter l) →
        ∀ (t : Fin 2) (a : ℂˣ), hT.baseCenter l = center[r ((![0, 2] : Fin 2 → Fin 4) t),a] →
          2 * (-x.2 l) ≤ β) →
      decreasingPath[A,B] ∨
      ∃ (σ : Φ.cones) (k l : Fin n), Nat.card (ToricRay σ.val) = 2 ∧
        (r 3).toCone ≤ σ ∧ hT.baseCenter k = Φ.distinguishedPointHom σ pt ∧
        hT.baseCenter l = hT.baseCenter k ∧ k < l ∧
        (∀ q < k, hT.baseCenter q ≠ hT.baseCenter k) ∧
        β < 2 * (-x.2 k) ∧ β < 2 * (-x.2 l) ∧
        (∀ q, q ≠ j → β < 2 * (-x.2 q) → hT.baseCenter q = hT.baseCenter k) ∧
        let I := pointIdeal[hT.baseCenter k]
        ∃ (m : ℕ) (W : Scheme) (U : BlowupTower I.blowup m W) (e : Y ≅ W)
          (hU : IsClosedPointTower I.blowup U) (tail : Fin m ↪o Fin n),
          Set.range tail = {q | q ≠ k} ∧
          e.hom ≫ U.toBase ≫ I.blowupToBase = T.toBase ∧
          pullback e.hom (pullback U.toBase I.blowupExceptionalClass) = T.exceptionalClass k ∧
          (∀ q, I.blowupToBase (hU.baseCenter q) = hT.baseCenter (tail q)) ∧
          (∀ q, pullback e.hom (U.exceptionalClass q) = T.exceptionalClass (tail q)) ∧
          (∃! p : I.blowup, I.blowupToBase p = hT.baseCenter k ∧
            ∀ q, hT.baseCenter (tail q) = hT.baseCenter k →
              β < 2 * (-x.2 (tail q)) → hU.baseCenter q = p) := by
  classical
  intro hcones hdim hOver hSmooth hIntegral A B hA hAh hB hBh hjhigh hlow
  let := hcones
  let := hdim
  let := hOver
  let := hSmooth
  let := hIntegral
  let : Φ.algebraicRealization.IsProjectiveOver ℂ := Φ.isProjectiveOver_quadric b hΦ hc r hr
  have hpole : (Φ.boundaryIdeal hc.nonempty_cones).comap T.toBase =
      D * hT.ramificationIdealSheafToBase ℂ := by
    rcases A with ⟨Ψ, hΨ, hcΨ, p, hp, hd, hpole⟩
    dsimp only at hA hAh
    subst Ψ
    obtain rfl : p = T.toBase := eq_of_heq hAh
    exact (hT.ramificationIdealSheafToBase_def ℂ).symm ▸ hpole
  have hlog := hpole.le.trans (mul_le_of_le_one_left' le_top)
  obtain ⟨j', hj', hjfirst, hjle⟩ := hT.exists_first_baseCenter_ge_of_plane_resolution g hg j
  have hjmem : hT.baseCenter j' ∈ (Φ.rayBoundaryIdeal hΦ (r 1)).support := by
    rw [hj', hj]
    exact ((r 1).binomialCenter_mem_support_sdiff_colon hΦ rankTwo
      (b.detDualEquiv_self _) ((r 1).surjective_detCharacter b) c).1
  have he : j = j' := hT.eq_of_high_base_orders_on_hirzebruch_fiber b 0 hΦ hc r hr g hg
    hlog 0 c hj hjmem hjhigh (by omega)
  subst j'
  have hcases := hT.high_base_orders_on_opposite_hirzebruch_fiber b 0 hΦ hc r hr g hg
    hlog hlow c j hj hjhigh
  have hh (l : high) : β < 2 * (-x.2 l) := (Finset.mem_filter.mp l.property).2
  have smooth := primary_decrease_of_smooth_fiber_pivots b hΦ hc r hr hT g hg hbir hA hAh
    hB hBh hpole ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjhigh⟩⟩
  rcases hcases with hsingle | ⟨k, hkj, hkhigh, hkfirst, hs, hcorner | hopen⟩
  · apply Or.inl (smooth ?_)
    refine ⟨⟨fun _ ↦ 0, fun l m _ ↦ Subtype.ext
      ((hsingle l (hh l)).trans (hsingle m (hh m)).symm)⟩, ?_⟩
    intro l
    obtain rfl : l.val = j := hsingle l (hh l)
    exact ⟨hjfirst, c, hj⟩
  · obtain ⟨σ, hσ, hpoint, hface⟩ := hcorner
    by_cases hex : ∃ l, l ≠ j ∧ l ≠ k ∧ β < 2 * (-x.2 l)
    · obtain ⟨l, hlj, hlk, hlhigh⟩ := hex
      have hl := hs l hlj hlhigh
      have hbound := hT.base_order_le_hirzebruch_fiber_degree b 0 hΦ r hr hc g hg k
      have hfocus := hT.exists_unique_high_base_center_on_first_exceptional g hg k hkfirst β
        hbound ⟨l, hlk, hl, hlhigh⟩
      exact Or.inr ⟨σ, k, l, hσ, hface, hpoint, hl,
        lt_of_le_of_ne (le_of_not_gt fun h ↦ hkfirst l h hl) hlk.symm, hkfirst, hkhigh, hlhigh,
        hs, hfocus⟩
    · exact Or.inl (primary_decrease_of_mixed_fiber_pivots b hΦ hc r hr hT g hg hbir
        hkj.symm c hj hjfirst σ hσ hpoint hkfirst hA hAh hB hBh hjhigh hkhigh
        (fun l hlj hlk ↦ le_of_not_gt fun hh ↦ hex ⟨l, hlj, hlk, hh⟩))
  · obtain ⟨a, ha, hother⟩ := hopen
    exact Or.inl (smooth (exists_fiber_embedding_of_two_high_pivots b hΦ r hr hT g hj ha
      hjfirst hkfirst (fun l hlj ↦ hother l hlj (hh l))))

end TauCeti.Toric.Fan.LogarithmicProjection
