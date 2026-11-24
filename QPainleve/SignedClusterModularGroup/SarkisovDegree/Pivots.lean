/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.PlaneResolution
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Centres
public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef.Pullback
import QPainleve.Geometry.Toric.Fan.Boundary.Node
import QPainleve.Geometry.Toric.Fan.Logarithmic.Multiplicity

/-!
# High-order pivots of a logarithmic Hirzebruch resolution

A closed point tower resolving a logarithmic birational map to the plane can have
centers of order greater than half the ruling degree. A high-order corner or section
point gives a proper pivot for an elementary transformation. In the remaining case
there is at most one high-order center above the interior of each invariant fiber,
and these centers are proper. This is the selection of the Hirzebruch cases in
Lutz's [Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=71
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry LineBundleClass Chow TauCeti.SymmetricAlgebra TauCeti.Toric
open Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X" => Φ.algebraicRealization
local notation "f" => (X ↘ S)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "C" => Fan.hirzebruchPicardBasis b e hΦ r hr
local notation "d₂" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "D" => Φ.boundaryIdeal hc.nonempty_cones
local notation "p[" ρ "," c "]" => Fan.Ray.binomialCenter ρ d₂
  (b.detDualEquiv_self (Fan.Ray.primitiveGenerator ρ))
  (Fan.Ray.surjective_detCharacter ρ b) c (IsLocalRing.closedPoint ℂ)
local notation "fiberRay[" t "]" => r ((![1, 3] : Fin 2 → Fin 4) t)

include hc in
open Classical in
private theorem invariant_fiber_degree [Nonempty Φ.cones] [SmoothOfRelativeDimension 2 f]
    (a : Additive (LineBundleClass X)) (t : Fin 2) :
    intersectionBilinForm ℂ X a ((Φ.rayDivisorToPicard hΦ) (Pi.single (fiberRay[t]) 1)) =
      (C).repr a 1 := by
  have hclass : (Φ.rayDivisorToPicard hΦ) (Pi.single (fiberRay[t]) 1) = C 0 := by
    fin_cases t
    · exact (Fan.hirzebruchPicardBasis_apply_zero b e hΦ r hr).symm
    · exact (Fan.hirzebruchPicardBasis_apply_zero_eq_ray_three b e hΦ r hr).symm
  rw [hclass, (Fan.hirzebruchPicardBasis_intersection_repr b e hΦ r hr hc a).1]

variable {Y : Scheme.{0}} {n : ℕ} {T : BlowupTower Φ.algebraicRealization n Y}
  (hT : IsClosedPointTower Φ.algebraicRealization T)

open Classical in
private theorem sum_base_orders_le_invariant_fiber
    [Nonempty Φ.cones] [SmoothOfRelativeDimension 2 f]
    (hlog : (D).comap T.toBase ≤ hT.ramificationIdealSheafToBase ℂ)
    (a : Additive (LineBundleClass X)) (m : Fin n → ℤ) (hm : ∀ j, 0 ≤ m j)
    (hnef : (T.picardHom (a, -m)).toMul.IsNef ℂ (T.toBase ≫ f))
    (t : Fin 2) (A : Finset (Fin n))
    (hA : ∀ j ∈ A, ∃ c : ℂˣ, hT.baseCenter j = p[fiberRay[t],c]) :
    ∑ j ∈ A, m j ≤ (C).repr a 1 := by
  have h := (fiberRay[t]).sum_base_orders_le_ray_degree b hΦ hc hT hlog a m A hm hnef hA
  rwa [invariant_fiber_degree b e hΦ hc r hr a t] at h

local notation "Corner[" j "]" => (∃! σ : Φ.cones, Nat.card (ToricRay σ.val) = 2 ∧
  Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ) = hT.baseCenter j)
local notation "Section[" j "]" =>
  (∃ t : Fin 2, ∃ c : ℂˣ, hT.baseCenter j = p[r ((![0, 2] : Fin 2 → Fin 4) t),c])

omit [Φ.algebraicRealization.IsProjectiveOver ℂ] in
include hΦ in
private theorem baseCenter_hirzebruch_cases
    [SmoothOfRelativeDimension 2 f]
    (hlog : (D).comap T.toBase ≤ hT.ramificationIdealSheafToBase ℂ) (j : Fin n) :
    Corner[j] ∨ Section[j] ∨ ∃ t : Fin 2, ∃ c : ℂˣ, hT.baseCenter j = p[fiberRay[t],c] := by
  rcases Φ.baseCenter_cases_of_totalTransform_le_ramification b hΦ hc hT hlog j with
    hcorner | ⟨_, a, ha, _⟩
  · exact Or.inl hcorner
  obtain ⟨k, hk⟩ := r.surjective a.1
  rw [Fan.Ray.map_internalCenter_subschemeι, Scheme.Hom.ker_eq_ker_fromSpecResidueField,
    Scheme.ker_fromSpecResidueField_inj] at ha
  have hp := ha.symm
  rw [← hk] at hp
  fin_cases k
  · exact Or.inr (Or.inl ⟨0, a.2, hp⟩)
  · exact Or.inr (Or.inr ⟨0, a.2, hp⟩)
  · exact Or.inr (Or.inl ⟨1, a.2, hp⟩)
  · exact Or.inr (Or.inr ⟨1, a.2, hp⟩)

variable (g : Y ⟶ Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ)))
  (hg : g ≫ (Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ)) ↘ Spec (.of ℂ)) =
    T.toBase ≫ (Φ.algebraicRealization ↘ Spec (.of ℂ)))

include hg in
private theorem hirzebruch_high_fiber_centers
    [Nonempty Φ.cones] [SmoothOfRelativeDimension 2 f] [IsNoetherian X]
    (hlog : (D).comap T.toBase ≤ hT.ramificationIdealSheafToBase ℂ)
    (v : Additive (LineBundleClass X) × (Fin n → ℤ))
    (hv : v = (T.picardMarking hT f).symm (Additive.ofMul (pullback g H)))
    (hm : ∀ j, 0 ≤ -v.2 j)
    (hcenters : ∀ j, (C).repr v.1 1 < 2 * (-v.2 j) →
      ∃ t : Fin 2, ∃ c : ℂˣ, hT.baseCenter j = p[fiberRay[t],c]) :
    let A := Finset.univ.filter (fun j ↦ (C).repr v.1 1 < 2 * (-v.2 j))
    ∃ fiber : (↑A : Type) ↪ Fin 2, ∀ j : A,
      -v.2 j ≤ (C).repr v.1 1 ∧
      (∀ l < (j : Fin n), hT.baseCenter l ≠ hT.baseCenter j) ∧
      ∃ c : ℂˣ, hT.baseCenter j = p[fiberRay[fiber j],c] := by
  classical
  intro A
  have hhigh (j : A) := (Finset.mem_filter.mp j.property).2
  choose t c hp using fun j : A ↦ hcenters j (hhigh j)
  let : Y.Over S := ⟨T.toBase ≫ f⟩
  have : g.IsOver S := ⟨hg⟩
  have hH : (H).IsAmple := isAmple_twistingSheaf ℂ (Fin 3 → ℂ) Nat.one_pos
  have hnef : (T.picardHom (v.1, -(fun j ↦ -v.2 j))).toMul.IsNef ℂ (T.toBase ≫ f) := by
    simp only [Pi.neg_def, neg_neg, Prod.mk.eta, hv, ← T.picardMarking_apply hT f,
      LinearEquiv.apply_symm_apply, toMul_ofMul]
    exact hH.isNef.pullback g
  have hbound := sum_base_orders_le_invariant_fiber b e hΦ hc r hr hT hlog
    v.1 (fun j ↦ -v.2 j) hm hnef
  have hunique {j l : A} {a : ℂˣ} (h : hT.baseCenter l = p[fiberRay[t j],a]) : j = l := by
    let ρ := fiberRay[t j]
    let F := Φ.rayBoundaryIdeal hΦ ρ
    let hF := Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ
    let : F.subscheme.IsProjectiveOver ℂ :=
      Scheme.IsProjectiveOver.of_isClosedImmersion ℂ F.subschemeι
    let : TauCeti.AlgebraicGeometry.IsRegular F.subscheme := Φ.isRegular_rayBoundary hΦ ρ
    let : F.subscheme.IsCurveOver ℂ := ρ.isCurveOver_boundaryComponent hΦ d₂
      (b.detDualEquiv_self ρ.primitiveGenerator) (ρ.surjective_detCharacter b)
    have hsupport (u : ℂˣ) := ρ.binomialCenter_mem_support_sdiff_colon hΦ d₂
      (b.detDualEquiv_self ρ.primitiveGenerator) (ρ.surjective_detCharacter b) u
    have hdegree := invariant_fiber_degree b e hΦ hc r hr v.1 (t j)
    have := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
    rw [intersectionBilinForm_apply, Fan.rayDivisorToPicard_single, one_zsmul, toMul_ofMul,
      primeDivisorClass_def,
      mk_toInvertibleSheaf_congr _ hF (Φ.rayBoundaryIdeal_def hΦ ρ).symm] at hdegree
    exact Subtype.ext (hT.eq_of_intersection_lt_two_mul_baseOrder_of_logarithmic_tower
      (Φ.isEffectiveCartier_boundaryIdeal hΦ hc d₂) hF (Φ.boundaryIdeal_le_rayBoundaryIdeal ρ hΦ)
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one ℂ) hlog v.1.toMul (fun k ↦ -v.2 k) hm hnef
      (by rw [hp j]; exact hsupport (c j)) (by rw [h]; exact hsupport a)
      (hdegree.symm ▸ hhigh j) (hdegree.symm ▸ hhigh l))
  refine ⟨⟨t, fun j l h ↦ hunique (h.symm ▸ hp l)⟩, fun j ↦ ?_⟩
  have hle := hbound (t j) {j.val} (by
    intro k hk
    rw [Finset.mem_singleton.mp hk]
    exact ⟨c j, hp j⟩)
  refine ⟨by simpa only [Finset.sum_singleton] using hle, ?_, c j, hp j⟩
  obtain ⟨l, hl, hfirst, hle⟩ := hT.exists_first_baseCenter_ge_of_plane_resolution g hg j
  have hle' : -v.2 j ≤ -v.2 l := by simpa only [hv] using hle
  have hlhigh : (C).repr v.1 1 < 2 * (-v.2 l) := lt_of_lt_of_le (hhigh j) (by omega)
  let l' : A := ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlhigh⟩⟩
  have he : j = l' := hunique (l := l') (hl.trans (hp j))
  exact (congrArg Subtype.val he).symm ▸ hfirst

include hg in
/-- If a logarithmic Hirzebruch resolution has an order greater than half the
fiber degree, a proper high-order center is available for a corner or section
link. A corner pivot also comes with a Hirzebruch basis spanning that corner and
with the same fiber degree. Otherwise, there are exactly one or two high-order
steps over the interiors of distinct invariant fibers. Each such step is the first
above its projected point and has order at most the fiber degree. -/
theorem hirzebruch_high_baseCenter_cases :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f :=
      d₂ ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let v := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    let A := Finset.univ.filter (fun j ↦ (C).repr v.1 1 < 2 * (-v.2 j))
    (D).comap T.toBase ≤ hT.ramificationIdealSheafToBase ℂ →
    A.Nonempty →
    (∃ j ∈ A, (∀ l < j, hT.baseCenter l ≠ hT.baseCenter j) ∧
      ((∃! σ : Φ.cones, Nat.card (ToricRay σ.val) = 2 ∧
        Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ) = hT.baseCenter j ∧
        ∃ (d : Basis (Fin 2) ℤ N) (e' : ℤ) (r' : Fin 4 ≃ Φ.Ray)
          (hr' : (fun l ↦ (r' l).primitiveGenerator) = ![d 0, d 1, -d 0, e' • d 0 - d 1]),
          σ.val = hull ℝ (Set.range (i ∘ d)) ∧
          (Φ.hirzebruchPicardBasis d e' hΦ r' hr').repr v.1 1 = (C).repr v.1 1) ∨ Section[j])) ∨
      (A.card = 1 ∨ A.card = 2) ∧ ∃ fiber : (↑A : Type) ↪ Fin 2, ∀ j : A,
        -v.2 j ≤ (C).repr v.1 1 ∧
        (∀ l < (j : Fin n), hT.baseCenter l ≠ hT.baseCenter j) ∧
        ∃ c : ℂˣ, hT.baseCenter j = p[fiberRay[fiber j],c] := by
  classical
  intro hcones hdim hnoeth v A hlog hA
  let := hcones
  let := hdim
  let := hnoeth
  by_cases hshort : ∃ j ∈ A, (∀ l < j, hT.baseCenter l ≠ hT.baseCenter j) ∧ (Corner[j] ∨ Section[j])
  · obtain ⟨j, hj, hfirst, hcorner | hsection⟩ := hshort
    · refine Or.inl ⟨j, hj, hfirst, Or.inl ?_⟩
      obtain ⟨σ, ⟨hcard, hpoint⟩, huniq⟩ := hcorner
      obtain ⟨d, e', r', hr', _, hcone, _, _, hrepr⟩ :=
        Φ.exists_hirzebruch_corner_picardBasis b e hΦ r hr hc σ hcard
      exact ⟨σ, ⟨hcard, hpoint, d, e', r', hr', hcone, (hrepr v.1).2⟩,
        fun τ hτ ↦ huniq τ ⟨hτ.1, hτ.2.1⟩⟩
    · exact Or.inl ⟨j, hj, hfirst, Or.inr hsection⟩
  have hcenter (j : Fin n) (hj : (C).repr v.1 1 < 2 * (-v.2 j)) :
      ∃ t : Fin 2, ∃ c : ℂˣ, hT.baseCenter j = p[fiberRay[t],c] := by
    obtain ⟨l, hl, hfirst, hle⟩ := hT.exists_first_baseCenter_ge_of_plane_resolution g hg j
    have hle' : -v.2 j ≤ -v.2 l := hle
    have hl' : l ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_of_lt_of_le hj (by omega)⟩
    rcases baseCenter_hirzebruch_cases b hΦ hc r hT hlog l with hc | hs | hf
    · exact (hshort ⟨l, hl', hfirst, Or.inl hc⟩).elim
    · exact (hshort ⟨l, hl', hfirst, Or.inr hs⟩).elim
    · simpa only [hl] using hf
  obtain ⟨_, _, -, -, -, -, -, horders⟩ := hT.exists_moving_base_ideal_of_plane_resolution g hg
  have hm (j : Fin n) : 0 ≤ -v.2 j := by
    rw [horders j]
    exact Int.natCast_nonneg _
  obtain ⟨fiber, hfiber⟩ :=
    hirzebruch_high_fiber_centers b e hΦ hc r hr hT g hg hlog v rfl hm hcenter
  have hcard : A.card ≤ 2 := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_embedding fiber
  have hpos := Finset.card_pos.mpr hA
  exact Or.inr ⟨by omega, fiber, hfiber⟩

end QPainleve.BlowupTower.IsClosedPointTower
