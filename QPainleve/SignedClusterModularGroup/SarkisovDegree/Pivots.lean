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
import QPainleve.Geometry.Toric.Fan.Picard.CurveIntersection

/-!
# High-order pivots of a logarithmic Hirzebruch resolution

A closed point tower resolving a logarithmic birational map to the plane can have
centers of order greater than half the ruling degree. A high-order corner or section
point gives a proper pivot for an elementary transformation. A high-order center
above the interior of an invariant fiber excludes every other high order over that
fiber, including over its corners. This separates the retained pivot from any
additional pivot after preparation to the quadric. These estimates are used in
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
local notation "p[" d "," ρ "," c "]" => Fan.Ray.binomialCenter ρ
  (Eq.trans (finrank_eq_card_basis d) (Fintype.card_fin 2))
  (Basis.detDualEquiv_self d (Fan.Ray.primitiveGenerator ρ))
  (Fan.Ray.surjective_detCharacter ρ d) c (IsLocalRing.closedPoint ℂ)
local notation "p[" ρ "," c "]" => p[b,ρ,c]
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

local notation "marking" =>
  LinearEquiv.symm (BlowupTower.picardMarking T hT f) (Additive.ofMul (pullback g H))

omit [Φ.algebraicRealization.IsProjectiveOver ℂ] in
include hg in
private theorem planeResolution_picardHom_isNef [Nonempty Φ.cones] [SmoothOfRelativeDimension 2 f] :
    (T.picardHom (marking)).toMul.IsNef ℂ (T.toBase ≫ f) := by
  let : Y.Over S := ⟨T.toBase ≫ f⟩
  let : g.IsOver S := ⟨hg⟩
  rw [← T.picardMarking_apply hT f, LinearEquiv.apply_symm_apply, toMul_ofMul]
  exact (isAmple_twistingSheaf ℂ (Fin 3 → ℂ) Nat.one_pos).isNef.pullback g

include hc hg in
/-- The sum of two base orders over distinct points of the same invariant fiber
is at most the fiber degree. The centers may be toric corners or infinitely near. -/
theorem add_base_orders_le_hirzebruch_fiber_degree
    [Nonempty Φ.cones] [SmoothOfRelativeDimension 2 f] [IsNoetherian X]
    (t : Fin 2) {j k : Fin n}
    (hj : hT.baseCenter j ∈ (Φ.rayBoundaryIdeal hΦ (fiberRay[t])).support)
    (hk : hT.baseCenter k ∈ (Φ.rayBoundaryIdeal hΦ (fiberRay[t])).support)
    (hne : hT.baseCenter j ≠ hT.baseCenter k) :
    -(marking).2 j + -(marking).2 k ≤ (C).repr (marking).1 1 := by
  classical
  obtain ⟨j', hj', hjfirst, hjle⟩ := hT.exists_first_baseCenter_ge_of_plane_resolution g hg j
  obtain ⟨k', hk', hkfirst, hkle⟩ := hT.exists_first_baseCenter_ge_of_plane_resolution g hg k
  have hne' : j' ≠ k' := fun h ↦ hne (hj'.symm.trans (h ▸ hk'))
  obtain ⟨_, J, -, -, -, -, -, horders⟩ := hT.exists_moving_base_ideal_of_plane_resolution g hg
  have hnef := planeResolution_picardHom_isNef hT g hg
  have hnef' : (T.picardHom ((marking).1, fun l ↦ -(baseMultiplicities J hT l : ℤ))).toMul.IsNef
      ℂ (T.toBase ≫ f) := by
    simpa only [← horders, neg_neg, Prod.mk.eta] using hnef
  have hbound := (fiberRay[t]).sum_first_base_orders_le_ray_degree b hΦ hT (marking).1
    (baseMultiplicities J hT) {j', k'} (by
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact ⟨hj' ▸ hj, hjfirst⟩
      · obtain rfl := Finset.mem_singleton.mp hl
        exact ⟨hk' ▸ hk, hkfirst⟩) hnef'
  rw [Finset.sum_pair hne', ← horders, ← horders] at hbound
  have hsum : -(marking).2 j' + -(marking).2 k' ≤ (C).repr (marking).1 1 := by
    simpa only [invariant_fiber_degree b e hΦ hc r hr (marking).1 t] using hbound
  exact (add_le_add hjle hkle).trans hsum

include hc hg in
/-- Two orders greater than half the ruling degree over the same invariant fiber
have the same projected center, including at corners and infinitely near centers. -/
theorem baseCenter_eq_of_high_base_orders_on_hirzebruch_fiber
    [Nonempty Φ.cones] [SmoothOfRelativeDimension 2 f] [IsNoetherian X]
    (t : Fin 2) {j k : Fin n}
    (hj : hT.baseCenter j ∈ (Φ.rayBoundaryIdeal hΦ (fiberRay[t])).support)
    (hk : hT.baseCenter k ∈ (Φ.rayBoundaryIdeal hΦ (fiberRay[t])).support)
    (hjhigh : (C).repr (marking).1 1 < 2 * (-(marking).2 j))
    (hkhigh : (C).repr (marking).1 1 < 2 * (-(marking).2 k)) :
    hT.baseCenter j = hT.baseCenter k := by
  by_contra hne
  have hbound := hT.add_base_orders_le_hirzebruch_fiber_degree b e hΦ hc r hr g hg t hj hk hne
  omega

include hg in
/-- In a logarithmic plane resolution, a high base order over the open orbit of an
invariant Hirzebruch fiber excludes every other high base order over that fiber.
The competing center may lie above an endpoint or be infinitely near. An order
is high when it exceeds half the degree on the ruling fiber. -/
theorem eq_of_high_base_orders_on_hirzebruch_fiber :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f :=
      d₂ ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let v := marking
    let β := (C).repr v.1 1
    (D).comap T.toBase ≤ hT.ramificationIdealSheafToBase ℂ →
    ∀ (t : Fin 2) (c : ℂˣ) {j k : Fin n},
      hT.baseCenter j = p[fiberRay[t],c] →
      hT.baseCenter k ∈ (Φ.rayBoundaryIdeal hΦ (fiberRay[t])).support →
      β < 2 * (-v.2 j) → β < 2 * (-v.2 k) → j = k := by
  classical
  intro hcones hdim hnoeth v β hlog t c j k hj hk hjhigh hkhigh
  let := hcones
  let := hdim
  let := hnoeth
  let ρ := fiberRay[t]
  have hjs : hT.baseCenter j ∈ (Φ.rayBoundaryIdeal hΦ ρ).support := by
    rw [hj]
    exact (ρ.binomialCenter_mem_support_sdiff_colon hΦ d₂
      (b.detDualEquiv_self ρ.primitiveGenerator) (ρ.surjective_detCharacter b) c).1
  have hp := hT.baseCenter_eq_of_high_base_orders_on_hirzebruch_fiber b e hΦ hc r hr g hg
    t hjs hk hjhigh hkhigh
  -- Above one open-orbit point the logarithmic bound counts both steps.
  by_contra hne
  obtain ⟨_, J, -, -, -, -, -, hv⟩ := hT.exists_moving_base_ideal_of_plane_resolution g hg
  have horders (l : Fin n) : -v.2 l = (baseMultiplicities J hT l : ℤ) := hv l
  have hm (l : Fin n) : 0 ≤ -v.2 l := by
    rw [horders l]
    exact Int.natCast_nonneg _
  have hnef := planeResolution_picardHom_isNef hT g hg
  have h := sum_base_orders_le_invariant_fiber b e hΦ hc r hr hT hlog
    v.1 (fun l ↦ -v.2 l) hm (by simpa only [Pi.neg_def, neg_neg, Prod.mk.eta] using hnef)
    t {j, k} (by
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact ⟨c, hj⟩
      · obtain rfl := Finset.mem_singleton.mp hl
        exact ⟨c, hp.symm.trans hj⟩)
  rw [Finset.sum_pair hne] at h
  omega

include hg in
/-- If there is a high base order in the interior of ray one's fiber and a
distinct high order over a toric corner, the corner is on ray three's fiber.
Both orders are measured in the same Hirzebruch ruling. -/
theorem opposite_hirzebruch_fiber_le_of_high_corner
    (σ : Φ.cones) (hσ : Nat.card (ToricRay σ.val) = 2) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f :=
      d₂ ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let v := marking
    let β := (C).repr v.1 1
    (D).comap T.toBase ≤ hT.ramificationIdealSheafToBase ℂ →
    ∀ (c : ℂˣ) {j k : Fin n}, hT.baseCenter j = p[r 1,c] →
      hT.baseCenter k = Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ) →
      β < 2 * (-v.2 j) → β < 2 * (-v.2 k) → k ≠ j → (r 3).toCone ≤ σ := by
  intro hcones hdim hnoeth v β hlog c j k hj hk hjhigh hkhigh hne
  obtain ⟨d, a, s, hcone, hs, hfiber, -⟩ :=
    Φ.exists_hirzebruch_corner_basis b e r hr hΦ hc σ hσ
  have hface : (s 1).toCone ≤ σ := by
    rw [(s 1).toCone_le_iff, hcone, congrFun hs (1 : Fin 4)]
    exact subset_hull ⟨1, rfl⟩
  rcases hfiber with he | he
  · have hmem := (Φ.distinguishedPoint_mem_support_rayBoundaryIdeal_iff hΦ σ (r 1)).mpr
      (he ▸ hface)
    exact (hne (hT.eq_of_high_base_orders_on_hirzebruch_fiber b e hΦ hc r hr g hg
      hlog 0 c hj (hk.symm ▸ hmem) hjhigh hkhigh).symm).elim
  · exact he ▸ hface

include hg in
/-- In a logarithmic plane resolution with a high-order center in the interior
of ray one's fiber, every other high-order center has a distinct projected
point. The first center over that point has at least the same order and lies on
an open section orbit, the open orbit of the opposite fiber, or a corner of the
opposite fiber. The corner case records the incidence needed for the mixed
quadric link. -/
theorem exists_first_high_baseCenter_of_high_base_order_on_hirzebruch_fiber :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f :=
      d₂ ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let v := marking
    let β := (C).repr v.1 1
    (D).comap T.toBase ≤ hT.ramificationIdealSheafToBase ℂ →
    ∀ (c : ℂˣ) {j k : Fin n}, hT.baseCenter j = p[r 1,c] →
      β < 2 * (-v.2 j) → β < 2 * (-v.2 k) → k ≠ j →
      ∃ l : Fin n, hT.baseCenter l = hT.baseCenter k ∧
        (∀ a < l, hT.baseCenter a ≠ hT.baseCenter l) ∧
        hT.baseCenter l ≠ hT.baseCenter j ∧ -v.2 k ≤ -v.2 l ∧
        ((∃ σ : Φ.cones, Nat.card (ToricRay σ.val) = 2 ∧
          hT.baseCenter l = Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ) ∧
          (r 3).toCone ≤ σ) ∨
        (∃ c' : ℂˣ, hT.baseCenter l = p[r 3,c']) ∨ Section[l]) := by
  intro hcones hdim hnoeth v β hlog c j k hj hjhigh hkhigh hne
  let := hcones
  let := hdim
  let := hnoeth
  obtain ⟨l, hl, hfirst, hle⟩ := hT.exists_first_baseCenter_ge_of_plane_resolution g hg k
  have hmem (a : ℂˣ) : p[r 1,a] ∈ (Φ.rayBoundaryIdeal hΦ (r 1)).support :=
    ((r 1).binomialCenter_mem_support_sdiff_colon hΦ d₂
      (b.detDualEquiv_self (r 1).primitiveGenerator) ((r 1).surjective_detCharacter b) a).1
  have havoid : hT.baseCenter l ∉ (Φ.rayBoundaryIdeal hΦ (r 1)).support := by
    intro h
    exact hne (hT.eq_of_high_base_orders_on_hirzebruch_fiber b e hΦ hc r hr g hg
      hlog 0 c hj (hl ▸ h) hjhigh hkhigh).symm
  refine ⟨l, hl, hfirst, fun h ↦ havoid ((h.trans hj).symm ▸ hmem c), hle, ?_⟩
  rcases baseCenter_hirzebruch_cases b hΦ hc r hT hlog l with hcorner | hsection | hfiber
  · obtain ⟨σ, ⟨hcard, hpoint⟩, -⟩ := hcorner
    exact Or.inl ⟨σ, hcard, hpoint.symm,
      hT.opposite_hirzebruch_fiber_le_of_high_corner b e hΦ hc r hr g hg σ hcard
        hlog c hj (hl.symm ▸ hpoint.symm) hjhigh hkhigh hne⟩
  · exact Or.inr (Or.inr hsection)
  · obtain ⟨t, c', h⟩ := hfiber
    fin_cases t
    · exact (havoid (h.symm ▸ hmem c')).elim
    · exact Or.inr (Or.inl ⟨c', h⟩)

include hg in
/-- When all high orders project to open orbits of invariant fibers, they occur
at first centers on distinct fibers and are bounded by the ruling degree. -/
theorem exists_fiber_embedding_of_hirzebruch_high_base_orders
    [Nonempty Φ.cones] [SmoothOfRelativeDimension 2 f] [IsNoetherian X]
    (hlog : (D).comap T.toBase ≤ hT.ramificationIdealSheafToBase ℂ) :
    let v := marking
    let A := Finset.univ.filter (fun j ↦ (C).repr v.1 1 < 2 * (-v.2 j))
    (∀ j ∈ A, ∃ t : Fin 2, ∃ c : ℂˣ, hT.baseCenter j = p[fiberRay[t],c]) →
    ∃ fiber : (↑A : Type) ↪ Fin 2, ∀ j : A,
      -v.2 j ≤ (C).repr v.1 1 ∧
      (∀ l < (j : Fin n), hT.baseCenter l ≠ hT.baseCenter j) ∧
      ∃ c : ℂˣ, hT.baseCenter j = p[fiberRay[fiber j],c] := by
  classical
  intro v A hcenters
  obtain ⟨_, J, -, -, -, -, -, horders⟩ := hT.exists_moving_base_ideal_of_plane_resolution g hg
  have hm (j : Fin n) : 0 ≤ -v.2 j := by
    rw [horders j]
    exact Int.natCast_nonneg _
  have hhigh (j : A) := (Finset.mem_filter.mp j.property).2
  choose t c hp using fun j : A ↦ hcenters j j.property
  have hnef : (T.picardHom (v.1, -(fun j ↦ -v.2 j))).toMul.IsNef ℂ (T.toBase ≫ f) := by
    simpa only [Pi.neg_def, neg_neg, Prod.mk.eta, v] using
      planeResolution_picardHom_isNef hT g hg
  have hbound := sum_base_orders_le_invariant_fiber b e hΦ hc r hr hT hlog
    v.1 (fun j ↦ -v.2 j) hm hnef
  have hunique {j l : A} {a : ℂˣ} (h : hT.baseCenter l = p[fiberRay[t j],a]) : j = l := by
    let ρ := fiberRay[t j]
    have hs : hT.baseCenter l ∈ (Φ.rayBoundaryIdeal hΦ ρ).support := h.symm ▸
      (ρ.binomialCenter_mem_support_sdiff_colon hΦ d₂
        (b.detDualEquiv_self ρ.primitiveGenerator) (ρ.surjective_detCharacter b) a).1
    exact Subtype.ext (hT.eq_of_high_base_orders_on_hirzebruch_fiber b e hΦ hc r hr g hg
      hlog (t j) (c j) (hp j) hs (hhigh j) (hhigh l))
  refine ⟨⟨t, fun j l h ↦ hunique (h.symm ▸ hp l)⟩, fun j ↦ ?_⟩
  have hle := hbound (t j) {j.val} (by
    intro k hk
    rw [Finset.mem_singleton.mp hk]
    exact ⟨c j, hp j⟩)
  refine ⟨by simpa only [Finset.sum_singleton] using hle, ?_, c j, hp j⟩
  obtain ⟨l, hl, hfirst, hle⟩ := hT.exists_first_baseCenter_ge_of_plane_resolution g hg j
  have hle' : -v.2 j ≤ -v.2 l := hle
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
above its projected point and has order at most the fiber degree. Either fiber
pivot can be marked as ray one for the preparation to the quadric, preserving
both the center and the Picard basis. -/
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
        (∃ c : ℂˣ, hT.baseCenter j = p[fiberRay[fiber j],c]) ∧
        ∃ (d : Basis (Fin 2) ℤ N) (s : Fin 4 ≃ Φ.Ray)
          (hs : (fun l ↦ (s l).primitiveGenerator) = ![d 0, d 1, -d 0, e • d 0 - d 1])
          (a : ℂˣ), s 1 = fiberRay[fiber j] ∧
          hT.baseCenter j = p[d,s 1,a] ∧ Fan.hirzebruchPicardBasis d e hΦ s hs = C := by
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
  obtain ⟨fiber, hfiber⟩ :=
    hT.exists_fiber_embedding_of_hirzebruch_high_base_orders b e hΦ hc r hr g hg hlog
      (fun j hj ↦ hcenter j (Finset.mem_filter.mp hj).2)
  have hcard : A.card ≤ 2 := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_embedding fiber
  have hpos := Finset.card_pos.mpr hA
  refine Or.inr ⟨by omega, fiber, fun j ↦ ?_⟩
  obtain ⟨hle, hfirst, c, hj⟩ := hfiber j
  obtain ⟨d, s, hs, -, h₁, hpic⟩ :=
    Fan.exists_hirzebruch_picardBasis_of_fiber b e r hr hΦ (fiber j)
  obtain ⟨a, ha⟩ := (s 1).exists_binomialCenter_eq_of_basis d b c
  refine ⟨hle, hfirst, ⟨c, hj⟩, d, s, hs, a, h₁, ?_, hpic⟩
  rw [hj, ← h₁, ← ha]

end QPainleve.BlowupTower.IsClosedPointTower
