/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Homaloidal
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.Link

import QPainleve.SignedClusterModularGroup.SarkisovDegree.PositiveSection.Basic

/-!
# Positive-section preparation for a marked plane resolution

The Picard marking of a Hirzebruch-to-plane resolution gives the degrees and
multiplicities used to choose the positive-section centers. For one or two
marked high orders, the degree bound survives any transport that preserves or
increases those orders. The resulting comparison is in the lexicographic
bidegree used for induction on resolved Sarkisov paths.
-/

public section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra TauCeti.Toric

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

/-- Select positive-section pivots for a specified Hirzebruch-to-plane resolution.
The input is the set of stages on the strict positive section, with orders
summing to at least `a - 1`, where `a` is the fiber coefficient in the marking.
The one or two high orders are outside that set and are at most the fiber degree.

The selected stages have positive orders and take priority over every unselected
stage on the section, with ties going to the earlier stage. Subtract their orders
from `a` to obtain the prepared coefficient. The resulting inequality on the
sum of retained orders gives the hypothesis for the prepared quadric exit.
The degree formulas for the one-center plane link and the two-center quadric
link give a strictly smaller bidegree for any transported high orders at least
as large as the original ones. -/
theorem exists_positiveSection_pivots_with_bidegree_drop
    (hT : IsClosedPointTower X T) (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f)
    (hbir : Scheme.BirationalOver g (𝟙 P)) (sectionCenters : Finset (Fin n)) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f :=
      (by simpa using Module.finrank_eq_card_basis b : Module.finrank ℤ N = 2) ▸
        Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let v := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    let a := (C).repr v.1 0
    let d := (C).repr v.1 1
    let order : Fin n → ℤ := fun j ↦ -v.2 j
    let high := Finset.univ.filter (fun j ↦ d < 2 * order j)
    let positive := sectionCenters.filter (fun j ↦ 0 < order j)
    (high.card = 1 ∨ high.card = 2) →
    (∀ j ∈ high, order j ≤ d) →
    Disjoint sectionCenters high → (a - 1 ≤ ∑ j ∈ sectionCenters, order j) →
    ∃ top ⊆ positive, top.card = min e positive.card ∧
      (∀ i ∈ top, ∀ j ∈ sectionCenters, j < i → order i ≤ order j → j ∈ top) ∧
      (∀ i ∈ top, ∀ j ∈ sectionCenters, j ∉ top → order j ≤ order i) ∧
      ∀ μ : Fin n → ℤ, (∀ j ∈ high, order j ≤ μ j) →
        let remaining := a - (∑ j ∈ top, order j) - (∑ j ∈ high, μ j)
        2 * remaining < (2 - (high.card : ℤ)) * d ∧
          let degree := a - (∑ j ∈ top, order j) + d - (∑ j ∈ high, μ j)
          let old := hirzebruchSarkisovBidegree d.toNat (∑ j, order j).toNat
          ∀ M' : ℕ, if high.card = 1 then planeSarkisovBidegree degree.toNat M' < old
            else hirzebruchSarkisovBidegree degree.toNat M' < old := by
  intro hcones hdim hnoeth v a d order high positive hcard hcap hdisj hline
  let := hcones
  let := hdim
  let := hnoeth
  obtain ⟨hd, ha, hm⟩ := hT.hirzebruch_resolution_degree_bounds k₀ b e hΦ hc r hr g hg hbir
  obtain ⟨hsq, hsum⟩ :=
    hT.homaloidal_intersection_identities_of_hirzebruch k₀ b e hΦ hc r hr g hg hbir
  have hd' : 0 < d := hd
  have hm' (j : Fin n) : 0 ≤ order j := hm j
  have hmem (j : Fin n) : j ∈ high ↔ d < 2 * order j := by simp [high]
  have hp (j : Fin n) : j ∈ positive ↔ j ∈ sectionCenters ∧ 0 < order j :=
    Finset.mem_filter
  have hpositive : (∑ j ∈ positive, order j) = ∑ j ∈ sectionCenters, order j := by
    have he : positive = sectionCenters.filter (fun j ↦ order j ≠ 0) := by
      ext j
      rw [hp, Finset.mem_filter]
      simp only [lt_iff_le_and_ne, hm' j, true_and, ne_comm]
    rw [he, Finset.sum_filter_ne_zero]
  have hhigh : ∀ j ∈ high, d < 2 * order j ∧ order j ≤ d :=
    fun j hj ↦ ⟨(hmem j).mp hj, hcap j hj⟩
  have hnonempty : high.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨top, hsub, hsize, hclosed, hlargest, hdrop⟩ :=
    exists_preparation_with_degree_drop positive high order e (a := a) hd' ha hm' hhigh
      (fun j hj ↦ le_of_not_gt (fun h ↦ hj ((hmem j).mpr h)))
      (hdisj.mono_left (Finset.filter_subset ..)) hnonempty (hpositive.symm ▸ hline)
      (by simpa only [order, neg_sq] using hsq) hsum
  refine ⟨top, hsub, hsize, ?_, ?_, ?_⟩
  · intro i hi j hj hji horder
    exact hclosed i hi j ((hp j).mpr ⟨hj, ((hp i).mp (hsub hi)).2.trans_le horder⟩) hji horder
  · intro i hi j hj hj'
    by_cases hjpos : 0 < order j
    · exact hlargest i hi j ((hp j).mpr ⟨hj, hjpos⟩) hj'
    · exact (le_of_not_gt hjpos).trans (hm' i)
  intro μ hμ remaining
  have h := hdrop μ hμ
  refine ⟨h, ?_⟩
  intro degree old M'
  split_ifs with hone
  · rw [Prod.Lex.lt_iff, ofLex_planeSarkisovBidegree, ofLex_hirzebruchSarkisovBidegree]
    refine Or.inl ?_
    simp only [hone, Nat.cast_one] at h
    dsimp only [degree]
    omega
  · have htwo : high.card = 2 := hcard.resolve_left hone
    rw [Prod.Lex.lt_iff, ofLex_hirzebruchSarkisovBidegree, ofLex_hirzebruchSarkisovBidegree]
    refine Or.inl ?_
    simp only [htwo, Nat.cast_ofNat, sub_self, zero_mul] at h
    dsimp only [degree]
    omega

end QPainleve.BlowupTower.IsClosedPointTower
