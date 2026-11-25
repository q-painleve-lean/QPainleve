/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.SectionDegree
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.PositiveSection.Resolution

import QPainleve.Geometry.Toric.Fan.Boundary.PlanePivot
import QPainleve.Geometry.Toric.Fan.Hirzebruch.Corner
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Pivots
import QPainleve.SignedClusterModularGroup.SarkisovDegree.PositiveSection.Basic
import QPainleve.SignedClusterModularGroup.SarkisovDegree.PositiveSection.PivotCount

/-!
# Positive-section pivots when the high orders lie on open fibers

For a specified logarithmic resolution from a Hirzebruch surface to the
coordinate plane, the centers incident to the successive strict transforms of
the positive section determine the preparation. If the high orders occur over
the open orbits of invariant fibers, the same resolution supplies both the
section pivots and the degree bound for the ensuing plane or quadric link.
The fiber estimates use [Lutz, Proposition 8.7][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=70
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra TauCeti.Toric
open Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

attribute [local instance] MvPolynomial.gradedAlgebra

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (e : ℕ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])
  {Y : Scheme} {n : ℕ} {T : BlowupTower Φ.algebraicRealization n Y}
  (hT : IsClosedPointTower Φ.algebraicRealization T)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X" => Φ.algebraicRealization
local notation "f" => (X ↘ S)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "plane[" d "," h "]" => Fan.projectiveSpace d h
local notation "planeIso[" d "," h "]" =>
  (Fan.projectivePlaneIso d h ≪≫ Basis.polynomialProjIso (Pi.basisFun ℂ (Fin 3)))
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "B" => Fan.hirzebruchPicardBasis b e hΦ r hr
local notation "C" => Φ.rayBoundaryIdeal hΦ (r 2)
local notation "fiberRay[" t "]" => r ((![1, 3] : Fin 2 → Fin 4) t)
local notation "z" => (IsLocalRing.closedPoint ℂ : S)
local notation "center[" ρ "," c "]" => Fan.Ray.binomialCenter ρ rankTwo
  (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
  (Fan.Ray.surjective_detCharacter ρ b) c z

include hc in
/-- Centers over open invariant fiber orbits are disjoint from the stages on
the successive strict transforms of the marked positive section. -/
theorem disjoint_sectionCenters_of_fiberCenters
    [IsNoetherian X] [SmoothOfRelativeDimension 2 f] (J : Finset (Fin n))
    (hJ : ∀ j ∈ J, ∃ t : Fin 2, ∃ c : ℂˣ, hT.baseCenter j = center[fiberRay[t],c]) :
    Disjoint (hT.strictTransformCenterIndices C) J := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  refine Finset.disjoint_left.mpr fun {j} hj hk ↦ ?_
  have hsec := hT.baseCenter_mem_support_of_strictTransformCoefficients_ne_zero f
    (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ (r 2))
    ((hT.mem_strictTransformCenterIndices C j).mp hj)
  obtain ⟨t, c, hp⟩ := hJ j hk
  rw [hp] at hsec
  have he := ((fiberRay[t]).binomialCenter_mem_support_rayBoundaryIdeal_iff hΦ rankTwo
    (b.detDualEquiv_self _) ((fiberRay[t]).surjective_detCharacter b) c (r 2)).mp hsec
  have he' := r.injective he
  fin_cases t <;> contradiction

/-- Choose the positive-section pivots of a marked Hirzebruch-to-plane
resolution in the high-fiber case. The high centers lie first over their
points on one or two different invariant fibers. The Hirzebruch index is at
most one more than their number. Choose exactly that index many largest
positive orders on the successive strict transforms of the section, giving
earlier stages priority in a tie. When the index is positive, the earliest
maximal order is selected and gives a proper corner or smooth pivot. For a
corner the corresponding invariant fiber specifies the cone. The prepared
degree strictly decreases after
the one-center plane link or two-center quadric link if the transported high
orders are at least as large as the original ones. -/
theorem exists_positiveSection_preparation_of_high_fiber_centers
    (d : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f)
    (hbir : Scheme.BirationalOver g (𝟙 P)) (D : Y.IdealSheafData) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    letI : Smooth f := SmoothOfRelativeDimension.smooth 2 f
    let : IsNoetherian X := isNoetherian_of_finiteType f
    letI : Y.Over S := ⟨T.toBase ≫ f⟩
    letI : Smooth (Y ↘ S) := (hT.smoothOfRelativeDimension f).smooth
    letI : g.IsOver S := ⟨hg⟩
    (Φ.boundaryIdeal hc.nonempty_cones).comap T.toBase = D * hT.ramificationIdealSheafToBase ℂ →
    ((plane[d,hi]).boundaryIdeal (Fan.isComplete_projectiveSpace d hi).nonempty_cones).comap
      (g ≫ (planeIso[d,hi]).inv) = D * ramificationIdealSheaf ℂ g →
    let v := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    let a := (B).repr v.1 0
    let β := (B).repr v.1 1
    let order := fun j : Fin n ↦ -v.2 j
    let high := Finset.univ.filter (fun j ↦ β < 2 * order j)
    let sectionCenters := hT.strictTransformCenterIndices C
    let positive := sectionCenters.filter (fun j ↦ 0 < order j)
    high.Nonempty →
    (∀ j ∈ high, ∃ t : Fin 2, ∃ c : ℂˣ, hT.baseCenter j = center[fiberRay[t],c]) →
    (high.card = 1 ∨ high.card = 2) ∧ e ≤ high.card + 1 ∧
      (∃ fiber : (↑high : Type) ↪ Fin 2, ∀ j : high,
        order j ≤ β ∧ (∀ l < (j : Fin n), hT.baseCenter l ≠ hT.baseCenter j) ∧
        ∃ c : ℂˣ, hT.baseCenter j = center[fiberRay[fiber j],c]) ∧
      ∃ top ⊆ positive, top.card = e ∧
        (∀ j ∈ top, ∀ l ∈ sectionCenters, l < j → order j ≤ order l → l ∈ top) ∧
        (∀ j ∈ top, ∀ l ∈ sectionCenters, l ∉ top → order l ≤ order j) ∧
        (0 < e →
          ∃ j ∈ top, (∀ l ∈ sectionCenters, order l ≤ order j) ∧
            (∀ l ∈ sectionCenters, l < j → order l < order j) ∧
            (∀ l < j, hT.baseCenter l ≠ hT.baseCenter j) ∧
            ((∃ (σ : Φ.cones) (t : Fin 2), Nat.card (ToricRay σ.val) = 2 ∧ (r 2).toCone ≤ σ ∧
                σ.val = hull ℝ {i (-b 0), i (fiberRay[t]).primitiveGenerator} ∧
                Φ.distinguishedPointHom σ z = hT.baseCenter j) ∨
              ∃ c : ℂˣ, hT.baseCenter j = center[r 2,c])) ∧
        ∀ μ : Fin n → ℤ, (∀ j ∈ high, order j ≤ μ j) →
          let degree := a - (∑ j ∈ top, order j) + β - (∑ j ∈ high, μ j)
          let old := hirzebruchSarkisovBidegree β.toNat (∑ j, order j).toNat
          ∀ M' : ℕ, if high.card = 1 then planeSarkisovBidegree degree.toNat M' < old
            else hirzebruchSarkisovBidegree degree.toNat M' < old := by
  intro hcones hsmooth hnoeth hsource htarget v a β order high sectionCenters positive
    hnonempty hcenters
  let := hcones
  let := hsmooth
  let := hnoeth
  let : (X).IsProjectiveOver ℂ := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
  obtain ⟨fiber, hfiber⟩ :=
    hT.exists_fiber_embedding_of_hirzebruch_high_base_orders b e hΦ hc r hr g hg
      (hsource.trans_le fun _ ↦ Ideal.mul_le_right) hcenters
  have hcap (j) (hj : j ∈ high) : order j ≤ β := (hfiber ⟨j, hj⟩).1
  have hcard : high.card ≤ 2 := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_embedding fiber
  have hpos := Finset.card_pos.mpr hnonempty
  have hsize : high.card = 1 ∨ high.card = 2 := by omega
  have hline := hT.section_order_sum_of_hirzebruch_plane b e hΦ hc r hr d hi g hg hbir D
    hsource (by simpa only [← comap_comp] using htarget)
  obtain ⟨hβ, ha, hm⟩ := hT.hirzebruch_resolution_degree_bounds b e hΦ hc r hr g hg hbir
  obtain ⟨hsq, hsum⟩ :=
    hT.homaloidal_intersection_identities_of_hirzebruch b e hΦ hc r hr g hg hbir
  have hsq' : ∑ j, order j ^ 2 = 2 * a * β - (e : ℤ) * β ^ 2 - 1 := by
    simpa only [order, neg_sq] using hsq
  have hlow (j) (hj : j ∉ high) : 2 * order j ≤ β :=
    le_of_not_gt fun h ↦ hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hindex : e ≤ high.card + 1 :=
    hirzebruch_index_le_card_high_add_one high order e hβ ha hm
      (fun j hj ↦ ⟨(Finset.mem_filter.mp hj).2, hcap j hj⟩) hlow hsq' hsum
  have hdisj := disjoint_sectionCenters_of_fiberCenters b hΦ hc r hT high hcenters
  obtain ⟨j, hj⟩ := hnonempty
  have hcountPositive : 2 * e ≤ positive.card + 1 :=
    two_mul_index_le_card_positiveSection_add_one sectionCenters order e hβ ha (fun j _ ↦ hm j)
      (fun j hj ↦ hlow j (Finset.disjoint_left.mp hdisj hj))
      ⟨j, (Finset.mem_filter.mp hj).2⟩ hline.1 hsq'
  have heCard : e ≤ positive.card := by omega
  obtain ⟨top, hsub, hcount, hpriority, horder, hdrop⟩ :=
    hT.exists_positiveSection_pivots_with_bidegree_drop b e hΦ hc r hr g hg hbir
      sectionCenters hsize hcap hdisj hline.1
  rw [min_eq_left heCard] at hcount
  refine ⟨hsize, hindex, ⟨fiber, hfiber⟩, top, hsub, hcount, hpriority, horder, ?_, hdrop⟩
  intro he
  have hcoeff (j : Fin n) : j ∈ sectionCenters ↔ hT.strictTransformCoefficients C j ≠ 0 :=
    hT.mem_strictTransformCenterIndices C j
  obtain ⟨l, hl⟩ := Finset.card_pos.mp (hcount.symm ▸ he)
  obtain ⟨hlsec, hlpos⟩ := Finset.mem_filter.mp (hsub hl)
  obtain ⟨j, hj, -, hmax, hleast, hfirst, hp⟩ :=
    Fan.exists_first_max_base_order_on_ray b hΦ hc (r 2) hT g hg ⟨l, (hcoeff l).mp hlsec, hlpos⟩
  have hjsec := (hcoeff j).mpr hj
  have hmem : j ∈ top := by
    by_contra hj'
    have hle := horder l hl j hjsec hj'
    have hjl : j ≤ l := le_of_not_gt fun h ↦ (not_lt_of_ge hle) (hleast l h ((hcoeff l).mp hlsec))
    exact hj' (hpriority l hl j hjsec (lt_of_le_of_ne hjl fun h ↦ hj' (h.symm ▸ hl))
      (hmax l ((hcoeff l).mp hlsec)))
  refine ⟨j, hmem, fun l hl ↦ hmax l ((hcoeff l).mp hl),
    fun l hl hlj ↦ hleast l hlj ((hcoeff l).mp hl), hfirst, ?_⟩
  refine hp.imp (fun ⟨σ, hσ, hle, hp⟩ ↦ ?_) id
  obtain ⟨t, ht⟩ := Φ.exists_hirzebruch_corner_eq_hull_of_section_le b e r hr hΦ hc σ hσ 1 hle
  have ht' : σ.val = hull ℝ {i (r 2).primitiveGenerator, i (fiberRay[t]).primitiveGenerator} := ht
  have hgen : (r 2).primitiveGenerator = -b 0 := congrFun hr 2
  exact ⟨σ, t, hσ, hle, hgen ▸ ht', hp⟩

end QPainleve.BlowupTower.IsClosedPointTower
