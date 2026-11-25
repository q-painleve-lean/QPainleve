/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization.Iso
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.PositiveSection.HighFibers
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.PositiveSection.Selection

import QPainleve.Geometry.Toric.Fan.Hirzebruch.CoordinateBoundary
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective

/-!
# Initial marks for positive-section preparation

The source and target logarithmic projections determine the two pole factorizations on
the actual closed-point resolution of the plane map. These factorizations give a full
selection of positive pivots and identify the first centers to keep on the invariant fibers.
The remaining fiber coefficient and the orders of those centers satisfy the inequality
for the decreasing quadric exit in Case C of [Lutz, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "plane[" b "," hi "]" => Fan.projectiveSpace b hi
local notation "planeIso[" b "," hi "]" =>
  (Fan.projectivePlaneIso b hi ≪≫ Basis.polynomialProjIso (Pi.basisFun ℂ (Fin 3)))
local notation "rankTwo[" b "]" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "fiberRay[" r "," t "]" => r ((![1, 3] : Fin 2 → Fin 4) t)
local notation "coordPoint[" t "]" =>
  projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) t 0 (IsLocalRing.closedPoint ℂ : S)
local notation "center[" b "," ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ rankTwo[b] (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c (IsLocalRing.closedPoint ℂ)

private theorem prepared_order_bound_of_bidegree_lt {a β marks : ℤ} (hβ : 0 ≤ β)
    {r m : ℕ} (hr : r = 1 ∨ r = 2)
    (h : if r = 1 then planeSarkisovBidegree (a + β - marks).toNat m <
        hirzebruchSarkisovBidegree β.toNat m
      else hirzebruchSarkisovBidegree (a + β - marks).toNat m <
        hirzebruchSarkisovBidegree β.toNat m) :
    2 * (a - marks) < (2 - (r : ℤ)) * β := by
  rcases hr with rfl | rfl
  · simp only [ite_true, Prod.Lex.lt_iff, ofLex_planeSarkisovBidegree,
      ofLex_hirzebruchSarkisovBidegree, lt_irrefl, and_false, or_false] at h
    have hcast : (2 : ℤ) * ((a + β - marks).toNat : ℤ) < 3 * (β.toNat : ℤ) := by
      exact_mod_cast h
    omega
  · simp only [ite_eq_right (by decide : (2 : ℕ) ≠ 1), Prod.Lex.lt_iff,
      ofLex_hirzebruchSarkisovBidegree, lt_irrefl, and_false, or_false] at h
    have hcast : (3 : ℤ) * ((a + β - marks).toNat : ℤ) < 3 * (β.toNat : ℤ) := by
      exact_mod_cast h
    simp only [Nat.cast_ofNat, sub_self, zero_mul]
    omega

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X Y : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
  {D : X.IdealSheafData} {A B : LogarithmicProjection i D} {n e : ℕ}
  {b b' : Basis (Fin 2) ℤ N} {hi : IsIntegralLattice i}
  (r : Fin 4 ≃ A.fan.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])
  {T : BlowupTower A.fan.algebraicRealization n Y}
  (hT : IsClosedPointTower A.fan.algebraicRealization T) (g : Y ⟶ P)

local notation "f" => (A.fan.algebraicRealization ↘ S)
local notation "J" => A.fan.rayBoundaryIdeal A.isRegular (r 2)
local notation "C" => A.fan.hirzebruchPicardBasis b e A.isRegular r hr
local notation "q" =>
  Fan.characterRuling A.fan (LinearMap.toAddMonoidHom (b.coord 1))
    (Fan.nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)

/-- A marked logarithmic Hirzebruch-to-plane resolution whose high centers lie on
invariant fiber orbits has an initial selection filling all positive-section pivot
slots. Its retained centers are first over their base points, lie off the strict
section, and occupy distinct invariant fibers. The selected pivot orders and original
high orders satisfy the strict inequality for the prepared quadric exit. -/
theorem exists_positiveSection_selection_of_marked_high_fibers
    (hB : B.fan = plane[b',hi]) (k : X ≅ Y)
    (hAh : A.hom = k.hom ≫ T.toBase) (hBh : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv)
    (hg : g ≫ (P ↘ S) = T.toBase ≫ f) (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : SmoothOfRelativeDimension 2 f :=
      rankTwo[b] ▸ A.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap A.isRegular
    letI : Smooth f := SmoothOfRelativeDimension.smooth 2 f
    let : IsNoetherian A.fan.algebraicRealization := isNoetherian_of_finiteType f
    let x := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    let a := Basis.repr C x.1 0
    let β := Basis.repr C x.1 1
    let order := fun j : Fin n ↦ -x.2 j
    let high := Finset.univ.filter (fun j ↦ β < 2 * order j)
    let sectionCenters := hT.strictTransformCenterIndices J
    high.Nonempty →
    (∀ j ∈ high, ∃ t : Fin 2, ∃ c : ℂˣ, hT.baseCenter j = center[b,fiberRay[r,t],c]) →
    (high.card = 1 ∨ high.card = 2) ∧
      (∃ fiber : (↑high : Type) ↪ Fin 2, ∀ j : high,
        order j ≤ β ∧ (∀ l < (j : Fin n), hT.baseCenter l ≠ hT.baseCenter j) ∧
        q (hT.baseCenter j) = coordPoint[fiber j] ∧ (j : Fin n) ∉ sectionCenters) ∧
      ∃ selected : Finset (Fin n),
        IsPositiveSectionSelection (sectionCenters.filter (fun j ↦ 0 < order j)) order e selected ∧
        selected.card = e ∧
        2 * (a - (∑ j ∈ selected, order j) - (∑ j : high, order j)) <
          (2 - (Fintype.card (↑high : Type) : ℤ)) * β := by
  intro hSmoothA hNoetherianA x a β order high sectionCenters hhigh hcenters
  let := hSmoothA
  let : Smooth f := hSmoothA.smooth
  let := hNoetherianA
  let : Y.Over S := ⟨T.toBase ≫ f⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : g.IsOver S := ⟨hg⟩
  let : k.hom.IsOver S := ⟨(Category.assoc k.hom T.toBase f).symm.trans
    (hAh ▸ comp_over A.hom S)⟩
  let := Fan.projectivePlaneIso_trans_polynomialProjIso_hom_isOver b' hi (Pi.basisFun ℂ (Fin 3))
  let : SmoothOfRelativeDimension 2 ((plane[b',hi]).algebraicRealization ↘ S) := by
    let := (Fan.isComplete_projectiveSpace b' hi).nonempty_cones
    simpa only [rankTwo[b'], Fan.algebraicRealization_over] using
      (plane[b',hi]).smoothOfRelativeDimension_algebraicRealizationStructureMap
        (Fan.isRegular_projectiveSpace b' hi)
  let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have hsource := A.comap_boundaryIdeal_of_eq_iso_comp rankTwo[b] k A.isComplete T.toBase rfl
    (heq_of_eq hAh)
  rw [← hT.ramificationIdealSheafToBase_def ℂ] at hsource
  have htarget := B.comap_boundaryIdeal_of_eq_iso_comp rankTwo[b] k
    (Fan.isComplete_projectiveSpace b' hi) (g ≫ (planeIso[b',hi]).inv) hB hBh
  rw [ramificationIdealSheaf_comp ℂ g (planeIso[b',hi]).inv 2,
    ramificationIdealSheaf_eq_top_of_isOpenImmersion ℂ (planeIso[b',hi]).inv,
    comap_top, mul_top] at htarget
  obtain ⟨hsize, -, ⟨fiber, hmarks⟩, selected, hsub, hcard, hpriority, hlargest, -, hdrop⟩ :=
    hT.exists_positiveSection_preparation_of_high_fiber_centers b e A.isRegular A.isComplete r hr
      b' hi g hg hbir (D.comap k.inv) hsource htarget hhigh hcenters
  have hdisj :=
    hT.disjoint_sectionCenters_of_fiberCenters b A.isRegular A.isComplete r high hcenters
  have hcount : e ≤ (sectionCenters.filter (fun j ↦ 0 < order j)).card :=
    hcard ▸ Finset.card_le_card hsub
  refine ⟨hsize, ⟨fiber, ?_⟩, selected, ⟨hsub, hcard.trans (min_eq_left hcount).symm,
    fun j hj l hl ↦ hpriority j hj l (Finset.mem_filter.mp hl).1,
    fun j hj l hl ↦ hlargest j hj l (Finset.mem_filter.mp hl).1⟩, hcard, ?_⟩
  · intro j
    obtain ⟨hcap, hfirst, c, he⟩ := hmarks j
    refine ⟨hcap, hfirst, ?_, fun hj ↦ Finset.disjoint_left.mp hdisj hj j.property⟩
    apply (A.fan.mem_support_rayBoundaryIdeal_hirzebruch_coordinateFiber_iff b e A.isRegular
      r hr (fiber j) _).mp
    rw [he]
    exact ((fiberRay[r,fiber j]).binomialCenter_mem_support_rayBoundaryIdeal_iff A.isRegular
      rankTwo[b] (b.detDualEquiv_self _) ((fiberRay[r,fiber j]).surjective_detCharacter b)
      c (fiberRay[r,fiber j])).mpr rfl
  · let : A.fan.algebraicRealization.IsProjectiveOver ℂ :=
      A.fan.isProjectiveOver_algebraicRealization_of_isComplete A.isRegular A.isComplete b
    have hβ : 0 < β := (hT.hirzebruch_resolution_degree_bounds b e A.isRegular A.isComplete r hr
      g hg hbir).1
    simpa only [Finset.sum_coe_sort, Fintype.card_coe] using
      prepared_order_bound_of_bidegree_lt hβ.le hsize (hdrop order (fun _ _ ↦ le_rfl) _)

end TauCeti.Toric.Fan.LogarithmicProjection
