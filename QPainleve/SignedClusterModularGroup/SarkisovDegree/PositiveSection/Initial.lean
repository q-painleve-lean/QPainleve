/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.StarFactorization
public import QPainleve.Geometry.Toric.Fan.Ruling.Basic
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.PositiveSection.HighFibers
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.PositiveSection.Selection

import QPainleve.Geometry.Toric.Fan.Hirzebruch.CoordinateBoundary

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

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of k₀)
local notation "P" => Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle k₀ (Fin 3 → k₀) 1)
local notation "plane[" b "," hi "]" => Fan.projectiveSpace b hi
local notation "planeIso[" b "," hi "]" =>
  (Fan.projectivePlaneIso k₀ b hi ≪≫ Basis.polynomialProjIso (Pi.basisFun k₀ (Fin 3)))
local notation "rankTwo[" b "]" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "fiberRay[" r "," t "]" => r ((![1, 3] : Fin 2 → Fin 4) t)
local notation "coordPoint[" t "]" =>
  projectiveLine.polynomialPoint k₀ (RingHom.id k₀) t 0 (IsLocalRing.closedPoint k₀ : S)
local notation "center[" b "," ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ k₀ rankTwo[b] (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c (IsLocalRing.closedPoint k₀)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X Y : Scheme} [X.Over (Spec (.of k₀))] [SmoothOfRelativeDimension 2 (X ↘ Spec
    (.of k₀))]
  {D : X.IdealSheafData} {A B : LogarithmicProjection k₀ i D} {n e : ℕ}
  {b b' : Basis (Fin 2) ℤ N} {hi : IsIntegralLattice i}
  (r : Fin 4 ≃ A.fan.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])
  {T : BlowupTower (A.fan.finiteFanScheme k₀) n Y}
  (hT : IsClosedPointTower (A.fan.finiteFanScheme k₀) T) (g : Y ⟶ (Proj (homogeneousSubmodule k₀
    (Fin 3 → k₀))))

local notation "f" => ((A.fan.finiteFanScheme k₀) ↘ S)
local notation "J" => A.fan.rayDivisorIdeal k₀ A.isRegular (r 2)
local notation "C" => A.fan.hirzebruchPicardBasis k₀ b e A.isRegular r hr
local notation "q" =>
  Fan.characterRuling k₀ A.fan (LinearMap.toAddMonoidHom (b.coord 1))
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
      rankTwo[b] ▸ A.fan.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ A.isRegular
    letI : Smooth f := SmoothOfRelativeDimension.smooth 2 f
    let : IsNoetherian (A.fan.finiteFanScheme k₀) := isNoetherian_of_finiteType f
    let x := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    let a := Basis.repr C x.1 0
    let β := Basis.repr C x.1 1
    let order := fun j : Fin n ↦ -x.2 j
    let high := Finset.univ.filter (fun j ↦ β < 2 * order j)
    let sectionCenters := hT.strictTransformCenterIndices J
    high.Nonempty →
    (∀ j ∈ high, ∃ t : Fin 2, ∃ c : k₀ˣ, hT.baseCenter j = center[b,fiberRay[r,t],c]) →
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
  let := Fan.projectivePlaneIso_trans_polynomialProjIso_hom_isOver k₀ b' hi (Pi.basisFun k₀ (Fin 3))
  let : SmoothOfRelativeDimension 2 ((Fan.finiteFanScheme k₀ (plane[b',hi])) ↘ S) := by
    let := (Fan.isComplete_projectiveSpace b' hi).nonempty_cones
    simpa only [rankTwo[b'], Fan.finiteFanScheme_over k₀] using
      (plane[b',hi]).smoothOfRelativeDimension_finiteFanSchemeToSpec k₀
        (Fan.isRegular_projectiveSpace b' hi)
  let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have hsource := A.comap_boundaryIdeal_of_eq_iso_comp rankTwo[b] k A.isComplete T.toBase rfl
    (heq_of_eq hAh)
  rw [← hT.ramificationIdealSheafToBase_def k₀] at hsource
  have htarget := B.comap_boundaryIdeal_of_eq_iso_comp rankTwo[b] k
    (Fan.isComplete_projectiveSpace b' hi) (g ≫ (planeIso[b',hi]).inv) hB hBh
  rw [ramificationIdealSheaf_comp k₀ g (planeIso[b',hi]).inv 2,
    ramificationIdealSheaf_eq_top_of_isOpenImmersion k₀ (planeIso[b',hi]).inv,
    comap_top, mul_top] at htarget
  obtain ⟨hsize, -, ⟨fiber, hmarks⟩, selected, hsub, hcard, hpriority, hlargest, -, hbound⟩ :=
    hT.exists_positiveSection_preparation_of_high_fiber_centers k₀ b e
      A.isRegular A.isComplete r hr
      b' hi g hg hbir (D.comap k.inv) hsource htarget hhigh hcenters
  have hdisj :=
    hT.disjoint_sectionCenters_of_fiberCenters k₀ b A.isRegular A.isComplete r high hcenters
  have hcount : e ≤ (sectionCenters.filter (fun j ↦ 0 < order j)).card :=
    hcard ▸ Finset.card_le_card hsub
  refine ⟨hsize, ⟨fiber, ?_⟩, selected, ⟨hsub, hcard.trans (min_eq_left hcount).symm,
    fun j hj l hl ↦ hpriority j hj l (Finset.mem_filter.mp hl).1,
    fun j hj l hl ↦ hlargest j hj l (Finset.mem_filter.mp hl).1⟩, hcard, ?_⟩
  · intro j
    obtain ⟨hcap, hfirst, c, he⟩ := hmarks j
    refine ⟨hcap, hfirst, ?_, fun hj ↦ Finset.disjoint_left.mp hdisj hj j.property⟩
    apply (A.fan.mem_support_rayBoundaryIdeal_hirzebruch_coordinateFiber_iff k₀ b e A.isRegular
      r hr (fiber j) _).mp
    rw [he]
    exact ((fiberRay[r,fiber j]).binomialCenter_mem_support_rayBoundaryIdeal_iff k₀ A.isRegular
      rankTwo[b] (b.detDualEquiv_self _) ((fiberRay[r,fiber j]).surjective_detCharacter b)
      c (fiberRay[r,fiber j])).mpr rfl
  · simpa only [Finset.sum_coe_sort, Fintype.card_coe] using (hbound order (fun _ _ ↦ le_rfl)).1

end TauCeti.Toric.Fan.LogarithmicProjection
