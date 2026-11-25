/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Incidence
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Picard
public import QPainleve.Geometry.Toric.Fan.Boundary.PlanePivot
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Plane
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.PositiveSection.Selection

import QPainleve.Geometry.Toric.Fan.Hirzebruch.Corner

/-!
# Iterating marked positive-section pivots

On an identified resolving surface, successive positive-section pivots keep the
same map to the target plane. The remaining selected orders, the two ruling
coordinates, and the retained first centers track the prescribed plane resolution
through the descent. At index zero the resulting preparation records the
transverse degree and the orders needed for the quadric exit.

The descent by elementary transformations develops Case C of
[Lutz, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone
open QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra

namespace TauCeti.Toric.Fan.LogarithmicProjection

open scoped Sarkisov

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "planeIso[" b "," hi "]" =>
  (Fan.projectivePlaneIso b hi ≪≫ Basis.polynomialProjIso (Pi.basisFun ℂ (Fin 3)))
local notation "f[" A "]" => (Fan.algebraicRealization (LogarithmicProjection.fan A) ↘ S)
local notation "rankTwo[" b "]" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "pt" => (IsLocalRing.closedPoint ℂ : S)
local notation "coordPoint[" j "]" => projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) j 0
local notation "fiberRay[" r "," j "]" => r ((![1, 3] : Fin 2 → Fin 4) j)
local notation "center[" b "," ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ rankTwo[b] (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c pt

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
  {D : X.IdealSheafData}

/-- A Hirzebruch marking on a closed-point tower resolving the two specified
projections. The top isomorphism records how the tower realizes those projections
on the common surface. -/
structure HirzebruchPlaneResolution (A B : LogarithmicProjection i D)
    (b' : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i) (e n : ℕ) where
  /-- Lattice frame of the current Hirzebruch surface. -/
  basis : Basis (Fin 2) ℤ N
  /-- Rays in Hirzebruch order. -/
  rays : Fin 4 ≃ A.fan.Ray
  /-- The ray generators in this frame. -/
  rays_eq : (fun j ↦ (rays j).primitiveGenerator) =
    ![basis 0, basis 1, -basis 0, (e : ℤ) • basis 0 - basis 1]
  /-- The target is the plane in the prescribed frame. -/
  target_fan : B.fan = Fan.projectiveSpace b' hi
  /-- Top of the tower. -/
  top : Scheme
  /-- The ordered tower over the current source fan. -/
  tower : BlowupTower A.fan.algebraicRealization n top
  /-- Each center is a closed point. -/
  closed : IsClosedPointTower A.fan.algebraicRealization tower
  /-- Identification of the common surface with the top of the tower. -/
  iso : X ≅ top
  /-- The plane map in the tower coordinates. -/
  planeMap : top ⟶ P
  /-- The tower presents the specified source projection. -/
  source_hom : A.hom = iso.hom ≫ tower.toBase
  /-- The plane map presents the specified target projection. -/
  target_hom : B.hom ≍ iso.hom ≫ planeMap ≫ (planeIso[b',hi]).inv
  /-- The plane map is over the base field. -/
  planeMap_over : planeMap ≫ (P ↘ S) = tower.toBase ≫ f[A]
  /-- The plane map is birational. -/
  planeMap_birational : Scheme.BirationalOver planeMap (𝟙 P)

namespace HirzebruchPlaneResolution

variable {A B : LogarithmicProjection i D} {b' : Basis (Fin 2) ℤ N}
  {hi : IsIntegralLattice i} {e n : ℕ} (M : HirzebruchPlaneResolution A B b' hi e n)

include M in
private theorem smooth : SmoothOfRelativeDimension 2 f[A] :=
  rankTwo[M.basis] ▸ A.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap A.isRegular

include M in
private theorem noetherian : IsNoetherian A.fan.algebraicRealization :=
  let : SmoothOfRelativeDimension 2 f[A] := M.smooth
  let : Smooth f[A] := SmoothOfRelativeDimension.smooth 2 _
  isNoetherian_of_finiteType f[A]

/-- Coordinates of the pullback of the plane line class in the tower marking. -/
def lineClass :
    Additive (LineBundleClass A.fan.algebraicRealization) × (Fin n → ℤ) :=
  let : SmoothOfRelativeDimension 2 f[A] := M.smooth
  let : IsNoetherian A.fan.algebraicRealization := M.noetherian
  (M.tower.picardMarking M.closed f[A]).symm (Additive.ofMul (pullback M.planeMap H))

/-- The tower coordinates are computed by the inverse Picard marking. -/
theorem lineClass_def [SmoothOfRelativeDimension 2 f[A]]
    [IsNoetherian A.fan.algebraicRealization] :
    M.lineClass =
      (M.tower.picardMarking M.closed f[A]).symm (Additive.ofMul (pullback M.planeMap H)) := (rfl)

/-- The fiber coefficient of the plane line class in the Hirzebruch basis. -/
def fiberCoefficient : ℤ :=
  let : Nonempty A.fan.cones := A.isComplete.nonempty_cones
  (A.fan.hirzebruchPicardBasis M.basis e A.isRegular M.rays M.rays_eq).repr M.lineClass.1 0

/-- The degree of the plane line class on a ruling fiber. -/
def fiberDegree : ℤ :=
  let : Nonempty A.fan.cones := A.isComplete.nonempty_cones
  (A.fan.hirzebruchPicardBasis M.basis e A.isRegular M.rays M.rays_eq).repr M.lineClass.1 1

/-- The fiber coefficient is the first Hirzebruch coordinate. -/
theorem fiberCoefficient_def :
    let : Nonempty A.fan.cones := A.isComplete.nonempty_cones
    M.fiberCoefficient =
      (A.fan.hirzebruchPicardBasis M.basis e A.isRegular M.rays M.rays_eq).repr M.lineClass.1 0 :=
  (rfl)

/-- The fiber degree is the second Hirzebruch coordinate. -/
theorem fiberDegree_def :
    let : Nonempty A.fan.cones := A.isComplete.nonempty_cones
    M.fiberDegree =
      (A.fan.hirzebruchPicardBasis M.basis e A.isRegular M.rays M.rays_eq).repr M.lineClass.1 1 :=
  (rfl)

/-- The order of the plane linear system at a stage of the resolving tower. -/
def order (j : Fin n) : ℤ := -M.lineClass.2 j

/-- The base order is the negative of the total-transform exceptional coefficient. -/
theorem order_def (j : Fin n) : M.order j = -M.lineClass.2 j := (rfl)

/-- The stages centered on the successive strict transforms of the positive
section. At index zero, the marking still specifies this section by its ray. -/
def sectionCenters : Finset (Fin n) :=
  let : Nonempty A.fan.cones := A.isComplete.nonempty_cones
  M.closed.strictTransformCenterIndices (A.fan.rayBoundaryIdeal A.isRegular (M.rays 2))

/-- A stage lies on the marked section exactly when it lies on its strict
transform at that stage of the tower. -/
theorem sectionCenters_def :
    let : Nonempty A.fan.cones := A.isComplete.nonempty_cones
    M.sectionCenters =
      M.closed.strictTransformCenterIndices (A.fan.rayBoundaryIdeal A.isRegular (M.rays 2)) :=
  (rfl)

/-- The strictly positive orders among the stages on the marked section. -/
def positiveCenters : Finset (Fin n) := M.sectionCenters.filter (fun j ↦ 0 < M.order j)

/-- The selected candidates are the section stages with strictly positive order. -/
@[simp]
theorem mem_positiveCenters (j : Fin n) :
    j ∈ M.positiveCenters ↔ j ∈ M.sectionCenters ∧ 0 < M.order j := Finset.mem_filter

/-- The invariant ruling of the marked Hirzebruch surface. -/
def ruling : A.fan.algebraicRealization ⟶ projectiveLine ℂ :=
  A.fan.characterRuling (M.basis.coord 1).toAddMonoidHom
    (Fan.nonneg_or_nonpos_hirzebruch_ruling_character M.basis e M.rays M.rays_eq)

/-- The ruling is induced by the second coordinate in the lattice frame. -/
theorem ruling_def :
    M.ruling = A.fan.characterRuling (M.basis.coord 1).toAddMonoidHom
      (Fan.nonneg_or_nonpos_hirzebruch_ruling_character M.basis e M.rays M.rays_eq) := (rfl)

/-- An earliest maximal positive order is attained at a first proper center on
the marked section. It lies at a corner on one of the invariant fibers or in
the section's open orbit. -/
theorem exists_first_max_of_positiveCenters_nonempty (h : M.positiveCenters.Nonempty) :
    ∃ j ∈ M.positiveCenters,
      (∀ l ∈ M.positiveCenters, M.order l ≤ M.order j) ∧
      (∀ l ∈ M.positiveCenters, l < j → M.order l < M.order j) ∧
      (∀ l < j, M.closed.baseCenter l ≠ M.closed.baseCenter j) ∧
      ((∃ (σ : A.fan.cones) (t : Fin 2),
        Nat.card (ToricRay σ.val) = 2 ∧ (M.rays 2).toCone ≤ σ ∧
        σ.val = hull ℝ {i (-M.basis 0), i (fiberRay[M.rays,t]).primitiveGenerator} ∧
        A.fan.distinguishedPointHom σ pt = M.closed.baseCenter j) ∨
        ∃ c : ℂˣ, M.closed.baseCenter j = center[M.basis,M.rays 2,c]) := by
  let : Nonempty A.fan.cones := A.isComplete.nonempty_cones
  let : SmoothOfRelativeDimension 2 f[A] := M.smooth
  let : IsNoetherian A.fan.algebraicRealization := M.noetherian
  let C := A.fan.rayBoundaryIdeal A.isRegular (M.rays 2)
  have hmem (l : Fin n) : l ∈ M.positiveCenters ↔
      M.closed.strictTransformCoefficients C l ≠ 0 ∧ 0 < M.order l := by
    rw [mem_positiveCenters, sectionCenters_def, M.closed.mem_strictTransformCenterIndices]
  obtain ⟨l, hl⟩ := h
  obtain ⟨j, hj, hjpos, hmax, hearly, hfirst, hcase⟩ :=
    A.fan.exists_first_max_base_order_on_ray M.basis A.isRegular A.isComplete
      (M.rays 2) M.closed M.planeMap M.planeMap_over ⟨l, (hmem l).mp hl⟩
  refine ⟨j, (hmem j).mpr ⟨hj, hjpos⟩, fun l hl ↦ hmax l ((hmem l).mp hl).1,
    fun l hl hlj ↦ hearly l hlj ((hmem l).mp hl).1, hfirst, ?_⟩
  refine hcase.imp (fun ⟨σ, hσ, hsec, hp⟩ ↦ ?_) id
  obtain ⟨t, ht⟩ :=
    A.fan.exists_hirzebruch_corner_eq_hull_of_section_le M.basis e M.rays M.rays_eq
      A.isRegular A.isComplete σ hσ 1 hsec
  have hgen : (M.rays 2).primitiveGenerator = -M.basis 0 := congrFun M.rays_eq 2
  exact ⟨σ, t, hσ, hsec, hgen ▸ ht, hp⟩

end HirzebruchPlaneResolution

/-- The marks carried through positive-section preparation. The selected set
fills the remaining pivot slots, and each retained center is first over its
point on its own invariant fiber, off the marked section. -/
structure PositiveSectionMarking {A B : LogarithmicProjection i D} {b' : Basis (Fin 2) ℤ N}
    {hi : IsIntegralLattice i} {e n : ℕ}
    (M : HirzebruchPlaneResolution A B b' hi e n) (ι : Type*) where
  /-- The remaining selected positive-section stages. -/
  selected : Finset (Fin n)
  /-- They are the largest positive section orders, with earlier stages first in ties. -/
  selection : IsPositiveSectionSelection M.positiveCenters M.order e selected
  /-- Every remaining slot has a positive pivot. -/
  card_selected : selected.card = e
  /-- The invariant fiber of each retained mark. -/
  fiber : ι ↪ Fin 2
  /-- The stage of each retained mark in the current tower. -/
  index : ι → Fin n
  /-- A marked stage is the first one over its point. -/
  first : ∀ a, ∀ l < index a, M.closed.baseCenter l ≠ M.closed.baseCenter (index a)
  /-- The value of the ruling on the retained point in the current frame. -/
  ruling_eq : ∀ a, M.ruling (M.closed.baseCenter (index a)) = coordPoint[fiber a] pt
  /-- The retained point is off the marked section in the tower. -/
  off_section : ∀ a, index a ∉ M.sectionCenters

namespace PositiveSectionMarking

variable {A B : LogarithmicProjection i D} {b' : Basis (Fin 2) ℤ N}
  {hi : IsIntegralLattice i} {e n : ℕ} {ι : Type*}
  {M : HirzebruchPlaneResolution A B b' hi e n}

/-- The fiber coefficient left after the remaining selected pivots. -/
def remainingCoefficient (s : PositiveSectionMarking M ι) : ℤ :=
  M.fiberCoefficient - ∑ j ∈ s.selected, M.order j

/-- The remaining coefficient subtracts exactly the orders in the current selection. -/
theorem remainingCoefficient_def (s : PositiveSectionMarking M ι) :
    s.remainingCoefficient = M.fiberCoefficient - ∑ j ∈ s.selected, M.order j := (rfl)

/-- At index zero no selected pivot contributes to the remaining coefficient. -/
@[simp]
theorem remainingCoefficient_zero {M : HirzebruchPlaneResolution A B b' hi 0 n}
    (s : PositiveSectionMarking M ι) : s.remainingCoefficient = M.fiberCoefficient := by
  rw [remainingCoefficient, Finset.card_eq_zero.mp s.card_selected, Finset.sum_empty, sub_zero]

/-- Transport the selected stages through a resolved pivot. The reverse center
contributes no positive section order, and the retained section stages
keep their orders and incidence. The remaining coefficient is invariant, and
the transported marking records the specified retained first centers. -/
private theorem exists_of_pivot {C : LogarithmicProjection i D}
    {M : HirzebruchPlaneResolution A B b' hi (e + 1) (n + 1)}
    (s : PositiveSectionMarking M ι) {M' : HirzebruchPlaneResolution C B b' hi e (1 + n)}
    (j : Fin (n + 1)) (hj : j ∈ M.positiveCenters)
    (hmax : ∀ l ∈ M.positiveCenters, M.order l ≤ M.order j)
    (hearly : ∀ l ∈ M.positiveCenters, l < j → M.order l < M.order j)
    (hhead : Fin.castAdd n (0 : Fin 1) ∉ M'.positiveCenters)
    (hsection : ∀ l : Fin n, l.natAdd 1 ∈ M'.sectionCenters ↔ j.succAbove l ∈ M.sectionCenters)
    (horder : ∀ l : Fin n, j.succAbove l ∈ M.sectionCenters →
      M'.order (l.natAdd 1) = M.order (j.succAbove l))
    (hcoef : M'.fiberCoefficient = M.fiberCoefficient - M.order j)
    (fiber : ι ↪ Fin 2) (index : ι → Fin (1 + n))
    (hfirst : ∀ a, ∀ l < index a, M'.closed.baseCenter l ≠ M'.closed.baseCenter (index a))
    (hvalue : ∀ a, M'.ruling (M'.closed.baseCenter (index a)) = coordPoint[fiber a] pt)
    (hoff : ∀ a, index a ∉ M'.sectionCenters) :
    ∃ s' : PositiveSectionMarking M' ι, s'.index = index ∧
      s'.remainingCoefficient = s.remainingCoefficient := by
  have hstages (l : Fin n) :
      l.natAdd 1 ∈ M'.positiveCenters ↔ j.succAbove l ∈ M.positiveCenters := by
    simp only [HirzebruchPlaneResolution.mem_positiveCenters, hsection]
    exact and_congr_right (fun hl ↦ by rw [horder l hl])
  obtain ⟨selected, hs, -, hsum⟩ := s.selection.of_pivot hj hmax hearly hhead hstages
    (fun l hl ↦ horder l ((M.mem_positiveCenters _).mp hl).1)
  have hcard : selected.card = e := by
    rw [hs.card_eq, min_eq_left]
    have hsub := s.selection.subset
    have hp := s.selection.mem_of_earliest_max hj hmax hearly
    have hle : (s.selected.erase j).card ≤ M'.positiveCenters.card := by
      refine Finset.card_le_card_of_surjOn (Fin.addCases (fun _ : Fin 1 ↦ j) j.succAbove) ?_
      intro l hl
      obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
      obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq_iff.mpr hne
      exact ⟨t.natAdd 1, (hstages t).mpr (hsub hl), Fin.addCases_right ..⟩
    rwa [Finset.card_erase_of_mem hp, s.card_selected, Nat.add_sub_cancel] at hle
  refine ⟨⟨selected, hs, hcard, fiber, index, hfirst, hvalue, hoff⟩, rfl, ?_⟩
  rw [remainingCoefficient, hcoef, hsum, remainingCoefficient]

end PositiveSectionMarking

/-- Compose the resolved positive-section pivots on the common surface from
the single-pivot comparisons of the towers. The earliest maximal proper
center is chosen at each positive index. The resulting quadric keeps the
ruling degree and reaches the prepared fiber coefficient. Each original
mark is still first over its point and has at least its initial order. -/
theorem exists_marked_quadric_of_positive_section_pivots [PreirreducibleSpace X]
    {A B : LogarithmicProjection i D} {b' : Basis (Fin 2) ℤ N}
    {hi : IsIntegralLattice i} {e n : ℕ} {ι : Type*}
    (M : HirzebruchPlaneResolution A B b' hi e n) (s : PositiveSectionMarking M ι)
    (hstep : ∀ {A : LogarithmicProjection i D} {k l : ℕ}
      (U : HirzebruchPlaneResolution A B b' hi (k + 1) (l + 1)) (t : PositiveSectionMarking U ι)
      (j : Fin (l + 1)), j ∈ U.positiveCenters →
      (∀ p < j, U.closed.baseCenter p ≠ U.closed.baseCenter j) →
      ((∃ (σ : A.fan.cones) (q : Fin 2),
          Nat.card (ToricRay σ.val) = 2 ∧ (U.rays 2).toCone ≤ σ ∧
          σ.val = hull ℝ {i (-U.basis 0), i (fiberRay[U.rays,q]).primitiveGenerator} ∧
          A.fan.distinguishedPointHom σ pt = U.closed.baseCenter j) ∨
        ∃ c : ℂˣ, U.closed.baseCenter j = center[U.basis,U.rays 2,c]) →
      ∃ (C : LogarithmicProjection i D) (W : HirzebruchPlaneResolution C B b' hi k (1 + l))
        (fiber : ι ↪ Fin 2) (index : ι → Fin (1 + l)), Nonempty (SarkisovPath A C) ∧
        W.fiberDegree = U.fiberDegree ∧ W.fiberCoefficient = U.fiberCoefficient - U.order j ∧
        Fin.castAdd l (0 : Fin 1) ∉ W.positiveCenters ∧
        (∀ p : Fin l, p.natAdd 1 ∈ W.sectionCenters ↔ j.succAbove p ∈ U.sectionCenters) ∧
        (∀ p : Fin l, j.succAbove p ∈ U.sectionCenters →
          W.order (p.natAdd 1) = U.order (j.succAbove p)) ∧
        (∀ a, ∀ p < index a, W.closed.baseCenter p ≠ W.closed.baseCenter (index a)) ∧
        (∀ a, W.ruling (W.closed.baseCenter (index a)) = coordPoint[fiber a] pt) ∧
        (∀ a, index a ∉ W.sectionCenters) ∧
        ∀ a, U.order (t.index a) ≤ W.order (index a)) :
    ∃ (C : LogarithmicProjection i D) (m : ℕ) (W : HirzebruchPlaneResolution C B b' hi 0 m)
      (u : PositiveSectionMarking W ι), Nonempty (SarkisovPath A C) ∧ m = n ∧
      W.fiberDegree = M.fiberDegree ∧ W.fiberCoefficient = s.remainingCoefficient ∧
      ∀ a, M.order (s.index a) ≤ W.order (u.index a) := by
  induction e generalizing A n with
  | zero =>
    exact ⟨A, n, M, s, ⟨Quiver.Path.nil⟩, rfl, rfl, s.remainingCoefficient_zero.symm,
      fun _ ↦ le_rfl⟩
  | succ k ih =>
    have hnonempty : s.selected.Nonempty :=
      Finset.card_pos.mp (s.card_selected.symm ▸ Nat.succ_pos k : 0 < s.selected.card)
    obtain ⟨j, hj⟩ := hnonempty
    cases n with
    | zero => exact Fin.elim0 j
    | succ l =>
      obtain ⟨p, hp, hmax, hearly, hfirst, hcase⟩ :=
        M.exists_first_max_of_positiveCenters_nonempty ⟨j, s.selection.subset hj⟩
      obtain ⟨C, U, fiber, index, ⟨q⟩, hdeg, hcoef, hhead, hsection, horder, hfirst', hvalue,
        hoff, hretained⟩ := hstep M s p hp hfirst hcase
      obtain ⟨t, ht, hremain⟩ := s.exists_of_pivot p hp hmax hearly hhead hsection horder
        hcoef fiber index hfirst' hvalue hoff
      obtain ⟨E, m, W, u, ⟨w⟩, hm, hdeg', hcoef', hretained'⟩ := ih U t
      refine ⟨E, m, W, u, ⟨Quiver.Path.comp q w⟩, hm.trans (Nat.add_comm 1 l),
        hdeg'.trans hdeg, hcoef'.trans hremain, fun a ↦ (hretained a).trans ?_⟩
      simpa only [ht] using hretained' a

end TauCeti.Toric.Fan.LogarithmicProjection
