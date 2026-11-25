/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.NodalContraction
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Complexity

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.Point.BoundaryPrimes
import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryPrimes
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Boundary complexity along mixed point blowup towers

A reduced anticanonical boundary determines a boundary at each stage of a
point blowup tower by schematic image. Each blowup increases the complexity
by one precisely when the exceptional curve is omitted from that stage's
boundary. This gives an indexed count of the internal steps, including
blowups at infinitely near points.

See [Friedman, *On the geometry of anticanonical pairs*, Lemmas 1.2 and 2.2][Friedman]
for the charge and its behavior under interior and corner blowups.

[Friedman]: https://arxiv.org/abs/1502.02560
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

universe u

namespace QPainleve.BlowupTower

variable {X Y : Scheme.{u}} {n : ℕ}

open Classical in
/-- The indices of steps whose exceptional support is omitted by the schematic
image of the top boundary on the surface created by that step. For a reduced
anticanonical boundary on a closed-point tower, these are the internal blowups. -/
def internalBlowupIndices : {n : ℕ} → {Y : Scheme.{u}} →
    BlowupTower X n Y → Y.IdealSheafData → Finset (Fin n)
  | _, _, .nil, _ => ∅
  | _, _, .snoc T I, B =>
    let earlier := (T.internalBlowupIndices (B.map I.blowupToBase)).map Fin.castSuccEmb
    if (I.comap I.blowupToBase).support ≤ B.support then earlier
    else insert (Fin.last _) earlier

/-- An empty tower has no internal blowups. -/
@[simp]
theorem internalBlowupIndices_nil (B : X.IdealSheafData) :
    (nil (X := X)).internalBlowupIndices B = ∅ :=
  (rfl)

open Classical in
/-- Appending a blowup leaves the previous indices of the schematic image intact
and adds the new index precisely when the exceptional support is omitted. -/
theorem internalBlowupIndices_snoc (T : BlowupTower X n Y) (I : Y.IdealSheafData)
    (B : I.blowup.IdealSheafData) :
    (T.snoc I).internalBlowupIndices B =
      let earlier := (T.internalBlowupIndices (B.map I.blowupToBase)).map Fin.castSuccEmb
      if (I.comap I.blowupToBase).support ≤ B.support then earlier
      else insert (Fin.last n) earlier :=
  (rfl)

/-- The internal indices before the last blowup are read from the schematic image. -/
@[simp]
theorem castSucc_mem_internalBlowupIndices_snoc {T : BlowupTower X n Y} {I : Y.IdealSheafData}
    {B : I.blowup.IdealSheafData} (j : Fin n) :
    j.castSucc ∈ (T.snoc I).internalBlowupIndices B ↔
      j ∈ T.internalBlowupIndices (B.map I.blowupToBase) := by
  rw [internalBlowupIndices_snoc]
  split <;> simp [Finset.mem_map, Fin.castSucc_ne_last]

/-- The last step is internal exactly when its exceptional support is omitted. -/
@[simp]
theorem last_mem_internalBlowupIndices_snoc {T : BlowupTower X n Y} {I : Y.IdealSheafData}
    {B : I.blowup.IdealSheafData} :
    Fin.last n ∈ (T.snoc I).internalBlowupIndices B ↔
      ¬ (I.comap I.blowupToBase).support ≤ B.support := by
  rw [internalBlowupIndices_snoc]
  split <;> simp only [*, Finset.mem_map, Fin.castSuccEmb_apply, Fin.castSucc_ne_last,
    and_false, exists_false, Finset.mem_insert, or_false, not_true, not_false_eq_true]

open Classical in
private theorem card_internalBlowupIndices_snoc (T : BlowupTower X n Y) (I : Y.IdealSheafData)
    (B : I.blowup.IdealSheafData) :
    ((T.snoc I).internalBlowupIndices B).card =
      (T.internalBlowupIndices (B.map I.blowupToBase)).card +
        if (I.comap I.blowupToBase).support ≤ B.support then 0 else 1 := by
  rw [internalBlowupIndices_snoc]
  split <;> simp [Finset.mem_map, Fin.castSucc_ne_last]

section PointBlowup

variable {k : Type u} [Field k] [PerfectField k] {p : X}
  [IsIntegral X] [IsNoetherian X]
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]

local notation "I" => Scheme.Hom.ker (X.fromSpecResidueField p)
local notation "π" => blowupToBase I
local notation "E" => comap I π

open Classical in
include f in
private theorem ncard_boundaryPrimes_of_totalTransform
    (hp : IsClosed ({p} : Set X)) {D : X.IdealSheafData} {B : (I).blowup.IdealSheafData}
    (hD : D.IsEffectiveCartier) (hB : B.IsEffectiveCartier) (hpD : p ∈ D.support)
    (h : D.comap π = B * E) :
    B.boundaryPrimes.ncard + (if (E).support ≤ B.support then 0 else 1) =
      D.boundaryPrimes.ncard + 1 := by
  have hd := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp inferInstance).2 p hp
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have := isRegularLocalRing_stalk_of_smooth f p
  let : IsIntegral (I).blowup :=
    (IsClosedPointTower.nil.snoc p hp rfl).isIntegral f
  let : IsNoetherian (I).blowup := isNoetherian_of_finiteType π
  have hE := isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hd
  let : IsIntegral (E).subscheme := hE.isIntegral_subscheme
  let q := (E).subschemeι (genericPoint (E).subscheme)
  have hq : Order.coheight q = 1 := hE.isEffectiveCartier.coheight_subschemeι_genericPoint
  have hcard : (D.comap π).boundaryPrimes.ncard = D.boundaryPrimes.ncard + 1 := by
    have hc := congrArg ENat.toNat (D.encard_boundaryPrimes_comap_pointBlowup f hp hpD)
    rw [ENat.toNat_add hD.finite_boundaryPrimes.encard_lt_top.ne
      (show (1 : ℕ∞) ≠ ⊤ by simp), ENat.toNat_one] at hc
    exact hc
  rw [← hcard]
  by_cases hEB : (E).support ≤ B.support
  · rw [ite_eq_left hEB, add_zero]
    apply congrArg Set.ncard
    exact boundaryPrimes_eq_of_support_eq (by rw [h, support_mul, sup_eq_left.mpr hEB])
  · have hqB : q ∉ B.boundaryPrimes := by
      intro hb
      apply hEB
      have hs := (E).support_eq_closure_subschemeι_genericPoint
      refine IsConcreteLE.le_iff.mpr ?_
      intro x hx
      rw [← SetLike.mem_coe, hs] at hx
      exact (closure_minimal (Set.singleton_subset_iff.mpr (mem_boundaryPrimes.mp hb).1)
        B.support.isClosed) hx
    have hinsert : (D.comap π).boundaryPrimes = insert q B.boundaryPrimes := by
      ext x
      simp only [h, mem_boundaryPrimes, support_mul, Set.mem_insert_iff,
        ← SetLike.mem_coe, Closeds.coe_sup, Set.mem_union]
      constructor
      · rintro ⟨hx | hx, hc⟩
        · exact Or.inr ⟨hx, hc⟩
        · exact Or.inl ((hE.isEffectiveCartier.mem_support_iff_eq_subschemeι_genericPoint hc).mp hx)
      · rintro (rfl | ⟨hx, hc⟩)
        · exact ⟨Or.inr (by rw [← range_subschemeι]; exact Set.mem_range_self _), hq⟩
        · exact ⟨Or.inl hx, hc⟩
    rw [ite_eq_right hEB, hinsert, Set.ncard_insert_of_notMem hqB hB.finite_boundaryPrimes]

end PointBlowup

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "g[" X "]" => (X ↘ S)
local notation "K(" X ")" => mk (QPainleve.canonicalBundle k X 2)
local notation "Pic(" X ")" => Additive (LineBundleClass X)

variable [PerfectField k] in
private theorem canonicalBundle_snoc {U : BlowupTower X n Y} {I : Y.IdealSheafData}
    (hT : IsClosedPointTower X (U.snoc I))
    (hs : SmoothOfRelativeDimension 2 (I.blowupToBase ≫ U.toBase ≫ g[X])) :
    @QPainleve.canonicalBundle k _ I.blowup ⟨(U.snoc I).toBase ≫ g[X]⟩ 2
        (hT.smoothOfRelativeDimension g[X]) =
      @QPainleve.canonicalBundle k _ I.blowup ⟨I.blowupToBase ≫ U.toBase ≫ g[X]⟩ 2 hs := by
  apply ObjectProperty.FullSubcategory.ext
  exact (@QPainleve.canonicalBundle_obj k _ I.blowup ⟨(U.snoc I).toBase ≫ g[X]⟩ 2
    (hT.smoothOfRelativeDimension g[X])).trans
    ((congrArg (fun f ↦ differentialForms k f 2) (by rw [toBase_snoc, Category.assoc])).trans
      (@QPainleve.canonicalBundle_obj k _ I.blowup ⟨I.blowupToBase ≫ U.toBase ≫ g[X]⟩ 2 hs).symm)

section Complexity

variable [PerfectField k] [IsIntegral X] [IsNoetherian X] [Module.Finite ℤ (Pic(X))]

open Classical in
include k in
private theorem pointBlowup_complexity_step {T : BlowupTower X n Y}
    (hT : IsClosedPointTower X T) {p : Y} (hp : IsClosed ({p} : Set Y))
    {I : Y.IdealSheafData} (hI : I = (Y.fromSpecResidueField p).ker)
    {B : I.blowup.IdealSheafData} (hB : B.IsEffectiveCartier)
    (hD : (B.map I.blowupToBase).IsEffectiveCartier)
    (hpD : p ∈ (B.map I.blowupToBase).support)
    (htotal : (B.map I.blowupToBase).comap I.blowupToBase = B * I.comap I.blowupToBase) :
    B.boundaryComplexity = (B.map I.blowupToBase).boundaryComplexity +
      if (I.comap I.blowupToBase).support ≤ B.support then 0 else 1 := by
  subst I
  let I := (Y.fromSpecResidueField p).ker
  let : IsNoetherian Y := T.isNoetherian
  let : IsIntegral Y := hT.isIntegral g[X]
  let : SmoothOfRelativeDimension 2 (T.toBase ≫ g[X]) := hT.smoothOfRelativeDimension g[X]
  have hrank : Module.finrank ℤ (Pic(I.blowup)) = Module.finrank ℤ (Pic(Y)) + 1 := by
    rw [finrank_picard k (hT.snoc p hp rfl), finrank_picard k hT]
    omega
  have hcount := ncard_boundaryPrimes_of_totalTransform (T.toBase ≫ g[X]) hp hD hB hpD htotal
  rw [boundaryComplexity_def, boundaryComplexity_def, hrank]
  by_cases h : (I.comap I.blowupToBase).support ≤ B.support
  · rw [ite_eq_left h] at hcount ⊢
    omega
  · rw [ite_eq_right h] at hcount ⊢
    omega

/-- The complexity of a reduced anticanonical boundary equals the complexity
of its schematic image plus the number of internal steps of the specified
closed-point blowup tower. This applies to towers that interleave internal
and boundary blowups. -/
theorem IsClosedPointTower.boundaryComplexity_eq_add_card_internalBlowupIndices
    {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)
    {B : Y.IdealSheafData} [IsReduced B.subscheme] (hB : B.IsEffectiveCartier) :
    let : Y.Over S := ⟨T.toBase ≫ g[X]⟩
    let : SmoothOfRelativeDimension 2 g[Y] := hT.smoothOfRelativeDimension g[X]
    mk hB.toInvertibleSheaf = K(Y) →
    B.boundaryComplexity =
      (B.map T.toBase).boundaryComplexity + (T.internalBlowupIndices B).card := by
  induction hT with
  | nil => simp
  | @snoc m W U I hU p hp hI ih =>
    have hcenter := hI.trans (W.ker_fromSpecResidueField_eq_vanishingIdeal p)
    subst hcenter
    let I := vanishingIdeal (Closeds.mk (closure {p}) isClosed_closure)
    let : W.Over S := ⟨U.toBase ≫ g[X]⟩
    let : SmoothOfRelativeDimension 2 g[W] := hU.smoothOfRelativeDimension g[X]
    let : IsIntegral W := hU.isIntegral g[X]
    let : IsNoetherian W := U.isNoetherian
    dsimp only
    intro hcan
    rw [canonicalBundle_snoc k (hU.snoc p hp hI)
      (smoothOfRelativeDimension_blowup_closed_point g[W] hp)] at hcan
    obtain ⟨hD, hred, hcanD, htotal, hcases⟩ :=
      hB.anticanonical_boundary_point_blowdown k hp hcan
    let D := B.map I.blowupToBase
    have hpD : p ∈ D.support := (D.one_le_stalkOrder_iff p).mp
      (by
        rcases hcases with ⟨h, -⟩ | ⟨h, -⟩
        · exact h.ge
        · exact one_le_two.trans h.ge)
    let : IsReduced D.subscheme := hred
    have hprev := ih hD hcanD
    have hq := pointBlowup_complexity_step k hU hp hI hB hD hpD htotal
    rw [toBase_snoc, map_comp, card_internalBlowupIndices_snoc, hq, hprev, Nat.cast_add, add_assoc]
    split <;> simp

end Complexity

variable [IsAlgClosed k] [NeZero (2 : k)] [IsIntegral X] [X.IsProjectiveOver k]

/-- If every exceptional curve belongs to the boundary at the stage where it
is contracted, a specified closed-point contraction of a nodal anticanonical
boundary is a nodal tower. The boundary upstairs is the reduced total transform. -/
theorem IsClosedPointTower.isNodalBoundaryTower_of_internalBlowupIndices_eq_empty
    {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)
    {B : Y.IdealSheafData} (hB : B.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ T.toBase ≫ g[X]))
    (hindices : T.internalBlowupIndices B = ∅) :
    let : Y.Over S := ⟨T.toBase ≫ g[X]⟩
    let : SmoothOfRelativeDimension 2 g[Y] := hT.smoothOfRelativeDimension g[X]
    mk hB.toInvertibleSheaf = K(Y) →
    IsNodalBoundaryTower (B.map T.toBase) g[X] (𝟙 X) T ∧
      ((B.map T.toBase).comap T.toBase).radical = B := by
  have : Smooth g[X] := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType g[X]
  induction hT with
  | nil =>
    intro _ _ _
    rw [toBase_nil, map_id, comap_id]
    exact ⟨.nil, B.isReduced_subscheme_iff_radical_eq.mp hnodal.isReduced⟩
  | @snoc m W U I hU p hp hI ih =>
    have hcenter := hI.trans (W.ker_fromSpecResidueField_eq_vanishingIdeal p)
    subst hcenter
    let I := vanishingIdeal (Closeds.mk (closure {p}) isClosed_closure)
    let : W.Over S := ⟨U.toBase ≫ g[X]⟩
    let : SmoothOfRelativeDimension 2 g[W] := hU.smoothOfRelativeDimension g[X]
    let : IsIntegral W := hU.isIntegral g[X]
    let : W.IsProjectiveOver k := U.isProjectiveOver k
    intro _ _ hcan
    have hbase : (U.snoc I).toBase ≫ g[X] = I.blowupToBase ≫ g[W] := by
      rw [toBase_snoc, Category.assoc]
      rfl
    have hnodal' : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ I.blowupToBase ≫ g[W]) :=
      hbase ▸ hnodal
    rw [canonicalBundle_snoc k (hU.snoc p hp hI)
      (smoothOfRelativeDimension_blowup_closed_point g[W] hp)] at hcan
    obtain ⟨hD, hcanD, hnodalD, htotal, hnode⟩ :=
      hB.anticanonical_nodal_boundary_point_blowdown k hp hnodal' hcan
    let D := B.map I.blowupToBase
    have hindices' : (U.snoc I).internalBlowupIndices B = ∅ := hindices
    have hE : (I.comap I.blowupToBase).support ≤ B.support := by
      by_contra hn
      have hm := (last_mem_internalBlowupIndices_snoc (T := U) (I := I) (B := B)).mpr hn
      exact Finset.notMem_empty _ (hindices' ▸ hm)
    have hprev : U.internalBlowupIndices D = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr fun j hj ↦ ?_
      have hm := (castSucc_mem_internalBlowupIndices_snoc (I := I) (B := B) j).mpr hj
      exact Finset.notMem_empty _ (hindices' ▸ hm)
    obtain ⟨hU', hD'⟩ := ih hD hnodalD hprev hcanD
    rw [toBase_snoc, map_comp]
    refine ⟨hU'.snoc p hp hI ?_, ?_⟩
    · rw [Category.comp_id, ← isNodeOfReducedBoundary_radical, hD']
      exact hnode.mp hE
    · -- The last exceptional curve already belongs to the reduced boundary.
      rw [comap_comp, ← vanishingIdeal_support, support_comap, ← support_radical (comap _ _),
        hD', ← support_comap, htotal, support_mul, sup_eq_left.mpr hE, vanishingIdeal_support]
      exact B.isReduced_subscheme_iff_radical_eq.mp hnodal.isReduced

variable [Module.Finite ℤ (Pic(X))] in
/-- A complexity-zero nodal anticanonical boundary descends along a specified
closed-point tower to a complexity-zero boundary, provided the image has
nonnegative complexity. Every step is a nodal blowup of that image, and the
original boundary is its reduced total transform. -/
theorem IsClosedPointTower.isNodalBoundaryTower_of_boundaryComplexity_eq_zero
    {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)
    {B : Y.IdealSheafData} (hB : B.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ T.toBase ≫ g[X]))
    (hzero : B.boundaryComplexity = 0)
    (hnonneg : 0 ≤ (B.map T.toBase).boundaryComplexity) :
    let : Y.Over S := ⟨T.toBase ≫ g[X]⟩
    let : SmoothOfRelativeDimension 2 g[Y] := hT.smoothOfRelativeDimension g[X]
    mk hB.toInvertibleSheaf = K(Y) →
    (B.map T.toBase).boundaryComplexity = 0 ∧
      IsNodalBoundaryTower (B.map T.toBase) g[X] (𝟙 X) T ∧
      ((B.map T.toBase).comap T.toBase).radical = B := by
  intro _ _ hcan
  have : Smooth g[X] := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType g[X]
  let : IsReduced B.subscheme := hnodal.isReduced
  have hq := hT.boundaryComplexity_eq_add_card_internalBlowupIndices k hB hcan
  rw [hzero] at hq
  have hempty : T.internalBlowupIndices B = ∅ := Finset.card_eq_zero.mp (by omega)
  exact ⟨by omega,
    hT.isNodalBoundaryTower_of_internalBlowupIndices_eq_empty k hB hnodal hempty hcan⟩

end QPainleve.BlowupTower
