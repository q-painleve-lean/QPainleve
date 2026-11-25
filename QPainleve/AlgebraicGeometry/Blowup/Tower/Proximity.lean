/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.PlaneResolution
public import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.Tower.CurveIntersection
import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Blowup.Tower.Reorder
import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef.Pullback

/-!
# Bounds on base orders over a point blowup

The sum of the orders at distinct first centers on a point exceptional curve
is bounded by the order at the original point. The degree on the exceptional
curve is read by `classIntersectionNumber_picardHom_exceptionalClass`. Applying
`sum_first_base_orders_le_curve_intersection` to that curve bounds the orders
of subsequent blowups. For a plane resolution, this determines a unique
point of the first exceptional curve above which the remaining high orders
lie, a local refinement of the base-center analysis in
[Lutz, Proposition 8.11][Lutz].

[Lutz]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.SymmetricAlgebra LineBundleClass Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [IsAlgClosed k] {X Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "f" => (X ↘ S)
local notation "I[" p "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ p)

/-- For a nef class marked on a tower starting with the blowup of a closed point,
the sum of its orders at selected first centers on the exceptional curve is at
most its order at the original point. The selected first centers are taken
relative to the point blowup, and subsequent centers may be infinitely near. -/
theorem sum_first_base_orders_le_exceptional_order {p : X} (hp : IsClosed ({p} : Set X))
    {n : ℕ} {U : BlowupTower (I[p]).blowup n Z}
    (hU : IsClosedPointTower (I[p]).blowup U)
    (a : LineBundleClass X) (m₀ : ℤ) (m : Fin n → ℕ) (s : Finset (Fin n))
    (hs : ∀ j ∈ s, (I[p]).blowupToBase (hU.baseCenter j) = p ∧
      ∀ l < j, hU.baseCenter l ≠ hU.baseCenter j)
    (hnef : (U.picardHom
      (Additive.ofMul (pullback (I[p]).blowupToBase a * (I[p]).blowupExceptionalClass ^ (-m₀)),
        fun l ↦ -(m l : ℤ))).toMul.IsNef k (U.toBase ≫ (I[p]).blowupToBase ≫ f)) :
    ∑ j ∈ s, (m j : ℤ) ≤ m₀ := by
  let I := I[p]
  let π := I.blowupToBase
  let E := I.comap π
  let L := pullback π a * I.blowupExceptionalClass ^ (-m₀)
  let T := BlowupTower.nil.snoc I
  have hT : IsClosedPointTower X T := .snoc .nil p hp rfl
  let : I.blowup.Over S := ⟨T.toBase ≫ f⟩
  let : E.subscheme.Over S := ⟨E.subschemeι ≫ (I.blowup ↘ S)⟩
  have hf : (I.blowup ↘ S) = π ≫ f := calc
    _ = T.toBase ≫ f := rfl
    _ = _ := by simp only [T, toBase_snoc, toBase_nil, Category.comp_id, π]
  let : IsNoetherian X := isNoetherian_of_finiteType f
  let : I.blowup.IsProjectiveOver k := T.isProjectiveOver k
  let : IsIntegral I.blowup := hT.isIntegral f
  have : SmoothOfRelativeDimension 2 (I.blowup ↘ S) := hT.smoothOfRelativeDimension f
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp inferInstance).2 p hp
  let : IsRegularLocalRing (X.presheaf.stalk p) := isRegularLocalRing_stalk_of_smooth f p
  have hE : E.IsExceptionalCurveOfFirstKind :=
    isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hdim
  let : IsProper (E.subscheme ↘ S) :=
    inferInstanceAs (IsProper (E.subschemeι ≫ (I.blowup ↘ S)))
  let : IsIntegral E.subscheme := hE.isIntegral_subscheme
  let : E.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨hE.isIntegral_subscheme, inferInstance, hE.topologicalKrullDim_subscheme⟩
  have hregular : IsRegular E.subscheme := by
    obtain ⟨κ, _, e, -⟩ := hE.exists_iso
    let : IsRegular (projectiveLine κ) := ⟨fun _ ↦ inferInstance⟩
    exact IsRegular.of_isOpenImmersion e.inv
  have hcenters : ∀ j ∈ s, hU.baseCenter j ∈ Set.range E.subschemeι ∧
      ∀ l < j, hU.baseCenter l ≠ hU.baseCenter j := by
    intro j hj
    obtain ⟨hj', hfirst⟩ := hs j hj
    refine ⟨?_, hfirst⟩
    rw [range_subschemeι, support_comap, Closeds.coe_preimage, Set.mem_preimage,
      X.support_ker_fromSpecResidueField_of_isClosed hp, Set.mem_singleton_iff]
    exact hj'
  have hbound := hU.sum_first_base_orders_le_curve_intersection E.subschemeι (I.blowup ↘ S)
    rfl L m s hcenters (by rwa [hf])
  have hdeg : intersectionNumber k E.subschemeι L = m₀ := by
    have hsurf := topologicalKrullDim_eq_of_smoothOfRelativeDimension (I.blowup ↘ S) (n := 2)
    rw [← Chow.classIntersectionNumber_eq_intersectionNumber_subschemeι k hsurf.le
      (I := E) I.isEffectiveCartier_comap_blowupToBase hE.topologicalKrullDim_subscheme,
      ← blowupExceptionalClass_def]
    have hpair := classIntersectionNumber_picardHom_exceptionalClass (k := k) hT
      (Additive.ofMul a, fun _ ↦ -m₀) (Fin.last 0)
    simpa only [exceptionalClass_snoc_last, picardHom_snoc_apply_toMul, picardHom_nil,
      toMul_ofMul, neg_neg, L, π, T, blowupExceptionalClass_def] using hpair
  exact hbound.trans_eq hdeg

section PlaneResolution

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "P" => Proj (homogeneousSubmodule k (Fin 3 → k))
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) 1)
local notation "mark[" T "," hT "," s "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking T hT s) (Additive.ofMul (pullback g H))

local notation "L[" p "," a "," x "]" =>
  (pullback (blowupToBase (I[p])) a * blowupExceptionalClass (I[p]) ^ x)

private theorem baseCenter_eq_of_high_orders_on_exceptional {p : X}
    (hp : IsClosed ({p} : Set X)) {n : ℕ} {U : BlowupTower (I[p]).blowup n Z}
    (hU : IsClosedPointTower (I[p]).blowup U) (g : Z ⟶ P)
    (hg : g ≫ (P ↘ S) = U.toBase ≫ (I[p]).blowupToBase ≫ f)
    (a : LineBundleClass X) (m₀ cutoff : ℤ) (hbound : m₀ ≤ cutoff) :
    let T := BlowupTower.nil.snoc (I[p])
    let : (I[p]).blowup.Over S := ⟨T.toBase ≫ f⟩
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let hT : IsClosedPointTower X T := .snoc .nil p hp rfl
    let : SmoothOfRelativeDimension 2 ((I[p]).blowup ↘ S) := hT.smoothOfRelativeDimension f
    let : IsNoetherian (I[p]).blowup := T.isNoetherian
    let : IsIntegral (I[p]).blowup := hT.isIntegral f
    let v := mark[U,hU,((I[p]).blowup ↘ S),g]
    v.1 = Additive.ofMul (L[p,a,-m₀]) →
    ∀ {j l : Fin n},
      (I[p]).blowupToBase (hU.baseCenter j) = p →
      (I[p]).blowupToBase (hU.baseCenter l) = p →
      cutoff < 2 * (-v.2 j) → cutoff < 2 * (-v.2 l) →
      hU.baseCenter j = hU.baseCenter l := by
  classical
  intro T hOver hNoeth hT hSmooth hNoeth' hIntegral v hv j l hj hl hjhigh hlhigh
  let := hOver
  let := hNoeth
  let := hSmooth
  let := hNoeth'
  let : (I[p]).blowup.IsProjectiveOver k := T.isProjectiveOver k
  let := hIntegral
  let : Z.Over S := ⟨U.toBase ≫ (I[p]).blowup ↘ S⟩
  have hf : (I[p]).blowup ↘ S = (I[p]).blowupToBase ≫ f := calc
    _ = T.toBase ≫ f := rfl
    _ = _ := by simp only [T, toBase_snoc, toBase_nil, Category.comp_id]
  have hg' : g ≫ P ↘ S = U.toBase ≫ (I[p]).blowup ↘ S := by rw [hf, hg]
  let : g.IsOver S := ⟨hg'⟩
  obtain ⟨j', hj', hjfirst, hjle⟩ := hU.exists_first_baseCenter_ge_of_plane_resolution g hg' j
  obtain ⟨l', hl', hlfirst, hlle⟩ := hU.exists_first_baseCenter_ge_of_plane_resolution g hg' l
  by_contra hne
  have hne' : j' ≠ l' := fun h ↦ hne (hj'.symm.trans (h ▸ hl'))
  obtain ⟨_, J, -, -, -, -, -, horders⟩ := hU.exists_moving_base_ideal_of_plane_resolution g hg'
  have hnef : (U.picardHom (Additive.ofMul (L[p,a,-m₀]),
      fun l ↦ -(hU.baseMultiplicities J l : ℤ))).toMul.IsNef k
      (U.toBase ≫ (I[p]).blowupToBase ≫ f) := by
    have hmark : (Additive.ofMul (L[p,a,-m₀]), fun l ↦ -(hU.baseMultiplicities J l : ℤ)) = v := by
      exact Prod.ext hv.symm (funext fun l ↦ neg_eq_iff_eq_neg.mpr (horders l).symm)
    rw [← hf, hmark]
    dsimp only [v]
    rw [← U.picardMarking_apply hU ((I[p]).blowup ↘ S),
      LinearEquiv.apply_symm_apply, toMul_ofMul]
    exact (isAmple_twistingSheaf k (Fin 3 → k) Nat.one_pos).isNef.pullback g
  have hsum := hU.sum_first_base_orders_le_exceptional_order hp a m₀ (hU.baseMultiplicities J)
    {j', l'} (by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ⟨hj' ▸ hj, hjfirst⟩
      · obtain rfl := Finset.mem_singleton.mp hi
        exact ⟨hl' ▸ hl, hlfirst⟩) hnef
  rw [Finset.sum_pair hne', ← horders, ← horders] at hsum
  dsimp only [v] at hjhigh hlhigh
  omega

/-- If a plane resolution has a high order above a chosen point after its first
blowup, all such high orders project to a single point of the first exceptional
curve. Here an order is high when it exceeds half the cutoff, and the first
order is at most the cutoff. Moving the first blowup to the front preserves the
specified plane projection and the ordered exceptional classes. -/
theorem exists_unique_high_base_center_on_first_exceptional
    {n : ℕ} {T : BlowupTower X n Z} (hT : IsClosedPointTower X T)
    (g : Z ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f)
    (j : Fin n) (hfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
    (cutoff : ℤ) :
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let v := mark[T,hT,f,g]
    let p := hT.baseCenter j
    (-v.2 j ≤ cutoff) →
    (∃ l, l ≠ j ∧ hT.baseCenter l = hT.baseCenter j ∧ cutoff < 2 * (-v.2 l)) →
    ∃ (m : ℕ) (W : Scheme) (U : BlowupTower (I[p]).blowup m W) (e : Z ≅ W)
      (hU : IsClosedPointTower (I[p]).blowup U) (tail : Fin m ↪o Fin n),
      Set.range tail = {l | l ≠ j} ∧
      e.hom ≫ U.toBase ≫ (I[p]).blowupToBase = T.toBase ∧
      pullback e.hom (pullback U.toBase (I[p]).blowupExceptionalClass) = T.exceptionalClass j ∧
      (∀ l, (I[p]).blowupToBase (hU.baseCenter l) = hT.baseCenter (tail l)) ∧
      (∀ l, pullback e.hom (U.exceptionalClass l) = T.exceptionalClass (tail l)) ∧
      (∃! q : (I[p]).blowup, (I[p]).blowupToBase q = p ∧
        ∀ l, hT.baseCenter (tail l) = p → cutoff < 2 * (-v.2 (tail l)) →
          hU.baseCenter l = q) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt j.isLt))
  intro hNoeth v p hcut hhigh
  let := hNoeth
  have hp : IsClosed ({p} : Set X) := hT.isClosed_baseCenter j
  obtain ⟨W, U, e, hU, he, hE, hcenters, htail⟩ :=
    hT.exists_move_closed_point_blowup_to_front j hp rfl hfirst
  refine ⟨n, W, U, e, hU, j.succAboveOrderEmb, ?_, he, hE, hcenters, htail, ?_⟩
  · ext l
    exact Fin.exists_succAbove_eq_iff
  let I := I[p]
  let V := BlowupTower.nil.snoc I
  have hV : IsClosedPointTower X V := .snoc .nil p hp rfl
  let : I.blowup.Over S := ⟨V.toBase ≫ f⟩
  let : SmoothOfRelativeDimension 2 (I.blowup ↘ S) := hV.smoothOfRelativeDimension f
  let : IsNoetherian I.blowup := V.isNoetherian
  let : IsIntegral I.blowup := hV.isIntegral f
  let g' := e.inv ≫ g
  have hg' : g' ≫ (P ↘ S) = U.toBase ≫ I.blowupToBase ≫ f := by
    simp only [g', Category.assoc, hg, ← he, Iso.inv_hom_id_assoc, I]
  let v' := mark[U,hU,(I.blowup ↘ S),g']
  have hv' : v' = (Additive.ofMul (L[p,v.1.toMul,v.2 j]), v.2 ∘ j.succAbove) := by
    apply (LinearEquiv.symm_apply_eq _).mpr
    apply Additive.toMul.injective
    have hm := T.pullback_picardHom_move_to_front j e he hE htail v.1 v.2
    rw [← T.picardMarking_apply hT f, LinearEquiv.apply_symm_apply, toMul_ofMul,
      picardHom_append] at hm
    have hprefix : (BlowupTower.nil.snoc (I[p])).picardHom (v.1, fun _ ↦ v.2 j) =
        Additive.ofMul (L[p,v.1.toMul,v.2 j]) := by
      apply Additive.toMul.injective
      simp only [picardHom_snoc_apply_toMul, picardHom_nil, toMul_ofMul]
    simpa only [g', pullback_comp, toMul_ofMul, Fin.addCases_left, Fin.addCases_right,
      picardMarking_apply, hprefix] using hm
  obtain ⟨l, hlj, hlp, hlhigh⟩ := hhigh
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hlj
  have hpa : I.blowupToBase (hU.baseCenter a) = p := (hcenters a).trans (ha ▸ hlp)
  have hbase : v'.1 = Additive.ofMul (L[p,v.1.toMul,-(-v.2 j)]) := by
    simpa only [neg_neg] using congrArg Prod.fst hv'
  refine ⟨hU.baseCenter a, ⟨hpa, ?_⟩, fun q hq ↦ ?_⟩
  · intro b hbp hbhigh
    have hb : cutoff < 2 * (-v'.2 b) := by
      simpa only [hv', Function.comp_apply, Fin.succAboveOrderEmb_apply] using hbhigh
    have hl' : cutoff < 2 * (-v'.2 a) := by simpa only [hv', Function.comp_apply, ha] using hlhigh
    exact baseCenter_eq_of_high_orders_on_exceptional hp hU g' hg' v.1.toMul (-v.2 j)
      cutoff hcut hbase ((hcenters b).trans hbp) hpa hb hl'
  · apply (hq.2 a ?_ ?_).symm
    · simpa only [Fin.succAboveOrderEmb_apply, ha] using hlp
    · simpa only [Fin.succAboveOrderEmb_apply, ha] using hlhigh

end PlaneResolution

end QPainleve.BlowupTower.IsClosedPointTower
