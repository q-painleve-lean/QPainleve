/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Contraction
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Complexity

import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Isomorphism
import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryPrimes
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField

/-!
# Internal blowdown towers of anticanonical pairs

A point blowup tower with distinct projected centers restricts to an isomorphism
from a nodal anticanonical boundary omitting the exceptional curves onto its
schematic image. The image is again nodal and anticanonical, and the projected
centers lie in its smooth locus. The total boundary transform multiplies the
strict boundary ideal by the ramification ideal of the tower.

This is the contraction of an exceptional configuration in the proof of
[Gross, Hacking and Keel, Theorem 1.8](https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}

private theorem baseCenter_last_notMem_range {I : Y.IdealSheafData}
    (hT : IsClosedPointTower X (T.snoc I)) (hinj : Function.Injective hT.baseCenter) :
    hT.baseCenter (Fin.last n) ∉ Set.range (snoc_iff.mp hT).1.baseCenter := by
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i (hinj ((baseCenter_snoc_castSucc hT i).trans hi))

/-- If the base images of the centers are distinct, the last center is the entire
fiber of the prefix projection over its image. -/
private theorem preimage_singleton_baseCenter_last {I : Y.IdealSheafData}
    (hT : IsClosedPointTower X (T.snoc I)) (hinj : Function.Injective hT.baseCenter) :
    T.toBase ⁻¹' {hT.baseCenter (Fin.last n)} = {hT.lastCenter.val} := by
  have havoid := baseCenter_last_notMem_range hT hinj
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hy
    exact (snoc_iff.mp hT).1.injOn_toBase_compl_range_baseCenter
      (by simpa only [Set.mem_preimage, Set.mem_compl_iff, hy] using havoid)
      (by simpa only [Set.mem_preimage, Set.mem_compl_iff, baseCenter_snoc_last] using havoid)
      (hy.trans (baseCenter_snoc_last hT))
  · rintro rfl
    exact (baseCenter_snoc_last hT).symm

private theorem support_comap_baseCenter_snoc_last {I : Y.IdealSheafData}
    (hT : IsClosedPointTower X (T.snoc I)) (hinj : Function.Injective hT.baseCenter)
    [IsLocallyNoetherian X] :
    (((X.fromSpecResidueField (hT.baseCenter (Fin.last n))).ker.comap
      (T.snoc I).toBase).support : Set I.blowup) =
      (I.comap I.blowupToBase).support := by
  obtain ⟨hU, p, hp, hI⟩ := snoc_iff.mp hT
  have hfiber := preimage_singleton_baseCenter_last hT hinj
  rw [hT.lastCenter_eq p hp hI] at hfiber
  rw [toBase_snoc, comap_comp, support_comap, support_comap, support_comap,
    Closeds.coe_preimage, Closeds.coe_preimage, Closeds.coe_preimage,
    X.support_ker_fromSpecResidueField_of_isClosed (hT.isClosed_baseCenter (Fin.last n)),
    hfiber]
  rw [hI, Y.support_ker_fromSpecResidueField_of_isClosed hp]

private theorem omits_prefix_fibers {I B : Y.IdealSheafData} {A : I.blowup.IdealSheafData}
    (hT : IsClosedPointTower X (T.snoc I)) (hinj : Function.Injective hT.baseCenter)
    [IsLocallyNoetherian X]
    (e : A.subscheme ≅ B.subscheme)
    (he : e.hom ≫ B.subschemeι = A.subschemeι ≫ I.blowupToBase)
    (hA : ∀ j, ¬ ((X.fromSpecResidueField (hT.baseCenter j)).ker.comap
      (T.snoc I).toBase).support ≤ A.support) (j : Fin n) :
    ¬ ((X.fromSpecResidueField ((snoc_iff.mp hT).1.baseCenter j)).ker.comap T.toBase).support ≤
      B.support := by
  obtain ⟨hU, p, hp, hI⟩ := snoc_iff.mp hT
  have hcenter : (I.support : Set Y) = {p} :=
    (congrArg (fun J : Y.IdealSheafData ↦ (J.support : Set Y)) hI).trans
      (Y.support_ker_fromSpecResidueField_of_isClosed hp)
  have havoid := baseCenter_last_notMem_range hT hinj
  rw [baseCenter_snoc_last, hT.lastCenter_eq p hp hI] at havoid
  have hne : hU.baseCenter j ≠ T.toBase p := fun h ↦ havoid ⟨j, h⟩
  let J := (X.fromSpecResidueField (hU.baseCenter j)).ker
  have hJ : (J.support : Set X) = {hU.baseCenter j} :=
    X.support_ker_fromSpecResidueField_of_isClosed (hU.isClosed_baseCenter j)
  intro hsub
  apply hA j.castSucc
  rw [baseCenter_snoc_castSucc, toBase_snoc, comap_comp]
  intro x hx
  have hy : I.blowupToBase x ∈ (J.comap T.toBase).support := by
    simpa only [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage] using hx
  have hrange : I.blowupToBase x ∈ Set.range B.subschemeι := by
    rw [B.range_subschemeι]
    exact hsub hy
  obtain ⟨b, hb⟩ := hrange
  have hround : e.hom (e.inv b) = b := by simp
  have hab : I.blowupToBase (A.subschemeι (e.inv b)) = I.blowupToBase x := by
    rw [← Scheme.Hom.comp_apply, ← he, Scheme.Hom.comp_apply, hround, hb]
  have hmiss : I.blowupToBase x ∉ (I.support : Set Y) := by
    rw [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage, hJ,
      Set.mem_singleton_iff] at hy
    rw [hcenter, Set.mem_singleton_iff]
    exact fun h ↦ hne (hy.symm.trans (congrArg T.toBase h))
  have hmiss' : I.blowupToBase (A.subschemeι (e.inv b)) ∉ (I.support : Set Y) := hab.symm ▸ hmiss
  have hx' := I.injOn_blowupToBase_compl_support hmiss' hmiss hab
  rw [← hx']
  rw [← SetLike.mem_coe, ← A.range_subschemeι]
  exact Set.mem_range_self (e.inv b)

variable (k : Type u) [Field k] [PerfectField k] [IsIntegral X] [IsNoetherian X]
  [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "s" => (X ↘ S)
local notation "K(" Z ")" => mk (canonicalBundle k Z 2)

private theorem internalBlowdown_snoc {I : Y.IdealSheafData}
    (hT : IsClosedPointTower X T) (p : Y) (hp : IsClosed ({p} : Set Y))
    (hI : I = (Y.fromSpecResidueField p).ker) {B : I.blowup.IdealSheafData}
    (hB : B.IsEffectiveCartier) (hlast : ¬ (I.comap I.blowupToBase).support ≤ B.support)
    (hN : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ (T.snoc I).toBase ≫ s)) :
    let : I.blowup.Over S := ⟨(T.snoc I).toBase ≫ s⟩
    let : SmoothOfRelativeDimension 2 (I.blowup ↘ S) :=
      (hT.snoc p hp hI).smoothOfRelativeDimension s
    mk hB.toInvertibleSheaf = K(I.blowup) →
    let : Y.Over S := ⟨T.toBase ≫ s⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
    let D := B.map I.blowupToBase
    ∃ hD : D.IsEffectiveCartier, mk hD.toInvertibleSheaf = K(Y) ∧
      ∃ hnodal : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ T.toBase ≫ s),
        D.comap I.blowupToBase = B * I.comap I.blowupToBase ∧
        (let : LocallyOfFinitePresentation (D.subschemeι ≫ T.toBase ≫ s) :=
          hnodal.syntomic.locallyOfFinitePresentation
         ∃ q : D.subscheme, D.subschemeι q = p ∧
           q ∈ (D.subschemeι ≫ T.toBase ≫ s).smoothLocus) ∧
        ∃ e : B.subscheme ≅ D.subscheme, e.hom ≫ D.subschemeι = B.subschemeι ≫ I.blowupToBase := by
  let J := vanishingIdeal (Closeds.mk (closure ({p} : Set Y)) isClosed_closure)
  have hJ : J = I := (hI.trans (Y.ker_fromSpecResidueField_eq_vanishingIdeal p)).symm
  let a : J.blowup ≅ I.blowup := I.blowupIso (Iso.refl Y) (by simpa using hJ.symm)
  have ha : a.hom ≫ I.blowupToBase = J.blowupToBase := by simp [a]
  let : Y.Over S := ⟨T.toBase ≫ s⟩
  let : I.blowup.Over S := ⟨(T.snoc I).toBase ≫ s⟩
  have : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
  have : SmoothOfRelativeDimension 2 (I.blowup ↘ S) := (hT.snoc p hp hI).smoothOfRelativeDimension s
  have : IsIntegral Y := hT.isIntegral s
  have : IsNoetherian Y := T.isNoetherian
  have hf : I.blowupToBase ≫ (T.toBase ≫ s) = (T.snoc I).toBase ≫ s := by
    rw [toBase_snoc, Category.assoc]
  have : I.blowupToBase.IsOver S := ⟨hf⟩
  dsimp only
  intro hcan
  obtain ⟨hD, hcanD, hnd, -, htotal, -, hpoint, e, he⟩ :=
    hB.internalBlowdown_of_anticanonical_of_blowupIso k hp I.blowupToBase a ha
      (hJ.symm ▸ hlast) hN hcan
  have hfactor : J.comap I.blowupToBase = I.comap I.blowupToBase :=
    congrArg (fun L : Y.IdealSheafData ↦ L.comap I.blowupToBase) hJ
  exact ⟨hD, hcanD, hnd, htotal.trans (congrArg (B * ·) hfactor), hpoint, e, he⟩

/-- Contract a nodal anticanonical boundary along a specified closed-point tower
with distinct projected centers. When the boundary omits each exceptional fiber,
its schematic image is a nodal anticanonical divisor and the restriction of the
projection is an isomorphism. All projected centers are smooth points of the image,
and the total boundary transform has the ramification ideal as its exceptional factor. -/
theorem internalBlowdown_tower_of_anticanonical (hT : IsClosedPointTower X T)
    (hinj : Function.Injective hT.baseCenter) {B : Y.IdealSheafData}
    (hB : B.IsEffectiveCartier)
    (homit : ∀ j, ¬ ((X.fromSpecResidueField (hT.baseCenter j)).ker.comap T.toBase).support ≤
      B.support)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ T.toBase ≫ s)) :
    let : Y.Over S := ⟨T.toBase ≫ s⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
    mk hB.toInvertibleSheaf = K(Y) →
    let D := B.map T.toBase
    ∃ hD : D.IsEffectiveCartier, mk hD.toInvertibleSheaf = K(X) ∧
      ∃ hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s),
        D.comap T.toBase = B * hT.ramificationIdealSheafToBase k ∧
        (let : LocallyOfFinitePresentation (D.subschemeι ≫ s) :=
          hN.syntomic.locallyOfFinitePresentation
         ∀ j, ∃ q : D.subscheme, D.subschemeι q = hT.baseCenter j ∧
           q ∈ (D.subschemeι ≫ s).smoothLocus) ∧
        ∃ e : B.subscheme ≅ D.subscheme, e.hom ≫ D.subschemeι = B.subschemeι ≫ T.toBase := by
  induction hT with
  | nil =>
    dsimp only
    intro hcan
    have hmap : B.map (BlowupTower.nil (X := X)).toBase = B := by rw [toBase_nil, map_id]
    rw [hmap]
    refine ⟨hB, ?_, ?_, ?_, fun i ↦ i.elim0, Iso.refl _, ?_⟩
    · have hbase : (BlowupTower.nil (X := X)).toBase ≫ s = s := by
        rw [toBase_nil, Category.id_comp]
      have hclass (f : X ⟶ S) (hf : f = s) (hs : SmoothOfRelativeDimension 2 f) :
          @canonicalBundle k _ X ⟨f⟩ 2 hs = canonicalBundle k X 2 := by
        subst f
        rfl
      rw [hclass _ hbase (IsClosedPointTower.nil.smoothOfRelativeDimension s)] at hcan
      exact hcan
    · simpa only [toBase_nil, Category.id_comp] using hnodal
    · rw [toBase_nil, comap_id, ramificationIdealSheafToBase_nil, mul_top]
    · rw [Iso.refl_hom, toBase_nil, Category.id_comp, Category.comp_id]
  | @snoc m W U I hU p hp hI ih =>
    let hT := hU.snoc p hp hI
    have hlast := homit (Fin.last m)
    rw [← SetLike.coe_subset_coe, support_comap_baseCenter_snoc_last hT hinj] at hlast
    rw [SetLike.coe_subset_coe] at hlast
    dsimp only
    intro hcan
    obtain ⟨hD, hcanD, hnd, htotal, ⟨q, hq, hqs⟩, e, he⟩ :=
      internalBlowdown_snoc k hU p hp hI hB hlast hnodal hcan
    have hinj' : Function.Injective hU.baseCenter := by
      intro a b hab
      exact Fin.castSucc_injective _ (hinj (by simpa only [baseCenter_snoc_castSucc] using hab))
    obtain ⟨hC, hcanC, hnc, hc, hpoints, d, hd⟩ :=
      ih hinj' hD (omits_prefix_fibers hT hinj e he homit) hnd hcanD
    have hcmap : B.map (U.snoc I).toBase = (B.map I.blowupToBase).map U.toBase := by
      rw [toBase_snoc, map_comp]
    rw [hcmap]
    refine ⟨hC, hcanC, hnc, ?_, ?_, e ≪≫ d, ?_⟩
    · rw [toBase_snoc, comap_comp, hc, comap_mul, htotal,
        ramificationIdealSheafToBase_snoc, mul_assoc]
    · refine Fin.lastCases ?_ (fun j ↦ ?_)
      · refine ⟨d.hom q, ?_, ?_⟩
        · rw [← Scheme.Hom.comp_apply, hd, Scheme.Hom.comp_apply, hq,
            baseCenter_snoc_last, lastCenter_eq hT p hp hI]
        · have := hnc.syntomic.locallyOfFinitePresentation
          rw [← Scheme.Hom.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq,
            Scheme.Hom.mem_smoothLocus, ← Category.assoc, hd, Category.assoc]
          have := hnd.syntomic.locallyOfFinitePresentation
          exact Scheme.Hom.mem_smoothLocus.mp hqs
      · simpa only [baseCenter_snoc_castSucc] using hpoints j
    · rw [Iso.trans_hom, Category.assoc, hd, ← Category.assoc, he, Category.assoc, toBase_snoc]

include k in
/-- A point blowup projection that identifies two effective Cartier boundaries
increases the boundary complexity by the number of blowups. In particular,
contracting an internal exceptional configuration of that size removes the
same amount of complexity. -/
theorem boundaryComplexity_eq_add_length_of_subschemeIso
    [Module.Finite ℤ (Additive (LineBundleClass X))]
    (hT : IsClosedPointTower X T) {D : X.IdealSheafData} {B : Y.IdealSheafData}
    (hD : D.IsEffectiveCartier) (hB : B.IsEffectiveCartier)
    (e : B.subscheme ≅ D.subscheme)
    (he : e.hom ≫ D.subschemeι = B.subschemeι ≫ T.toBase) :
    B.boundaryComplexity = D.boundaryComplexity + n := by
  have : IsNoetherian Y := T.isNoetherian
  have hprimes := (hB.bijOn_boundaryPrimes_of_subschemeIso hD T.toBase e he).ncard_eq
  rw [boundaryComplexity_def, boundaryComplexity_def, finrank_picard k hT, hprimes]
  push_cast
  ring

end QPainleve.BlowupTower.IsClosedPointTower
