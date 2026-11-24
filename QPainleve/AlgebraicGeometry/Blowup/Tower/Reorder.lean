/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard

import QPainleve.AlgebraicGeometry.Blowup.Disjoint
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField

/-!
# Moving a proper center to the front of a point blowup tower

The first center over a given base point can be moved to the start of an ordered tower.
The isomorphism of the final schemes is over the original base and identifies the
total exceptional classes in the new order. In particular the first step of a link
at a proper base point can be performed on a specified resolution, with the resolved
linear system and its remaining exceptional coordinates carried along.
If the point is absent from the tower, it can first be blown up on the final scheme.
Moving this additional blowup to the front preserves the order of the original centers
and gives the pulled-back linear system exceptional coefficient zero at the new step.

The extraction of a proper center is used in [Lutz's appendix to Hacking and Keating,
Proposition 8.11][HKL]. The interchange of two steps uses
`Scheme.IdealSheafData.blowupCommOfDisjoint`.

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry LineBundleClass

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}

local notation "J[" p "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ p)

/-- The comparison with the tower obtained by first blowing up a point away from the projected
centers. The source of the comparison has one extra blowup at the inverse image of that point. -/
private structure Rebase (I : X.IdealSheafData) (T : BlowupTower X n Y) where
  top : Scheme.{u}
  tower : BlowupTower I.blowup n top
  isClosedPointTower : IsClosedPointTower I.blowup tower
  iso : (I.comap T.toBase).blowup ≅ top
  over_base : iso.hom ≫ tower.toBase ≫ I.blowupToBase =
    (I.comap T.toBase).blowupToBase ≫ T.toBase
  exceptional (j : Fin n) : pullback iso.hom (tower.exceptionalClass j) =
    pullback (I.comap T.toBase).blowupToBase (T.exceptionalClass j)
  baseCenter (hT : IsClosedPointTower X T) (j : Fin n) :
    I.blowupToBase (isClosedPointTower.baseCenter j) = hT.baseCenter j

private theorem Rebase.pullback_exceptional {I : X.IdealSheafData} (R : Rebase I T) :
    pullback R.iso.hom (pullback R.tower.toBase I.blowupExceptionalClass) =
      (I.comap T.toBase).blowupExceptionalClass := by
  have h : R.iso.hom ≫ R.tower.toBase = I.blowupMap T.toBase :=
    I.eq_blowupMap T.toBase (by simpa only [Category.assoc] using R.over_base)
  rw [pullback_comp, h, pullback_blowupExceptionalClass_blowupMap]

private def Rebase.nil (I : X.IdealSheafData) : Rebase I (.nil (X := X)) := by
  let e := I.blowupIso (Iso.refl _) (by simp [toBase_nil] :
    I.comap (Iso.refl X).hom = I.comap (BlowupTower.nil (X := X)).toBase)
  refine ⟨_, .nil, .nil, e, ?_, fun j ↦ j.elim0, fun _ j ↦ j.elim0⟩
  simp [e, toBase_nil]

private def Rebase.snoc {I : X.IdealSheafData} (R : Rebase I T) (J : Y.IdealSheafData)
    (h : Disjoint (J.support : Set Y) ((I.comap T.toBase).support : Set Y))
    {p : Y} (hp : IsClosed ({p} : Set Y)) (hJ : J = J[p])
    {q : (I.comap T.toBase).blowup} (hq : IsClosed ({q} : Set (I.comap T.toBase).blowup))
    (hqJ : J.comap (I.comap T.toBase).blowupToBase = J[q])
    (hqp : (I.comap T.toBase).blowupToBase q = p) :
    Rebase I (T.snoc J) := by
  let A := I.comap T.toBase
  let E := (BlowupTower.nil.snoc (J.comap A.blowupToBase)).transport R.iso
  have hQ := IsClosedPointTower.nil.snoc q hq hqJ
  let hE := E.isLift.isClosedPointTower hQ
  let e := J.blowupCommOfDisjoint A h ≪≫ E.iso
  have he : e.hom ≫ E.tower.toBase = A.blowupMap J.blowupToBase ≫ R.iso.hom := by
    simp [e, E.isLift.hom_toBase, toBase_snoc, toBase_nil]
  have hcomap : I.comap (T.snoc J).toBase = A.comap J.blowupToBase := by
    rw [toBase_snoc, comap_comp]
  let u := (A.comap J.blowupToBase).blowupIso (Iso.refl _) (by simpa only
    [Iso.refl_hom, comap_id] using hcomap.symm)
  have hu : u.hom ≫ (A.comap J.blowupToBase).blowupToBase =
      (I.comap (T.snoc J).toBase).blowupToBase := by simp [u]
  have hv : u.hom ≫ A.blowupMap J.blowupToBase ≫ (I.comap T.toBase).blowupToBase =
      (I.comap (T.snoc J).toBase).blowupToBase ≫ J.blowupToBase := by
    rw [A.blowupMap_blowupToBase, ← Category.assoc, hu]
  refine ⟨_, R.tower.append E.tower, R.isClosedPointTower.append hE, u ≪≫ e, ?_, ?_, ?_⟩
  · simp only [Iso.trans_hom, toBase_append, Category.assoc, reassoc_of% he, R.over_base,
      reassoc_of% hv, toBase_snoc]
  · refine Fin.lastCases ?_ (fun j ↦ ?_)
    · have hlast : (Fin.last 0).natAdd n = Fin.last n := Fin.natAdd_last
      rw [← hlast, exceptionalClass_append_natAdd, hlast,
        Iso.trans_hom, ← pullback_comp, Iso.trans_hom, ← pullback_comp,
        E.isLift.pullback_exceptionalClass, exceptionalClass_snoc_last,
        ← blowupExceptionalClass_def, exceptionalClass_snoc_last, ← blowupExceptionalClass_def,
        ← pullback_blowupExceptionalClass_blowupMap J A.blowupToBase]
      simp only [pullback_comp, blowupCommOfDisjoint_hom_blowupMap, hu]
    · have hj : j.castAdd 1 = j.castSucc := (rfl)
      have hprefix : pullback e.hom (pullback E.tower.toBase (R.tower.exceptionalClass j)) =
          pullback (A.blowupMap J.blowupToBase)
            (pullback R.iso.hom (R.tower.exceptionalClass j)) := by simp only [pullback_comp, he]
      rw [← hj, exceptionalClass_append_castAdd, hj, exceptionalClass_snoc_castSucc,
        Iso.trans_hom, ← pullback_comp, hprefix, R.exceptional]
      simp only [pullback_comp, hv]
  · intro hT j
    refine Fin.lastCases ?_ (fun l ↦ ?_) j
    · have hl : (Fin.last 0).natAdd n = Fin.last n := Fin.natAdd_last
      rw [← hl, IsClosedPointTower.baseCenter_append_natAdd R.isClosedPointTower hE,
        ← E.isLift.hom_baseCenter hQ hE, IsClosedPointTower.baseCenter_snoc_last,
        hQ.lastCenter_eq q hq hqJ, toBase_nil,
        hl, hT.baseCenter_snoc_last, hT.lastCenter_eq p hp hJ]
      have hid : (𝟙 A.blowup) q = q := (rfl)
      simpa only [Scheme.Hom.comp_apply, hid, hqp] using
        congrArg (fun a : A.blowup ⟶ X ↦ a q) R.over_base
    · have hj : l.castAdd 1 = l.castSucc := (rfl)
      rw [← hj, IsClosedPointTower.baseCenter_append_castAdd R.isClosedPointTower hE,
        hj, hT.baseCenter_snoc_castSucc]
      exact R.baseCenter _ l

private theorem exists_rebase_of_notMem_range_baseCenter (hT : IsClosedPointTower X T)
    {p : X} (hp : IsClosed ({p} : Set X)) (h : p ∉ Set.range hT.baseCenter) :
    Nonempty (Rebase J[p] T) ∧
      ∃ q : Y, IsClosed ({q} : Set Y) ∧ T.toBase q = p ∧ J[p].comap T.toBase = J[q] := by
  induction hT with
  | nil =>
    exact ⟨⟨Rebase.nil _⟩, p, hp, by simp [toBase_nil], by simp [toBase_nil]⟩
  | @snoc n W T J hT r hr hJ ih =>
    subst J
    obtain ⟨⟨R⟩, q, hq, hqp, hA⟩ := ih fun ⟨j, hj⟩ ↦
      h ⟨j.castSucc, by simpa only [baseCenter_snoc_castSucc] using hj⟩
    have hrq : r ≠ q := by
      intro heq
      apply h
      refine ⟨Fin.last n, ?_⟩
      rw [baseCenter_snoc_last, lastCenter_eq _ r hr rfl, heq, hqp]
    have hqJ : q ∉ J[r].support := by
      simpa only [← SetLike.mem_coe, Scheme.support_ker_fromSpecResidueField_of_isClosed hr,
        Set.mem_singleton_iff] using hrq.symm
    have hrA : r ∉ (J[p].comap T.toBase).support := by
      rw [hA]
      simpa only [← SetLike.mem_coe, Scheme.support_ker_fromSpecResidueField_of_isClosed hq,
        Set.mem_singleton_iff] using hrq
    have hd : Disjoint (J[r].support : Set W) ((J[p].comap T.toBase).support : Set W) := by
      rw [hA, Scheme.support_ker_fromSpecResidueField_of_isClosed hr,
        Scheme.support_ker_fromSpecResidueField_of_isClosed hq, Set.disjoint_singleton]
      exact hrq
    obtain ⟨r', hr', hrr', hJ'⟩ :=
      (J[p].comap T.toBase).exists_comap_ker_fromSpecResidueField_blowupToBase hr hrA
    obtain ⟨q', hq', hq'q, hA'⟩ :=
      J[r].exists_comap_ker_fromSpecResidueField_blowupToBase hq hqJ
    refine ⟨⟨R.snoc J[r] hd hr rfl hr' hJ' hrr'⟩,
      q', hq', ?_, ?_⟩
    · rw [toBase_snoc, Scheme.Hom.comp_apply, hq'q, hqp]
    · rw [toBase_snoc, comap_comp, hA, hA']

private theorem exists_move_last_to_front (hT : IsClosedPointTower X T)
    {p : X} (hp : IsClosed ({p} : Set X)) (h : p ∉ Set.range hT.baseCenter)
    {q : Y} (hq : T.toBase q = p) :
    ∃ (W : Scheme.{u}) (U : BlowupTower J[p].blowup n W) (e : J[q].blowup ≅ W),
      IsClosedPointTower J[p].blowup U ∧ e.hom ≫ U.toBase ≫ J[p].blowupToBase =
        (T.snoc J[q]).toBase ∧
      pullback e.hom (pullback U.toBase J[p].blowupExceptionalClass) =
        (T.snoc J[q]).exceptionalClass (Fin.last n) ∧
      ∀ i : Fin n, pullback e.hom (U.exceptionalClass i) =
        (T.snoc J[q]).exceptionalClass i.castSucc := by
  obtain ⟨⟨R⟩, r, hr, -, hI⟩ := hT.exists_rebase_of_notMem_range_baseCenter hp h
  have hqI : J[p].comap T.toBase = J[q] := by
    have hqr : q = r := by
      -- The ideal of the fiber is the ideal of the single lifted point.
      have hmem : q ∈ (J[p].comap T.toBase).support := by
        rw [support_comap, ← SetLike.mem_coe, Closeds.coe_preimage, Set.mem_preimage, hq,
          Scheme.support_ker_fromSpecResidueField_of_isClosed hp]
        exact Set.mem_singleton _
      rw [hI, ← SetLike.mem_coe, Scheme.support_ker_fromSpecResidueField_of_isClosed hr] at hmem
      exact hmem
    rwa [hqr]
  let d := (J[p].comap T.toBase).blowupIso (Iso.refl _) (by simpa using hqI)
  have hd : d.hom ≫ (J[p].comap T.toBase).blowupToBase = J[q].blowupToBase := by simp [d]
  refine ⟨_, R.tower, d ≪≫ R.iso, R.isClosedPointTower, ?_, ?_, ?_⟩
  · simp only [Iso.trans_hom, Category.assoc, R.over_base, reassoc_of% hd, toBase_snoc]
  · rw [Iso.trans_hom, ← pullback_comp, R.pullback_exceptional, exceptionalClass_snoc_last,
      ← blowupExceptionalClass_def]
    exact pullback_blowupExceptionalClass _ _ _
  · intro i
    rw [Iso.trans_hom, ← pullback_comp, R.exceptional, pullback_comp, hd,
      exceptionalClass_snoc_castSucc]

/-- Insert a blowup of a closed point absent from the projected centers of a tower.
Blowing up its inverse image on the resolved scheme gives the same refinement as
blowing it up first and carrying along the original tower. The original centers
project to the same points in the same order, and the pullback of a marked Picard
class has coefficient zero at the inserted center. -/
theorem exists_prepend_closed_point_blowup (hT : IsClosedPointTower X T)
    {p : X} (hp : IsClosed ({p} : Set X)) (h : p ∉ Set.range hT.baseCenter) :
    let I := J[p]
    let A := I.comap T.toBase
    ∃ (q : Y) (W : Scheme.{u}) (U : BlowupTower I.blowup n W) (e : A.blowup ≅ W)
      (hU : IsClosedPointTower I.blowup U),
      IsClosed ({q} : Set Y) ∧ T.toBase q = p ∧ A = J[q] ∧
      e.hom ≫ U.toBase ≫ I.blowupToBase = A.blowupToBase ≫ T.toBase ∧
      (∀ j, I.blowupToBase (hU.baseCenter j) = hT.baseCenter j) ∧
      ∀ (a : Additive (LineBundleClass X)) (x : Fin n → ℤ),
        pullback (e.inv ≫ A.blowupToBase) (T.picardHom (a, x)).toMul =
          (((BlowupTower.nil.snoc I).append U).picardHom
            (a, Fin.addCases (fun _ : Fin 1 ↦ 0) x)).toMul := by
  intro I A
  obtain ⟨⟨R⟩, q, hq, hqp, hA⟩ := hT.exists_rebase_of_notMem_range_baseCenter hp h
  refine ⟨q, _, R.tower, R.iso, R.isClosedPointTower, hq, hqp, hA, R.over_base, R.baseCenter hT, ?_⟩
  intro a x
  have hbase : (R.iso.inv ≫ A.blowupToBase) ≫ T.toBase = R.tower.toBase ≫ I.blowupToBase := by
    rw [Category.assoc, ← R.over_base, Iso.inv_hom_id_assoc]
  have hE (j : Fin n) : pullback (R.iso.inv ≫ A.blowupToBase) (T.exceptionalClass j) =
      R.tower.exceptionalClass j := by
    rw [← pullback_comp, ← R.exceptional, pullback_comp, Iso.inv_hom_id, pullback_id]
  have ha : (BlowupTower.nil.snoc I).picardHom (a, 0) =
      Additive.ofMul (pullback I.blowupToBase a.toMul) := by
    apply Additive.toMul.injective
    rw [picardHom_apply_zero, toBase_snoc, toBase_nil, Category.comp_id, toMul_ofMul]
  rw [pullback_picardHom (T := R.tower) (T' := T) hbase hE, picardHom_append]
  simp only [Fin.addCases_left, Fin.addCases_right]
  exact congrArg (fun b ↦ (R.tower.picardHom (b, x)).toMul) ha.symm

/-- Move the first center over a specified closed point to the beginning of a point tower.
The final isomorphism commutes with the projection to the base and sends the corresponding
total exceptional classes to one another. The remaining classes retain their relative order,
including those of centers infinitely near the selected point. -/
theorem exists_move_closed_point_blowup_to_front {T : BlowupTower X (n + 1) Y}
    (hT : IsClosedPointTower X T) (j : Fin (n + 1)) {p : X}
    (hp : IsClosed ({p} : Set X)) (hj : hT.baseCenter j = p)
    (hfirst : ∀ i : Fin (n + 1), i < j → hT.baseCenter i ≠ p) :
    ∃ (W : Scheme.{u}) (U : BlowupTower J[p].blowup n W) (e : Y ≅ W),
      IsClosedPointTower J[p].blowup U ∧ e.hom ≫ U.toBase ≫ J[p].blowupToBase = T.toBase ∧
      pullback e.hom (pullback U.toBase J[p].blowupExceptionalClass) = T.exceptionalClass j ∧
      ∀ i : Fin n, pullback e.hom (U.exceptionalClass i) = T.exceptionalClass (j.succAbove i) := by
  induction n generalizing Y with
  | zero =>
    cases T with
    | snoc V I =>
      obtain ⟨hV, q, hq, rfl⟩ := snoc_iff.mp hT
      have hjlast : j = Fin.last 0 := Fin.ext (by omega)
      subst j
      rw [baseCenter_snoc_last, lastCenter_eq _ q hq rfl] at hj
      simpa only [Fin.succAbove_last_apply] using
        hV.exists_move_last_to_front hp (fun ⟨i, _⟩ ↦ i.elim0) hj
  | succ n ih =>
    cases T with
    | snoc T J =>
      obtain ⟨hT', q, hq, rfl⟩ := snoc_iff.mp hT
      by_cases hjlast : j = Fin.last (n + 1)
      · subst j
        rw [baseCenter_snoc_last, lastCenter_eq _ q hq rfl] at hj
        simpa only [Fin.succAbove_last_apply] using hT'.exists_move_last_to_front hp
          (fun ⟨i, hi⟩ ↦ hfirst i.castSucc (Fin.castSucc_lt_last i)
            (by simpa only [baseCenter_snoc_castSucc] using hi)) hj
      · let j' := j.castPred hjlast
        have hcast : j'.castSucc = j := Fin.castSucc_castPred _ _
        rw [← hcast, baseCenter_snoc_castSucc] at hj
        obtain ⟨W, U, e, hU, he, hE, htail⟩ := ih hT' j' hj fun i hi ↦ by
          simpa only [baseCenter_snoc_castSucc] using
            hfirst i.castSucc (hcast ▸ Fin.castSucc_lt_castSucc_iff.mpr hi)
        let V := (BlowupTower.nil.snoc J[q]).transport e
        have hV : IsClosedPointTower W V.tower :=
          V.isLift.isClosedPointTower (.snoc .nil q hq rfl)
        have hproj : V.iso.hom ≫ V.tower.toBase = J[q].blowupToBase ≫ e.hom := by
          simp only [V.isLift.hom_toBase, toBase_snoc, toBase_nil, Category.comp_id]
        refine ⟨_, U.append V.tower, V.iso, hU.append hV, ?_, ?_, ?_⟩
        · simp only [toBase_append, Category.assoc, reassoc_of% hproj, he, toBase_snoc]
        · rw [← hcast, exceptionalClass_snoc_castSucc, ← hE, toBase_append]
          simp only [pullback_comp, reassoc_of% hproj]
        · rw [← hcast]
          refine Fin.lastCases ?_ (fun i ↦ ?_)
          · have hh : (Fin.last 0).natAdd n = Fin.last n := Fin.natAdd_last
            rw [← hh, exceptionalClass_append_natAdd, hh,
              Fin.succAbove_ne_last_last (Fin.castSucc_ne_last j'),
              V.isLift.pullback_exceptionalClass, exceptionalClass_snoc_last,
              exceptionalClass_snoc_last]
          · have hh : i.castAdd 1 = i.castSucc := (rfl)
            rw [Fin.castSucc_succAbove_castSucc, ← hh, exceptionalClass_append_castAdd,
              exceptionalClass_snoc_castSucc, pullback_comp, hproj, ← pullback_comp, htail]

end QPainleve.BlowupTower.IsClosedPointTower

namespace QPainleve.BlowupTower

/-- Moving a selected blowup to the front reindexes the full Picard marking.
The base stays fixed, and the original exceptional coefficient at `j`
comes first, followed by the other coefficients in their relative order. -/
theorem pullback_picardHom_move_to_front {X W Z : Scheme.{u}} {n : ℕ}
    (T₀ : BlowupTower X (n + 1) W) {I : X.IdealSheafData} {T₁ : BlowupTower I.blowup n Z}
    (j : Fin (n + 1)) (e : W ≅ Z)
    (he : e.hom ≫ T₁.toBase ≫ I.blowupToBase = T₀.toBase)
    (hE : pullback e.hom (pullback T₁.toBase I.blowupExceptionalClass) =
      T₀.exceptionalClass j)
    (hTail : ∀ l, pullback e.hom (T₁.exceptionalClass l) = T₀.exceptionalClass (j.succAbove l))
    (a : Additive (LineBundleClass X)) (x : Fin (n + 1) → ℤ) :
    pullback e.inv (T₀.picardHom (a, x)).toMul =
      (((nil.snoc I).append T₁).picardHom
        (a, Fin.addCases (fun _ : Fin 1 ↦ x j) (x ∘ j.succAbove))).toMul := by
  let x' : Fin (1 + n) → ℤ := Fin.addCases (fun _ : Fin 1 ↦ x j) (x ∘ j.succAbove)
  have h : pullback e.hom (((nil.snoc I).append T₁).picardHom (a, x')).toMul =
      (T₀.picardHom (a, x)).toMul := by
    rw [picardHom_append, picardHom_apply_toMul, picardHom_snoc_apply_toMul, picardHom_nil,
      picardHom_apply_toMul T₀, Fin.prod_univ_succAbove _ j]
    simp only [x', Fin.addCases_left, Fin.addCases_right, pullback_mul, pullback_zpow, mul_assoc]
    rw [pullback_comp e.hom T₁.toBase, hE,
      ← pullbackHom_apply (f := e.hom) (a := ∏ l : Fin n, _), map_prod]
    simp only [pullbackHom_apply, pullback_zpow, hTail, Function.comp_apply]
    rw [pullback_comp (e.hom ≫ T₁.toBase), Category.assoc, he]
  rw [← h, pullback_comp, Iso.inv_hom_id, pullback_id]

end QPainleve.BlowupTower
