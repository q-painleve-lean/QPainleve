/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
import QPainleve.AlgebraicGeometry.Blowup.Disjoint
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Blowup.Restriction

/-!
# Common refinements of closed point blowup towers

Two towers over one scheme admit extensions whose final schemes are isomorphic over the
base. A point blowup can be moved past a blowup at another point using
`Scheme.IdealSheafData.blowupCommOfDisjoint`. When the two centers coincide, the
common refinement uses the shared blowup once. Iteration treats the centers on the
successive schemes, so it includes infinitely near centers. A point condition
preserved by local isomorphisms is preserved in the refinement.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower

variable {X Y Z : Scheme.{u}} {m n : ℕ}

local notation "pointIdeal " p => Scheme.Hom.ker (Scheme.fromSpecResidueField _ p)

section Local

variable {S : Scheme.{u}} {P : PointCondition S} {π : X ⟶ S}

private theorem exists_common_point_blowup_refinement (hlocal : P.IsLocal) (π : X ⟶ S) {p q : X}
    (hp : IsClosed ({p} : Set X)) (hq : IsClosed ({q} : Set X))
    (hPp : P π p) (hPq : P π q) :
    ∃ (a b : ℕ) (A B : Scheme.{u})
      (L : BlowupTower (pointIdeal p).blowup a A) (R : BlowupTower (pointIdeal q).blowup b B)
      (e : A ≅ B), a ≤ 1 ∧ b ≤ 1 ∧
      IsPointTowerWith P ((pointIdeal p).blowupToBase ≫ π) L ∧
      IsPointTowerWith P ((pointIdeal q).blowupToBase ≫ π) R ∧
      L.toBase ≫ (pointIdeal p).blowupToBase = e.hom ≫ R.toBase ≫ (pointIdeal q).blowupToBase := by
  by_cases h : p = q
  · subst q
    exact ⟨0, 0, _, _, .nil, .nil, Iso.refl _, by decide, by decide,
      .nil, .nil, by simp⟩
  · let I := pointIdeal p
    let J := pointIdeal q
    have hIp : (I.support : Set X) = {p} := Scheme.support_ker_fromSpecResidueField_of_isClosed hp
    have hJq : (J.support : Set X) = {q} := Scheme.support_ker_fromSpecResidueField_of_isClosed hq
    have hpU : p ∈ J.support.compl := by
      rw [← SetLike.mem_coe, Closeds.coe_compl, hJq]
      exact h
    have hqU : q ∈ I.support.compl := by
      rw [← SetLike.mem_coe, Closeds.coe_compl, hIp]
      exact Ne.symm h
    obtain ⟨p', hp', hpp', hI⟩ :=
      J.exists_comap_ker_fromSpecResidueField_blowupToBase hp hpU
    obtain ⟨q', hq', hqq', hJ⟩ :=
      I.exists_comap_ker_fromSpecResidueField_blowupToBase hq hqU
    have hIiso : I.support.compl ≤ I.blowupToBase.isoLocus :=
      I.blowupToBase.le_isoLocus_iff.mpr inferInstance
    have hJiso : J.support.compl ≤ J.blowupToBase.isoLocus :=
      J.blowupToBase.le_isoLocus_iff.mpr inferInstance
    have hqP := hlocal.pullback I.blowupToBase π q' (hqq'.symm ▸ hIiso hqU) (hqq'.symm ▸ hPq)
    have hpP := hlocal.pullback J.blowupToBase π p' (hpp'.symm ▸ hJiso hpU) (hpp'.symm ▸ hPp)
    have hd : Disjoint (I.support : Set X) (J.support : Set X) := by
      simpa only [hIp, hJq, Set.disjoint_singleton] using h
    refine ⟨1, 1, _, _, .snoc .nil (J.comap I.blowupToBase), .snoc .nil (I.comap J.blowupToBase),
      I.blowupCommOfDisjoint J hd, le_rfl, le_rfl,
      .snoc .nil q' hq' hJ (by rw [toBase_nil, Category.id_comp]; exact hqP),
      .snoc .nil p' hp' hI (by rw [toBase_nil, Category.id_comp]; exact hpP), ?_⟩
    have projection {S : Scheme.{u}} (K : S.IdealSheafData) :
        (BlowupTower.nil.snoc K).toBase = K.blowupToBase := by
      rw [toBase_snoc, toBase_nil, Category.comp_id]
    rw [projection, projection, blowupCommOfDisjoint_hom_blowupToBase_assoc,
      blowupMap_blowupToBase]

private theorem exists_common_point_tower_refinement_step
    {T : BlowupTower X n Y} (hT : IsPointTowerWith P π T) (hlocal : P.IsLocal) (hn : n ≤ 1)
    {p : X} (hp : IsClosed ({p} : Set X)) (hPp : P π p) :
    ∃ (a b : ℕ) (A B : Scheme.{u}) (L : BlowupTower Y a A)
      (R : BlowupTower (pointIdeal p).blowup b B) (e : A ≅ B),
      a ≤ 1 ∧ b ≤ 1 ∧ IsPointTowerWith P (T.toBase ≫ π) L ∧
      IsPointTowerWith P ((pointIdeal p).blowupToBase ≫ π) R ∧
      L.toBase ≫ T.toBase = e.hom ≫ R.toBase ≫ (pointIdeal p).blowupToBase := by
  cases hT with
  | nil =>
    exact ⟨1, 0, _, _, .snoc .nil (pointIdeal p), .nil, Iso.refl _, le_rfl, by decide,
      .snoc .nil p hp rfl (by simpa only [toBase_nil, Category.id_comp] using hPp), .nil,
      by simp [toBase_snoc, toBase_nil]⟩
  | @snoc n Y T I _ q hq hI hPq =>
    have hn' : n = 0 := by omega
    subst n
    cases T
    subst I
    simp only [toBase_nil, Category.id_comp] at hPq
    simpa only [toBase_snoc, toBase_nil, Category.comp_id] using
      exists_common_point_blowup_refinement hlocal π hq hp hPq hPp

/-- A tower and one blowup of its base admit a common refinement. The tower acquires
at most one new blowup, and the single blowup acquires at most the original tower's length. -/
theorem IsPointTowerWith.exists_common_refinement_point
    {T : BlowupTower X n Y} (hT : IsPointTowerWith P π T) (hlocal : P.IsLocal) {p : X}
    (hp : IsClosed ({p} : Set X)) (hPp : P π p) :
    ∃ (a b : ℕ) (A B : Scheme.{u}) (L : BlowupTower Y a A)
      (R : BlowupTower (pointIdeal p).blowup b B) (e : A ≅ B),
      a ≤ 1 ∧ b ≤ n ∧ IsPointTowerWith P (T.toBase ≫ π) L ∧
      IsPointTowerWith P ((pointIdeal p).blowupToBase ≫ π) R ∧
      L.toBase ≫ T.toBase = e.hom ≫ R.toBase ≫ (pointIdeal p).blowupToBase := by
  induction hT with
  | nil =>
    exact ⟨1, 0, _, _, .snoc .nil (pointIdeal p), .nil, Iso.refl _, le_rfl, le_rfl,
      .snoc .nil p hp rfl (by simpa only [toBase_nil, Category.id_comp] using hPp), .nil,
      by simp [toBase_snoc, toBase_nil]⟩
  | @snoc n Y T J hT q hq hJ hPq ih =>
    subst J
    obtain ⟨a, b, A, B, L, R, e, ha, hb, hL, hR, hbase⟩ := ih
    obtain ⟨c, d, C, D, L', R', f, hc, hd, hL', hR', hstep⟩ :=
      exists_common_point_tower_refinement_step hL hlocal ha hq hPq
    let V := L'.transport e
    have hcomm :
        e.hom ≫ (R.toBase ≫ (pointIdeal p).blowupToBase ≫ π) = L.toBase ≫ T.toBase ≫ π := by
      simpa only [Category.assoc] using congrArg (· ≫ π) hbase.symm
    refine ⟨d, b + c, D, V.top, R', R.append V.tower, f.symm ≪≫ V.iso, hd,
      by omega, ?_, hR.append (V.isLift.isPointTowerWith hlocal hcomm hL'), ?_⟩
    · simpa only [toBase_snoc, Category.assoc] using hR'
    · apply (cancel_epi f.hom).mp
      simp [V.isLift.hom_toBase_assoc, ← hbase, ← reassoc_of% hstep, toBase_append, toBase_snoc]

/-- Two point towers satisfying a local condition admit a common refinement whose new
centers satisfy the same condition. Each extension is no longer than the opposite tower. -/
theorem IsPointTowerWith.exists_common_point_tower_refinement
    {T : BlowupTower X m Y} {U : BlowupTower X n Z}
    (hT : IsPointTowerWith P π T) (hU : IsPointTowerWith P π U) (hlocal : P.IsLocal) :
    ∃ (a b : ℕ) (A B : Scheme.{u}) (L : BlowupTower Y a A)
      (R : BlowupTower Z b B) (e : A ≅ B),
      a ≤ n ∧ b ≤ m ∧ IsPointTowerWith P (T.toBase ≫ π) L ∧
      IsPointTowerWith P (U.toBase ≫ π) R ∧
      L.toBase ≫ T.toBase = e.hom ≫ R.toBase ≫ U.toBase := by
  induction hU with
  | nil =>
    exact ⟨0, m, _, _, .nil, T, Iso.refl _, le_rfl, le_rfl, .nil,
      by simpa only [toBase_nil, Category.id_comp] using hT, by simp [toBase_nil]⟩
  | @snoc n Z U J hU p hp hJ hPp ih =>
    subst J
    obtain ⟨a, b, A, B, L, R, e, ha, hb, hL, hR, hbase⟩ := ih
    obtain ⟨c, d, C, D, L', R', f, hc, hd, hL', hR', hstep⟩ :=
      hR.exists_common_refinement_point hlocal hp hPp
    let V := L'.transport e.symm
    have hcomm : e.inv ≫ (L.toBase ≫ T.toBase ≫ π) = R.toBase ≫ U.toBase ≫ π := by
      rw [reassoc_of% hbase, Iso.inv_hom_id_assoc]
    refine ⟨a + c, d, V.top, D, L.append V.tower, R', V.iso.symm ≪≫ f,
      by omega, hd.trans hb, hL.append (V.isLift.isPointTowerWith hlocal hcomm hL'), ?_, ?_⟩
    · simpa only [toBase_snoc, Category.assoc] using hR'
    · apply (cancel_epi V.iso.hom).mp
      simp [V.isLift.hom_toBase_assoc, hbase, reassoc_of% hstep, toBase_append, toBase_snoc]

/-- A finite family of point towers satisfying a local condition has a common refinement
by point blowups satisfying the same condition on the successive models. -/
theorem IsPointTowerWith.exists_common_point_tower_refinement_finset
    {ι : Type*} (s : Finset ι) {n : ι → ℕ} {Y : ι → Scheme.{u}}
    (T : ∀ i, BlowupTower X (n i) (Y i))
    (hT : ∀ i ∈ s, IsPointTowerWith P π (T i)) (hlocal : P.IsLocal) :
    ∃ (m : ℕ) (Z : Scheme.{u}) (U : BlowupTower X m Z), IsPointTowerWith P π U ∧
      ∀ i ∈ s, ∃ (a : ℕ) (A : Scheme.{u}) (L : BlowupTower (Y i) a A) (e : Z ≅ A),
        IsPointTowerWith P ((T i).toBase ≫ π) L ∧ U.toBase = e.hom ≫ L.toBase ≫ (T i).toBase := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, X, .nil, .nil, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨m, Z, U, hU, hprev⟩ := ih fun j hj ↦ hT j (Finset.mem_insert_of_mem hj)
    obtain ⟨a, b, A, B, L, R, e, -, -, hL, hR, hbase⟩ :=
      hU.exists_common_point_tower_refinement (hT i (Finset.mem_insert_self i s)) hlocal
    refine ⟨m + a, A, U.append L, hU.append hL, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ⟨b, B, R, e, hR, (toBase_append U L).trans hbase⟩
    · obtain ⟨c, C, V, f, hV, hprev⟩ := hprev j hj
      let E := L.transport f
      have hcomm : f.hom ≫ (V.toBase ≫ (T j).toBase ≫ π) = U.toBase ≫ π := by
        simpa only [Category.assoc] using congrArg (· ≫ π) hprev.symm
      refine ⟨c + a, E.top, V.append E.tower, E.iso,
        hV.append (E.isLift.isPointTowerWith hlocal hcomm hL), ?_⟩
      simp [E.isLift.hom_toBase_assoc, hprev, toBase_append]

end Local

end QPainleve.BlowupTower
