/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
import QPainleve.AlgebraicGeometry.Blowup.Disjoint
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Blowup.Restriction

/-!
# Common refinements of closed point blowup towers

Two towers over one scheme admit extensions whose final schemes are isomorphic over the
base. A point blowup can be moved past a blowup at another point using
`Scheme.IdealSheafData.blowupCommOfDisjoint`. When the two centers coincide, the
common refinement uses the shared blowup once. Iteration treats the centers on the
successive schemes, so it includes infinitely near centers.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower

variable {X Y Z : Scheme.{u}} {m n : ℕ}

local notation "pointIdeal " p => Scheme.Hom.ker (Scheme.fromSpecResidueField _ p)

private theorem exists_common_point_blowup_refinement {p q : X}
    (hp : IsClosed ({p} : Set X)) (hq : IsClosed ({q} : Set X)) :
    ∃ (a b : ℕ) (A B : Scheme.{u})
      (L : BlowupTower (pointIdeal p).blowup a A) (R : BlowupTower (pointIdeal q).blowup b B)
      (e : A ≅ B), a ≤ 1 ∧ b ≤ 1 ∧ IsClosedPointTower _ L ∧ IsClosedPointTower _ R ∧
      L.toBase ≫ (pointIdeal p).blowupToBase = e.hom ≫ R.toBase ≫ (pointIdeal q).blowupToBase := by
  by_cases h : p = q
  · subst q
    exact ⟨0, 0, _, _, .nil, .nil, Iso.refl _, by decide, by decide,
      .nil, .nil, by simp⟩
  · let I := pointIdeal p
    let J := pointIdeal q
    have support_point (r : X) (hr : IsClosed ({r} : Set X)) :
        ((pointIdeal r).support : Set X) = {r} := by
      rw [Scheme.ker_fromSpecResidueField_eq_vanishingIdeal, coe_support_vanishingIdeal,
        Closeds.coe_mk, hr.closure_eq]
    have hIp : (I.support : Set X) = {p} := support_point p hp
    have hJq : (J.support : Set X) = {q} := support_point q hq
    have hpU : p ∈ J.support.compl := by
      rw [← SetLike.mem_coe, Closeds.coe_compl, hJq]
      exact h
    have hqU : q ∈ I.support.compl := by
      rw [← SetLike.mem_coe, Closeds.coe_compl, hIp]
      exact Ne.symm h
    obtain ⟨p', hp', -, hI⟩ :=
      J.blowupToBase.exists_comap_ker_fromSpecResidueField_of_isIso_morphismRestrict p hp _ hpU
    obtain ⟨q', hq', -, hJ⟩ :=
      I.blowupToBase.exists_comap_ker_fromSpecResidueField_of_isIso_morphismRestrict q hq _ hqU
    have hd : Disjoint (I.support : Set X) (J.support : Set X) := by
      simpa only [hIp, hJq, Set.disjoint_singleton] using h
    refine ⟨1, 1, _, _, .snoc .nil (J.comap I.blowupToBase), .snoc .nil (I.comap J.blowupToBase),
      I.blowupCommOfDisjoint J hd, le_rfl, le_rfl, .snoc .nil q' hq' hJ,
      .snoc .nil p' hp' hI, ?_⟩
    have projection {S : Scheme.{u}} (K : S.IdealSheafData) :
        (BlowupTower.nil.snoc K).toBase = K.blowupToBase := by
      rw [toBase_snoc, toBase_nil, Category.comp_id]
    rw [projection, projection, blowupCommOfDisjoint_hom_blowupToBase_assoc,
      blowupMap_blowupToBase]

private theorem exists_common_point_tower_refinement_step
    {T : BlowupTower X n Y} (hT : IsClosedPointTower X T) (hn : n ≤ 1)
    {p : X} (hp : IsClosed ({p} : Set X)) :
    ∃ (a b : ℕ) (A B : Scheme.{u}) (L : BlowupTower Y a A)
      (R : BlowupTower (pointIdeal p).blowup b B) (e : A ≅ B),
      a ≤ 1 ∧ b ≤ 1 ∧ IsClosedPointTower _ L ∧ IsClosedPointTower _ R ∧
      L.toBase ≫ T.toBase = e.hom ≫ R.toBase ≫ (pointIdeal p).blowupToBase := by
  cases hT with
  | nil =>
    exact ⟨1, 0, _, _, .snoc .nil (pointIdeal p), .nil, Iso.refl _, le_rfl, by decide,
      .snoc .nil p hp rfl, .nil, by simp [toBase_snoc, toBase_nil]⟩
  | @snoc n Y T I _ q hq hI =>
    have hn' : n = 0 := by omega
    subst n
    cases T
    subst I
    simpa [toBase_snoc, toBase_nil] using exists_common_point_blowup_refinement hq hp

/-- A tower and one blowup of its base admit a common refinement. The tower acquires
at most one new blowup, and the single blowup acquires at most the original tower's length. -/
theorem IsClosedPointTower.exists_common_refinement_point
    {T : BlowupTower X n Y} (hT : IsClosedPointTower X T) {p : X}
    (hp : IsClosed ({p} : Set X)) :
    ∃ (a b : ℕ) (A B : Scheme.{u}) (L : BlowupTower Y a A)
      (R : BlowupTower (pointIdeal p).blowup b B) (e : A ≅ B),
      a ≤ 1 ∧ b ≤ n ∧ IsClosedPointTower _ L ∧ IsClosedPointTower _ R ∧
      L.toBase ≫ T.toBase = e.hom ≫ R.toBase ≫ (pointIdeal p).blowupToBase := by
  induction hT with
  | nil =>
    exact ⟨1, 0, _, _, .snoc .nil (pointIdeal p), .nil, Iso.refl _, le_rfl, le_rfl,
      .snoc .nil p hp rfl, .nil, by simp [toBase_snoc, toBase_nil]⟩
  | @snoc n Y T J hT q hq hJ ih =>
    subst J
    obtain ⟨a, b, A, B, L, R, e, ha, hb, hL, hR, hbase⟩ := ih
    obtain ⟨c, d, C, D, L', R', f, hc, hd, hL', hR', hstep⟩ :=
      exists_common_point_tower_refinement_step hL ha hq
    let P := L'.transport e
    refine ⟨d, b + c, D, P.top, R', R.append P.tower, f.symm ≪≫ P.iso, hd,
      by omega, hR', hR.append (P.isLift.isClosedPointTower hL'), ?_⟩
    apply (cancel_epi f.hom).mp
    simp [P.isLift.hom_toBase_assoc, ← hbase, ← reassoc_of% hstep, toBase_append, toBase_snoc]

/-- Two closed point blowup towers over the same scheme admit extensions with isomorphic
final schemes over the base. Each extension has length at most that of the opposite tower. -/
theorem IsClosedPointTower.exists_common_point_tower_refinement
    {T : BlowupTower X m Y} {U : BlowupTower X n Z}
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower X U) :
    ∃ (a b : ℕ) (A B : Scheme.{u}) (L : BlowupTower Y a A)
      (R : BlowupTower Z b B) (e : A ≅ B),
      a ≤ n ∧ b ≤ m ∧ IsClosedPointTower _ L ∧ IsClosedPointTower _ R ∧
      L.toBase ≫ T.toBase = e.hom ≫ R.toBase ≫ U.toBase := by
  induction hU with
  | nil =>
    exact ⟨0, m, _, _, .nil, T, Iso.refl _, le_rfl, le_rfl, .nil, hT, by simp [toBase_nil]⟩
  | @snoc n Z U J hU p hp hJ ih =>
    subst J
    obtain ⟨a, b, A, B, L, R, e, ha, hb, hL, hR, hbase⟩ := ih
    obtain ⟨c, d, C, D, L', R', f, hc, hd, hL', hR', hstep⟩ :=
      hR.exists_common_refinement_point hp
    let P := L'.transport e.symm
    refine ⟨a + c, d, P.top, D, L.append P.tower, R', P.iso.symm ≪≫ f,
      by omega, hd.trans hb, hL.append (P.isLift.isClosedPointTower hL'), hR', ?_⟩
    apply (cancel_epi P.iso.hom).mp
    simp [P.isLift.hom_toBase_assoc, hbase, reassoc_of% hstep, toBase_append, toBase_snoc]

/-- A finite family of closed point blowup towers over one scheme admits a common
refinement by closed point blowups. The extensions commute with the maps to the base. -/
theorem exists_common_point_tower_refinement_finset
    {ι : Type*} (s : Finset ι) {n : ι → ℕ} {Y : ι → Scheme.{u}}
    (T : ∀ i, BlowupTower X (n i) (Y i))
    (hT : ∀ i ∈ s, IsClosedPointTower X (T i)) :
    ∃ (m : ℕ) (Z : Scheme.{u}) (U : BlowupTower X m Z), IsClosedPointTower X U ∧
      ∀ i ∈ s, ∃ (a : ℕ) (A : Scheme.{u}) (L : BlowupTower (Y i) a A) (e : Z ≅ A),
        IsClosedPointTower _ L ∧ U.toBase = e.hom ≫ L.toBase ≫ (T i).toBase := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, X, .nil, .nil, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨m, Z, U, hU, hprev⟩ := ih fun j hj ↦ hT j (Finset.mem_insert_of_mem hj)
    obtain ⟨a, b, A, B, L, R, e, -, -, hL, hR, hbase⟩ :=
      hU.exists_common_point_tower_refinement (hT i (Finset.mem_insert_self i s))
    refine ⟨m + a, A, U.append L, hU.append hL, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ⟨b, B, R, e, hR, (toBase_append U L).trans hbase⟩
    · obtain ⟨c, C, V, f, hV, hprev⟩ := hprev j hj
      let P := L.transport f
      refine ⟨c + a, P.top, V.append P.tower, P.iso, hV.append (P.isLift.isClosedPointTower hL), ?_⟩
      simp [P.isLift.hom_toBase_assoc, hprev, toBase_append]

end QPainleve.BlowupTower
