/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField

/-!
# Local conditions on the centers of blowup towers

A point-centered blowup tower can impose a condition on each center, using the
map of its current scheme to a fixed base. Conditions preserved by local
isomorphisms can be transported along lifts of tower isomorphisms.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace QPainleve.BlowupTower

variable {S X Y Z X' Y' : Scheme.{u}} {m n : ℕ}

namespace IsClosedPointTower

/-- The image on the base of the center with the given index in a closed point tower. -/
noncomputable def baseCenter :
    {n : ℕ} → {Y : Scheme.{u}} → {T : BlowupTower X n Y} → IsClosedPointTower X T → Fin n → X
  | _, _, .nil, _ => Fin.elim0
  | _, _, .snoc U _, hT => Fin.lastCases (U.toBase hT.lastCenter.val)
      (baseCenter (snoc_iff.mp hT).1)
termination_by structural _ _ T => T

/-- Appending a blowup preserves the base images of all previous centers. -/
@[simp]
theorem baseCenter_snoc_castSucc {T : BlowupTower X n Y} {I : Y.IdealSheafData}
    (hT : IsClosedPointTower X (T.snoc I)) (j : Fin n) :
    hT.baseCenter j.castSucc = (snoc_iff.mp hT).1.baseCenter j := by
  simp [baseCenter]

/-- The last center is mapped to the base by the projection of the preceding tower. -/
@[simp]
theorem baseCenter_snoc_last {T : BlowupTower X n Y} {I : Y.IdealSheafData}
    (hT : IsClosedPointTower X (T.snoc I)) :
    hT.baseCenter (Fin.last n) = T.toBase hT.lastCenter.val := by
  simp [baseCenter]

/-- Appending a tower leaves the projected centers in the prefix unchanged. -/
@[simp]
theorem baseCenter_append_castAdd {T : BlowupTower X m Y} {U : BlowupTower Y n Z}
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Y U) (j : Fin m) :
    (hT.append hU).baseCenter (j.castAdd n) = hT.baseCenter j := by
  induction hU with
  | nil => simp
  | snoc _ _ _ _ ih =>
    simpa only [← Fin.castSucc_castAdd, append_snoc, baseCenter_snoc_castSucc] using ih

/-- The projected center of a tail step is the image of that step's center on the
intermediate base. -/
theorem baseCenter_append_natAdd {T : BlowupTower X m Y} {U : BlowupTower Y n Z}
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Y U) (j : Fin n) :
    (hT.append hU).baseCenter (j.natAdd m) = T.toBase (hU.baseCenter j) := by
  induction hU with
  | nil => exact j.elim0
  | @snoc n Z U I hU p hp hI ih =>
    refine Fin.lastCases ?_ (fun l ↦ ?_) j
    · rw [Fin.natAdd_last]
      simp only [append_snoc, baseCenter_snoc_last, lastCenter_eq _ p hp hI, toBase_append,
        Scheme.Hom.comp_apply]
    · simpa only [Fin.natAdd_castSucc, append_snoc, baseCenter_snoc_castSucc] using ih l

/-- On a locally Noetherian base, every projected center is a closed point. -/
theorem isClosed_baseCenter [IsLocallyNoetherian X] {T : BlowupTower X n Y}
    (hT : IsClosedPointTower X T) (j : Fin n) : IsClosed ({hT.baseCenter j} : Set X) := by
  induction hT with
  | nil => exact j.elim0
  | @snoc n Y T I hT q hq hI ih =>
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · rw [baseCenter_snoc_last, lastCenter_eq _ q hq hI]
      have := T.isProper_toBase
      simpa only [Set.image_singleton] using T.toBase.isClosedMap _ hq
    · simpa only [baseCenter_snoc_castSucc] using ih i

/-- A closed-point tower is injective above the complement of the projected centers. -/
theorem injOn_toBase_compl_range_baseCenter {T : BlowupTower X n Y}
    (hT : IsClosedPointTower X T) :
    Set.InjOn T.toBase (T.toBase ⁻¹' (Set.range hT.baseCenter)ᶜ) := by
  induction hT with
  | nil =>
    rw [toBase_nil]
    exact Function.injective_id.injOn
  | @snoc d W U I hU p hp hI ih =>
    intro x hx y hy hxy
    have hsupport : (I.support : Set W) = {p} :=
      (congrArg (fun J : W.IdealSheafData ↦ (J.support : Set W)) hI).trans
        (W.support_ker_fromSpecResidueField_of_isClosed hp)
    have hprev (z : I.blowup) (hz : (U.snoc I).toBase z ∉
        Set.range (hU.snoc p hp hI).baseCenter) :
        U.toBase (I.blowupToBase z) ∉ Set.range hU.baseCenter := by
      rintro ⟨j, hj⟩
      apply hz
      exact ⟨j.castSucc, by simpa only [baseCenter_snoc_castSucc, toBase_snoc,
        Scheme.Hom.comp_apply] using hj⟩
    have hstep (z : I.blowup) (hz : (U.snoc I).toBase z ∉
        Set.range (hU.snoc p hp hI).baseCenter) :
        I.blowupToBase z ∉ I.support := by
      rw [← SetLike.mem_coe, hsupport]
      intro hz'
      apply hz
      refine ⟨Fin.last d, ?_⟩
      rw [baseCenter_snoc_last, lastCenter_eq _ p hp hI, toBase_snoc, Scheme.Hom.comp_apply,
        Set.mem_singleton_iff.mp hz']
    apply I.injOn_blowupToBase_compl_support (hstep x hx) (hstep y hy)
    exact ih (hprev x hx) (hprev y hy) (by simpa only [toBase_snoc,
      Scheme.Hom.comp_apply] using hxy)

end IsClosedPointTower

/-- A condition on a point of a scheme over a fixed base. -/
abbrev PointCondition (S : Scheme.{u}) :=
  ∀ ⦃W : Scheme.{u}⦄, (W ⟶ S) → W → Prop

/-- A point condition transports backwards along a morphism at points lying over its
isomorphism locus. -/
structure PointCondition.IsLocal (P : PointCondition S) : Prop where
  /-- Pull back the condition to a point lying over the isomorphism locus. -/
  pullback ⦃A B : Scheme.{u}⦄ (f : A ⟶ B) (g : B ⟶ S) (x : A) :
    f x ∈ f.isoLocus → P g (f x) → P (f ≫ g) x

/-- The centers of a closed point tower satisfy `P` on their successive schemes over `S`. -/
inductive IsPointTowerWith (P : PointCondition S) (π : X ⟶ S) :
    {n : ℕ} → {Y : Scheme.{u}} → BlowupTower X n Y → Prop
  /-- The empty tower has no centers. -/
  | nil : IsPointTowerWith P π .nil
  /-- Append the blowup of a reduced closed point satisfying the point condition. -/
  | snoc {n : ℕ} {Y : Scheme.{u}} {T : BlowupTower X n Y} {I : Y.IdealSheafData}
      (hT : IsPointTowerWith P π T) (p : Y) (hp : IsClosed ({p} : Set Y))
      (hI : I = (Y.fromSpecResidueField p).ker) (hP : P (T.toBase ≫ π) p) :
      IsPointTowerWith P π (T.snoc I)

namespace IsPointTowerWith

variable {P : PointCondition S} {π : X ⟶ S} {T : BlowupTower X n Y}

/-- Every tower with a center condition is a closed point tower. -/
theorem isClosedPointTower (hT : IsPointTowerWith P π T) : IsClosedPointTower X T := by
  induction hT with
  | nil => exact .nil
  | snoc _ p hp hI _ ih => exact ih.snoc p hp hI

/-- A center condition on the successive schemes is preserved when appending compatible towers. -/
protected theorem append {U : BlowupTower Y m Z} (hT : IsPointTowerWith P π T)
    (hU : IsPointTowerWith P (T.toBase ≫ π) U) : IsPointTowerWith P π (T.append U) := by
  induction hU with
  | nil => simpa only [append_nil] using hT
  | snoc _ p hp hI hP ih =>
    rw [append_snoc]
    exact ih.snoc p hp hI (by simpa only [toBase_append, Category.assoc] using hP)

/-- A nonempty tower satisfies the center condition exactly when its prefix does and its
last center is a reduced closed point satisfying the condition. -/
theorem snoc_iff {I : Y.IdealSheafData} :
    IsPointTowerWith P π (T.snoc I) ↔ IsPointTowerWith P π T ∧
      ∃ p : Y, IsClosed ({p} : Set Y) ∧ I = (Y.fromSpecResidueField p).ker ∧
        P (T.toBase ≫ π) p := by
  constructor
  · have step {d : ℕ} {W : Scheme.{u}} {U : BlowupTower X d W}
        (hU : IsPointTowerWith P π U) :
        match U with
        | .nil => IsPointTowerWith P π .nil
        | .snoc V J => IsPointTowerWith P π V ∧
            ∃ p : _, IsClosed {p} ∧ J = (Scheme.fromSpecResidueField _ p).ker ∧
              P (V.toBase ≫ π) p := by
      cases hU with
      | nil => exact .nil
      | snoc hV p hp hJ hP => exact ⟨hV, p, hp, hJ, hP⟩
    exact fun h ↦ step h
  · rintro ⟨hT, p, hp, hI, hP⟩
    exact hT.snoc p hp hI hP

end IsPointTowerWith

/-- An unconditional center condition agrees with the ordinary closed point condition. -/
theorem IsClosedPointTower.isPointTowerWith_true {T : BlowupTower X n Y}
    (hT : IsClosedPointTower X T) (π : X ⟶ S) :
    IsPointTowerWith (fun {_} _ _ ↦ True) π T := by
  induction hT with
  | nil => exact .nil
  | snoc _ p hp hI ih => exact ih.snoc p hp hI trivial

/-- A tower lift over the fixed base preserves a local condition on the centers. -/
theorem IsLift.isPointTowerWith {T : BlowupTower X n Y} {U : BlowupTower X' n Y'}
    {e : X ≅ X'} {g : Y ≅ Y'} (h : IsLift e T U g)
    {P : PointCondition S} (hP : P.IsLocal) {π : X ⟶ S} {π' : X' ⟶ S}
    (he : e.hom ≫ π' = π) (hT : IsPointTowerWith P π T) :
    IsPointTowerWith P π' U := by
  induction hT generalizing Y' with
  | nil => cases U; exact .nil
  | @snoc m Y T I hT p hp hI hTp ih =>
    cases U with
    | snoc U J =>
      obtain ⟨f, hf, hJ, -⟩ := IsLift.snoc_iff.mp h
      have hcomap : I.comap f.inv = J := by
        rw [← hJ, ← Scheme.IdealSheafData.comap_comp, f.inv_hom_id, Scheme.IdealSheafData.comap_id]
      obtain ⟨q, hq, hqp, hqJ⟩ :=
        f.inv.exists_comap_ker_fromSpecResidueField_of_isIso_morphismRestrict p hp ⊤ (by simp)
      have hbase : f.inv ≫ T.toBase ≫ π = U.toBase ≫ π' := by
        rw [← he, ← Category.assoc T.toBase, ← hf.hom_toBase, Category.assoc, Iso.inv_hom_id_assoc]
      have hlocal := hP.pullback f.inv (T.toBase ≫ π) q
        (by rw [f.inv.isoLocus_eq_top_iff.mpr inferInstance]; trivial) (hqp.symm ▸ hTp)
      exact (ih hf).snoc q hq (hcomap.symm.trans (hI ▸ hqJ)) (hbase ▸ hlocal)

/-- A lift of an isomorphism carries the projected centers in their given order. -/
theorem IsLift.hom_baseCenter {T : BlowupTower X n Y} {U : BlowupTower X' n Y'}
    {e : X ≅ X'} {g : Y ≅ Y'} (h : IsLift e T U g)
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower X' U) (j : Fin n) :
    e.hom (hT.baseCenter j) = hU.baseCenter j := by
  induction hT generalizing Y' with
  | nil => exact j.elim0
  | @snoc m Y T I hT p hp hI ih =>
    cases U with
    | snoc U J =>
      obtain ⟨f, hf, hI', -⟩ := IsLift.snoc_iff.mp h
      refine Fin.lastCases ?_ (fun l ↦ ?_) j
      · have hJ : I.map f.hom = J := by
          rw [← hI', Scheme.IdealSheafData.map_comap_of_isClosedImmersion,
            f.hom.ker_eq_bot_of_isIso, sup_bot_eq]
        have hq : hU.lastCenter.val = f.hom p := by
          apply Scheme.ker_fromSpecResidueField_inj.mp
          rw [← hU.lastCenter.property.2, ← f.hom.map_ker_fromSpecResidueField, ← hI, hJ]
        rw [IsClosedPointTower.baseCenter_snoc_last, hU.baseCenter_snoc_last,
          IsClosedPointTower.lastCenter_eq _ p hp hI, hq]
        exact congrArg (fun a : Y ⟶ X' ↦ a p) hf.hom_toBase.symm
      · simpa only [IsClosedPointTower.baseCenter_snoc_castSucc] using
          ih hf (IsClosedPointTower.snoc_iff.mp hU).1 l

end QPainleve.BlowupTower
