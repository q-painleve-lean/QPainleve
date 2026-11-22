/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Isomorphism
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Ordered towers of blowups

Each stage of a tower blows up an ideal on the current scheme. A lift of an isomorphism
through two towers matches these ideals by scheme-theoretic inverse image at every stage.
The lifted isomorphism respects the projection to the base and pulls back each ordered
exceptional class to its counterpart. Exceptional classes from earlier stages are taken
with their full pullbacks, as needed when a later center lies on an earlier exceptional
divisor. The class comparison uses Tau Ceti's
`IsEffectiveCartier.pullback_mk_toInvertibleSheaf` for the newly formed exceptional divisor.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

universe u

namespace QPainleve

/-- An ordered sequence of `n` native blowups from the final scheme to the fixed base `X`.
Each center is an ideal sheaf on the scheme produced by the preceding stages. -/
inductive BlowupTower (X : Scheme.{u}) : ℕ → Scheme.{u} → Type (u + 1)
  /-- The empty tower on the base scheme. -/
  | nil : BlowupTower X 0 X
  /-- Blow up a center on the current final scheme. -/
  | snoc {n : ℕ} {Y : Scheme.{u}} (T : BlowupTower X n Y) (I : Y.IdealSheafData) :
      BlowupTower X (n + 1) I.blowup

namespace BlowupTower

variable {X Y Z X' Y' Z' : Scheme.{u}} {m n : ℕ}

/-- The composite projection from the final scheme to the base of the tower. -/
def toBase : {n : ℕ} → {Y : Scheme.{u}} → BlowupTower X n Y → (Y ⟶ X)
  | _, _, .nil => 𝟙 X
  | _, _, .snoc T I => I.blowupToBase ≫ T.toBase

@[simp]
theorem toBase_nil : (nil (X := X)).toBase = 𝟙 X := (rfl)

@[simp]
theorem toBase_snoc (T : BlowupTower X n Y) (I : Y.IdealSheafData) :
    (T.snoc I).toBase = I.blowupToBase ≫ T.toBase := (rfl)

/-- Concatenate two towers by performing the blowups of the second after those of the first. -/
def append (T : BlowupTower X m Y) :
    {n : ℕ} → {Z : Scheme.{u}} → BlowupTower Y n Z → BlowupTower X (m + n) Z
  | _, _, .nil => T
  | _, _, .snoc U I => (T.append U).snoc I

@[simp]
theorem append_nil (T : BlowupTower X n Y) : T.append nil = T := (rfl)

@[simp]
theorem append_snoc (T : BlowupTower X m Y) (U : BlowupTower Y n Z) (I : Z.IdealSheafData) :
    T.append (U.snoc I) = (T.append U).snoc I := (rfl)

/-- The projection of the concatenated tower is the composite of its two projections. -/
@[simp]
theorem toBase_append (T : BlowupTower X m Y) (U : BlowupTower Y n Z) :
    (T.append U).toBase = U.toBase ≫ T.toBase := by
  induction U with
  | nil => simp
  | snoc U I ih => simp [ih, Category.assoc]

/-- The class of the exceptional divisor of a stage, pulled back to the final scheme. The
stage order numbers the first blowup by zero. The inverse of the exceptional ideal's line
bundle class gives the positive divisor class. -/
def exceptionalClass :
    {n : ℕ} → {Y : Scheme.{u}} → BlowupTower X n Y → Fin n → LineBundleClass Y
  | _, _, .nil => Fin.elim0
  | _, _, .snoc T I => Fin.lastCases
      (LineBundleClass.mk I.isEffectiveCartier_comap_blowupToBase.toInvertibleSheaf)⁻¹
      (fun i ↦ LineBundleClass.pullback I.blowupToBase (T.exceptionalClass i))

/-- At the last index, the marking is the class of the new exceptional divisor. -/
@[simp]
theorem exceptionalClass_snoc_last (T : BlowupTower X n Y) (I : Y.IdealSheafData) :
    (T.snoc I).exceptionalClass (Fin.last n) =
      (LineBundleClass.mk I.isEffectiveCartier_comap_blowupToBase.toInvertibleSheaf)⁻¹ := by
  simp [exceptionalClass]

/-- At each earlier index, the marking pulls back along the last projection. -/
@[simp]
theorem exceptionalClass_snoc_castSucc (T : BlowupTower X n Y) (I : Y.IdealSheafData)
    (i : Fin n) :
    (T.snoc I).exceptionalClass i.castSucc =
      LineBundleClass.pullback I.blowupToBase (T.exceptionalClass i) := by
  simp [exceptionalClass]

/-- The exceptional classes from the first tower pull back along the second tower. -/
@[simp]
theorem exceptionalClass_append_castAdd (T : BlowupTower X m Y) (U : BlowupTower Y n Z)
    (i : Fin m) :
    (T.append U).exceptionalClass (i.castAdd n) =
      LineBundleClass.pullback U.toBase (T.exceptionalClass i) := by
  induction U with
  | nil => simp
  | snoc U I ih =>
    rw [append_snoc, ← Fin.castSucc_castAdd, exceptionalClass_snoc_castSucc, ih,
      LineBundleClass.pullback_comp, toBase_snoc]

/-- The exceptional classes from the second tower already live on the final scheme. -/
@[simp]
theorem exceptionalClass_append_natAdd (T : BlowupTower X m Y) (U : BlowupTower Y n Z)
    (i : Fin n) : (T.append U).exceptionalClass (i.natAdd m) = U.exceptionalClass i := by
  induction U with
  | nil => exact Fin.elim0 i
  | snoc U I ih =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [append_snoc, Fin.natAdd_last, exceptionalClass_snoc_last, exceptionalClass_snoc_last]
    · rw [append_snoc, Fin.natAdd_castSucc, exceptionalClass_snoc_castSucc,
        exceptionalClass_snoc_castSucc, ih]

/-- An isomorphism between the final schemes lifts the base isomorphism through the two ordered
towers when it arises by matching the center ideals and taking the induced isomorphism at
each step. -/
def IsLift (e : X ≅ X') :
    {n : ℕ} → {Y Y' : Scheme.{u}} →
      BlowupTower X n Y → BlowupTower X' n Y' → (Y ≅ Y') → Prop
  | _, _, _, .nil, .nil, g => g = e
  | _, _, _, .snoc T I, .snoc T' I', g =>
    ∃ (f : _ ≅ _) (_ : IsLift e T T' f) (hI : I'.comap f.hom = I), g = I'.blowupIso f hI

namespace IsLift

variable {T : BlowupTower X n Y} {T' : BlowupTower X' n Y'} {e : X ≅ X'} {g : Y ≅ Y'}

/-- Over empty towers the lift is the base isomorphism. -/
@[simp]
theorem nil_iff {g : X ≅ X'} : IsLift e nil nil g ↔ g = e := (Iff.rfl)

/-- Over nonempty towers a lift identifies the last centers over the lift on the preceding
stages and equals the induced isomorphism of the last blowups. -/
theorem snoc_iff {I : Y.IdealSheafData} {I' : Y'.IdealSheafData} {k : I.blowup ≅ I'.blowup} :
    IsLift e (T.snoc I) (T'.snoc I') k ↔
      ∃ (f : Y ≅ Y') (_ : IsLift e T T' f) (hI : I'.comap f.hom = I),
        k = I'.blowupIso f hI := (Iff.rfl)

/-- Extend a lift by blowing up matching scheme-theoretic centers. -/
theorem snoc (h : IsLift e T T' g) {I : Y.IdealSheafData} {I' : Y'.IdealSheafData}
    (hI : I'.comap g.hom = I) : IsLift e (T.snoc I) (T'.snoc I') (I'.blowupIso g hI) :=
  snoc_iff.mpr ⟨g, h, hI, rfl⟩

/-- An isomorphism lifting through the towers commutes with their projections. -/
@[reassoc]
theorem hom_toBase (h : IsLift e T T' g) : g.hom ≫ T'.toBase = T.toBase ≫ e.hom := by
  induction T generalizing Y' with
  | nil => cases T'; simp_all
  | snoc T I ih =>
    cases T' with
    | snoc T' I' =>
      obtain ⟨f, hf, hI, rfl⟩ := snoc_iff.mp h
      rw [toBase_snoc, toBase_snoc, Scheme.IdealSheafData.blowupIso_hom_blowupToBase_assoc,
        Category.assoc, ih hf]

/-- The induced Picard pullbacks commute with pullback from the base schemes. -/
theorem pullbackHom_toBase (h : IsLift e T T' g) :
    (LineBundleClass.pullbackHom g.hom).comp (LineBundleClass.pullbackHom T'.toBase) =
      (LineBundleClass.pullbackHom T.toBase).comp (LineBundleClass.pullbackHom e.hom) := by
  simp only [LineBundleClass.pullbackHom_comp, h.hom_toBase]

/-- The identity isomorphism lifts through any tower. -/
protected theorem refl (T : BlowupTower X n Y) : IsLift (Iso.refl X) T T (Iso.refl Y) := by
  induction T with
  | nil => simp
  | snoc T I ih => simpa using ih.snoc I.comap_id

/-- Interchanging the towers inverts both the base isomorphism and its lift. -/
protected theorem symm (h : IsLift e T T' g) : IsLift e.symm T' T g.symm := by
  induction T generalizing Y' with
  | nil => cases T'; simp_all
  | snoc T I ih =>
    cases T' with
    | snoc T' I' =>
      obtain ⟨f, hf, hI, rfl⟩ := snoc_iff.mp h
      have hI' : I.comap f.inv = I' := by
        rw [← hI, ← Scheme.IdealSheafData.comap_comp, f.inv_hom_id,
          Scheme.IdealSheafData.comap_id]
      rw [Scheme.IdealSheafData.blowupIso_symm]
      exact (ih hf).snoc hI'

/-- Center-preserving lifts through towers compose stage by stage. -/
protected theorem trans {X'' Y'' : Scheme.{u}} {T'' : BlowupTower X'' n Y''}
    {e' : X' ≅ X''} {g' : Y' ≅ Y''} (h : IsLift e T T' g) (h' : IsLift e' T' T'' g') :
    IsLift (e ≪≫ e') T T'' (g ≪≫ g') := by
  induction T generalizing Y' Y'' with
  | nil => cases T'; cases T''; simp_all
  | snoc T I ih =>
    cases T' with
    | snoc T' I' =>
      cases T'' with
      | snoc T'' I'' =>
        obtain ⟨f, hf, hI, rfl⟩ := snoc_iff.mp h
        obtain ⟨f', hf', hI', rfl⟩ := snoc_iff.mp h'
        rw [Scheme.IdealSheafData.blowupIso_trans]
        exact (ih hf hf').snoc (by
          rw [Iso.trans_hom, Scheme.IdealSheafData.comap_comp, hI', hI])

/-- For fixed towers and a fixed base isomorphism, the center-preserving lift is unique. -/
theorem unique (h : IsLift e T T' g) {g' : Y ≅ Y'} (h' : IsLift e T T' g') : g = g' := by
  induction T generalizing Y' with
  | nil => cases T'; simp_all
  | snoc T I ih =>
    cases T' with
    | snoc T' I' =>
      obtain ⟨f, hf, hI, rfl⟩ := snoc_iff.mp h
      obtain ⟨f', hf', hI', rfl⟩ := snoc_iff.mp h'
      cases ih hf hf'
      rfl

/-- Lifts through consecutive towers also lift through their concatenation. -/
theorem append {U : BlowupTower Y m Z} {U' : BlowupTower Y' m Z'} {k : Z ≅ Z'}
    (h : IsLift e T T' g) (h' : IsLift g U U' k) :
    IsLift e (T.append U) (T'.append U') k := by
  induction U generalizing Z' with
  | nil =>
    cases U'
    simpa [nil_iff.mp h'] using h
  | snoc U I ih =>
    cases U' with
    | snoc U' I' =>
      obtain ⟨f, hf, hI, rfl⟩ := snoc_iff.mp h'
      simpa only [append_snoc] using (ih hf).snoc hI

/-- Pullback along the lift preserves the full transform of each exceptional class. -/
theorem pullback_exceptionalClass (h : IsLift e T T' g) (i : Fin n) :
    LineBundleClass.pullback g.hom (T'.exceptionalClass i) = T.exceptionalClass i := by
  induction T generalizing Y' with
  | nil => exact Fin.elim0 i
  | snoc T I ih =>
    cases T' with
    | snoc T' I' =>
      obtain ⟨f, hf, hI, rfl⟩ := snoc_iff.mp h
      let k := I'.blowupIso f hI
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · have hE := I'.comap_blowupIso_hom f hI
        have hF := I'.isEffectiveCartier_comap_blowupToBase
        simp only [exceptionalClass_snoc_last, LineBundleClass.pullback_inv]
        rw [hF.pullback_mk_toInvertibleSheaf (hF.comap k.hom)]
        exact congrArg Inv.inv (LineBundleClass.mk_toInvertibleSheaf_congr _ _ hE)
      · rw [exceptionalClass_snoc_castSucc, exceptionalClass_snoc_castSucc,
          LineBundleClass.pullback_comp, Scheme.IdealSheafData.blowupIso_hom_blowupToBase,
          ← LineBundleClass.pullback_comp, ih hf j]

end IsLift

/-- Pulling back each center along the isomorphism at its stage transports a tower along any
base isomorphism. The resulting tower and the lift retain the order of all centers. -/
theorem exists_isLift (T : BlowupTower X' n Y') (e : X ≅ X') :
    ∃ (Y : Scheme.{u}) (U : BlowupTower X n Y) (g : Y ≅ Y'), IsLift e U T g := by
  induction T with
  | nil => exact ⟨X, nil, e, by simp⟩
  | snoc T I ih =>
    obtain ⟨Y, U, g, hg⟩ := ih
    refine ⟨(I.comap g.hom).blowup, U.snoc (I.comap g.hom), I.blowupIso g rfl, ?_⟩
    exact hg.snoc rfl

end BlowupTower
end QPainleve
