/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Ordered towers of blowups

Each stage of a tower blows up an ideal on the current scheme. A lift of an isomorphism
through two towers matches these ideals by scheme-theoretic inverse image at every stage.
The lifted isomorphism respects the projection to the base and pulls back each ordered
exceptional class to its counterpart. Exceptional classes from earlier stages are taken
with their full pullbacks, as needed when a later center lies on an earlier exceptional
divisor.
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

/-- The final scheme of a blowup tower on a Noetherian scheme is Noetherian. -/
theorem isNoetherian (T : BlowupTower X n Y) [IsNoetherian X] : IsNoetherian Y := by
  induction T with
  | nil => infer_instance
  | snoc _ I ih =>
    have := ih
    exact isNoetherian_of_finiteType I.blowupToBase

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
      I.blowupExceptionalClass
      (fun i ↦ LineBundleClass.pullback I.blowupToBase (T.exceptionalClass i))

/-- At the last index, the marking is the class of the new exceptional divisor. -/
@[simp]
theorem exceptionalClass_snoc_last (T : BlowupTower X n Y) (I : Y.IdealSheafData) :
    (T.snoc I).exceptionalClass (Fin.last n) =
      (LineBundleClass.mk I.isEffectiveCartier_comap_blowupToBase.toInvertibleSheaf)⁻¹ := by
  simp [exceptionalClass, Scheme.IdealSheafData.blowupExceptionalClass_def]

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
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simpa only [exceptionalClass_snoc_last, Scheme.IdealSheafData.blowupExceptionalClass_def]
          using I'.pullback_blowupExceptionalClass f hI
      · rw [exceptionalClass_snoc_castSucc, exceptionalClass_snoc_castSucc,
          LineBundleClass.pullback_comp, Scheme.IdealSheafData.blowupIso_hom_blowupToBase,
          ← LineBundleClass.pullback_comp, ih hf j]

end IsLift

/-- A target tower equipped with a lift of the base isomorphism from the source tower. -/
structure Transport (T : BlowupTower X n Y) (e : X ≅ X') where
  /-- The final scheme of the target tower. -/
  top : Scheme.{u}
  /-- The target tower with its original order of centers. -/
  tower : BlowupTower X' n top
  /-- The isomorphism of the final schemes. -/
  iso : Y ≅ top
  /-- The isomorphism lifts the base isomorphism through the two towers. -/
  isLift : IsLift e T tower iso

/-- Extend the transport by taking the inverse image of the next source center along the
inverse of the preceding lift. -/
def Transport.snoc {T : BlowupTower X n Y} {e : X ≅ X'}
    (p : Transport T e) (I : Y.IdealSheafData) : Transport (T.snoc I) e :=
  have hI : (I.comap p.iso.inv).comap p.iso.hom = I := by
    rw [← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id, Scheme.IdealSheafData.comap_id]
  ⟨_, p.tower.snoc (I.comap p.iso.inv), (I.comap p.iso.inv).blowupIso p.iso hI, p.isLift.snoc hI⟩

/-- Transport the ordered centers along the successive lifts of the base isomorphism. -/
def transport {n : ℕ} {Y : Scheme.{u}} (T : BlowupTower X n Y) (e : X ≅ X') : Transport T e :=
  match T with
  | .nil => ⟨X', .nil, e, IsLift.nil_iff.mpr rfl⟩
  | .snoc T I => (T.transport e).snoc I
termination_by structural T

/-- The transport of an empty tower is empty. -/
@[simp]
theorem transport_nil (e : X ≅ X') :
    (nil (X := X)).transport e = ⟨X', .nil, e, IsLift.nil_iff.mpr rfl⟩ := (rfl)

/-- Transporting one more center extends the transport through the preceding stages. -/
@[simp]
theorem transport_snoc (T : BlowupTower X n Y) (e : X ≅ X') (I : Y.IdealSheafData) :
    (T.snoc I).transport e = (T.transport e).snoc I := (rfl)

/-- The base isomorphism and the source tower determine the transported tower and its lift. -/
theorem Transport.eq_transport {T : BlowupTower X n Y} {e : X ≅ X'}
    (p : Transport T e) : p = T.transport e := by
  induction T with
  | nil =>
    obtain ⟨_, U, g, hg⟩ := p
    cases U
    cases IsLift.nil_iff.mp hg
    rfl
  | snoc T I ih =>
    obtain ⟨_, U, g, hg⟩ := p
    cases U with
    | snoc U J =>
      obtain ⟨f, hf, hJ, rfl⟩ := IsLift.snoc_iff.mp hg
      have hcenter := congrArg (fun K ↦ Scheme.IdealSheafData.comap K f.inv) hJ
      rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id,
        Scheme.IdealSheafData.comap_id] at hcenter
      subst J
      exact congrArg (fun p : Transport T e ↦ p.snoc I) (ih ⟨_, U, f, hf⟩)

/-- Transport by the identity recovers the original tower and the identity on its final
scheme. -/
@[simp]
theorem transport_refl (T : BlowupTower X n Y) :
    T.transport (Iso.refl X) = ⟨Y, T, Iso.refl Y, IsLift.refl T⟩ :=
  (Transport.eq_transport _).symm

/-- Transport by a composite agrees with successive transport of the centers and composition
of the induced lifts. -/
theorem transport_trans (T : BlowupTower X n Y) (e : X ≅ X') (f : X' ≅ Z) :
    let p := T.transport e
    let q := p.tower.transport f
    T.transport (e ≪≫ f) = ⟨q.top, q.tower, p.iso ≪≫ q.iso, p.isLift.trans q.isLift⟩ :=
  (Transport.eq_transport _).symm

/-- Every tower admits a lift with the given target tower and base isomorphism. -/
theorem exists_isLift (T : BlowupTower X' n Y') (e : X ≅ X') :
    ∃ (Y : Scheme.{u}) (U : BlowupTower X n Y) (g : Y ≅ Y'), IsLift e U T g :=
  let p := T.transport e.symm
  ⟨p.top, p.tower, p.iso.symm, p.isLift.symm⟩

end BlowupTower
end QPainleve
