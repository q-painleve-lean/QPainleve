/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Isomorphism

/-!
# Ordered sequences of blowups

Each center is an ideal sheaf on the scheme obtained from all preceding blowups. This permits
infinitely near centers. A base isomorphism lifts along a pair of sequences if the isomorphism
at each stage identifies the next center ideals. The lift commutes with the projection to the
base, and Picard pullback identifies the total transforms of the successive exceptional divisors.
-/

public section

noncomputable section

open CategoryTheory TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A finite ordered sequence of blowup centers, with each ideal sheaf on its own stage. -/
inductive BlowupSequence : Scheme.{u} → ℕ → Type (u + 1)
  /-- The sequence with no centers. -/
  | nil (X : Scheme.{u}) : BlowupSequence X 0
  /-- Blow up the first center before applying the rest of the sequence. -/
  | cons {X : Scheme.{u}} {n : ℕ} (I : X.IdealSheafData) (s : BlowupSequence I.blowup n) :
      BlowupSequence X (n + 1)

namespace BlowupSequence

open IdealSheafData

variable {X Y Z : Scheme.{u}} {n : ℕ}

/-- The final scheme of an ordered blowup sequence. This computes on the constructors so
that the sequence can be used as a source or target of morphisms. -/
abbrev top : {X : Scheme.{u}} → {n : ℕ} → BlowupSequence X n → Scheme.{u}
  | _, _, .nil X => X
  | _, _, .cons _ s => s.top

/-- The composite of the blowup projections, from the final scheme to the base. -/
def toBase : {X : Scheme.{u}} → {n : ℕ} → (s : BlowupSequence X n) → s.top ⟶ X
  | _, _, .nil X => 𝟙 X
  | _, _, .cons I s => s.toBase ≫ I.blowupToBase

/-- The projection for the empty sequence is the identity. -/
@[simp]
theorem toBase_nil (X : Scheme.{u}) : (nil X).toBase = 𝟙 X :=
  (rfl)

/-- The first blowup projection is the last morphism in the composite to the base. -/
@[simp]
theorem toBase_cons (I : X.IdealSheafData) (s : BlowupSequence I.blowup n) :
    (cons I s).toBase = s.toBase ≫ I.blowupToBase :=
  (rfl)

/-- The class of the total transform on the final scheme of the exceptional divisor at the
specified step. The indices begin with the first blowup, numbered zero. -/
def exceptionalClass :
    {X : Scheme.{u}} → {n : ℕ} → (s : BlowupSequence X n) → Fin n → LineBundleClass s.top
  | _, _, .nil _, i => i.elim0
  | _, _, .cons I s, i => Fin.cases
      (LineBundleClass.pullback s.toBase I.blowupExceptionalClass)
      (fun j ↦ s.exceptionalClass j) i

/-- The first exceptional class is pulled back along all subsequent blowups. -/
@[simp]
theorem exceptionalClass_cons_zero (I : X.IdealSheafData) (s : BlowupSequence I.blowup n) :
    (cons I s).exceptionalClass 0 = LineBundleClass.pullback s.toBase I.blowupExceptionalClass :=
  (rfl)

/-- Later exceptional classes are the total transforms from the remaining sequence. -/
@[simp]
theorem exceptionalClass_cons_succ (I : X.IdealSheafData)
    (s : BlowupSequence I.blowup n) (i : Fin n) :
    (cons I s).exceptionalClass i.succ = s.exceptionalClass i :=
  (rfl)

/-- Compatibility of two ordered blowup sequences over a base isomorphism. At each step,
the next center ideal of the target pulls back to the next center ideal of the source. -/
inductive Compatible :
    {X Y : Scheme.{u}} → (X ≅ Y) → {n : ℕ} →
      BlowupSequence X n → BlowupSequence Y n → Prop
  /-- An isomorphism identifies two empty sequences. -/
  | nil {X Y : Scheme.{u}} (e : X ≅ Y) : Compatible e (.nil X) (.nil Y)
  /-- A center identification lifts the base isomorphism to the bases of the remaining
  sequences. -/
  | cons {X Y : Scheme.{u}} {e : X ≅ Y} {n : ℕ}
      {I : X.IdealSheafData} {J : Y.IdealSheafData} {s : BlowupSequence I.blowup n}
      {t : BlowupSequence J.blowup n} (h : J.comap e.hom = I)
      (ht : Compatible (J.blowupIso e h) s t) : Compatible e (.cons I s) (.cons J t)

namespace Compatible

variable {e : X ≅ Y} {f : Y ≅ Z}
  {s : BlowupSequence X n} {t : BlowupSequence Y n} {v : BlowupSequence Z n}

/-- Compatibility identifies the first center ideals. -/
theorem comap_eq {I : X.IdealSheafData} {J : Y.IdealSheafData}
    {s : BlowupSequence I.blowup n} {t : BlowupSequence J.blowup n}
    (h : Compatible e (.cons I s) (.cons J t)) : J.comap e.hom = I := by
  cases h with
  | cons hc _ => exact hc

/-- After blowing up the matched centers, the remaining sequences are compatible over the
lifted isomorphism. -/
theorem tail {I : X.IdealSheafData} {J : Y.IdealSheafData}
    {s : BlowupSequence I.blowup n} {t : BlowupSequence J.blowup n}
    (h : Compatible e (.cons I s) (.cons J t)) : Compatible (J.blowupIso e h.comap_eq) s t := by
  cases h with
  | cons _ ht => exact ht

/-- A sequence is compatible with itself over the identity. -/
@[refl]
theorem refl (s : BlowupSequence X n) : Compatible (Iso.refl X) s s := by
  induction s with
  | nil X => exact .nil (Iso.refl X)
  | cons I _ ih => exact .cons (comap_id I) (by simpa only [blowupIso_refl] using ih)

/-- Reversing a base isomorphism reverses compatibility of the sequences. -/
theorem symm (h : Compatible e s t) : Compatible e.symm t s := by
  induction h with
  | nil e => exact .nil e.symm
  | cons hc _ ih =>
    refine .cons (by rw [← hc, ← comap_comp]; simp) ?_
    rwa [blowupIso_symm _ hc]

/-- Compatibility holds for the composite of two compatible base isomorphisms. -/
theorem trans (h : Compatible e s t) (k : Compatible f t v) : Compatible (e ≪≫ f) s v := by
  induction h generalizing Z with
  | nil e =>
    cases k
    exact .nil (e ≪≫ f)
  | cons hc _ ih =>
    cases k with
    | cons kc kt =>
      refine .cons (by simp [hc, kc]) ?_
      simpa only [blowupIso_trans _ _ hc kc] using ih kt

/-- A compatible base isomorphism induces an isomorphism of the final schemes. -/
def liftIso {X Y : Scheme.{u}} {n : ℕ} {e : X ≅ Y}
    {s : BlowupSequence X n} {t : BlowupSequence Y n} (h : Compatible e s t) : s.top ≅ t.top :=
  match s, t with
  | .nil _, .nil _ => e
  | .cons _ _, .cons _ _ => h.tail.liftIso
termination_by structural s

/-- On empty sequences the lifted isomorphism is the base isomorphism. -/
@[simp]
theorem liftIso_nil (e : X ≅ Y) : (Compatible.nil e).liftIso = e := by
  rw [liftIso]

/-- The lift through nonempty sequences is the lift along their tails after blowing up
the first centers. -/
@[simp]
theorem liftIso_cons {I : X.IdealSheafData} {J : Y.IdealSheafData}
    {s : BlowupSequence I.blowup n} {t : BlowupSequence J.blowup n}
    (h : Compatible e (.cons I s) (.cons J t)) : h.liftIso = h.tail.liftIso := by
  rw [liftIso]

private theorem liftIso_congr {e e' : X ≅ Y} (he : e = e')
    (h : Compatible e s t) (h' : Compatible e' s t) : h.liftIso = h'.liftIso := by
  subst e'
  rfl

/-- The lift through a compatible sequence commutes with the projection to the base. -/
@[reassoc (attr := simp)]
theorem liftIso_hom_toBase (h : Compatible e s t) :
    h.liftIso.hom ≫ t.toBase = s.toBase ≫ e.hom := by
  induction h with
  | nil => simp only [liftIso_nil, toBase_nil, Category.comp_id, Category.id_comp]
  | cons _ _ ih =>
    rw [liftIso_cons, toBase_cons, toBase_cons, reassoc_of% ih]
    simp only [Category.assoc, blowupIso_hom_blowupToBase]

/-- The lift of the identity along an ordered sequence is the identity. -/
@[simp]
theorem liftIso_refl (s : BlowupSequence X n) : (refl s).liftIso = Iso.refl s.top := by
  induction s with
  | nil => simp
  | cons I s ih =>
    rw [liftIso_cons, ← ih]
    exact liftIso_congr I.blowupIso_refl _ _

/-- Lifting through ordered blowups commutes with composition. -/
theorem liftIso_trans (h : Compatible e s t) (k : Compatible f t v) :
    (h.trans k).liftIso = h.liftIso ≪≫ k.liftIso := by
  induction h generalizing Z with
  | nil e =>
    cases k
    simp only [liftIso_nil]
  | cons hc ht ih =>
    cases k with
    | cons kc kt =>
      rw [liftIso_cons, liftIso_cons, liftIso_cons, ← ih kt]
      exact liftIso_congr (blowupIso_trans _ _ hc kc) _ _

/-- Reversing the base isomorphism gives the inverse lift through ordered blowups. -/
theorem liftIso_symm (h : Compatible e s t) : h.symm.liftIso = h.liftIso.symm := by
  have hcomp : h.liftIso ≪≫ h.symm.liftIso = Iso.refl s.top := by
    rw [← liftIso_trans]
    rw [← liftIso_refl s]
    exact liftIso_congr (by simp) _ _
  apply CategoryTheory.Iso.ext
  rw [Iso.symm_hom, ← cancel_epi h.liftIso.hom, Iso.hom_inv_id]
  exact congrArg Iso.hom hcomp

/-- The Picard pullbacks along the lift and the projections to the bases commute. -/
theorem pullback_toBase (h : Compatible e s t) (a : LineBundleClass Y) :
    LineBundleClass.pullback h.liftIso.hom (LineBundleClass.pullback t.toBase a) =
      LineBundleClass.pullback s.toBase (LineBundleClass.pullback e.hom a) := by
  simp only [LineBundleClass.pullback_comp, liftIso_hom_toBase]

/-- Pullback along the lift takes each total-transform exceptional class to the class
with the same index in the source sequence. -/
@[simp]
theorem pullback_exceptionalClass (h : Compatible e s t) (i : Fin n) :
    LineBundleClass.pullback h.liftIso.hom (t.exceptionalClass i) = s.exceptionalClass i := by
  induction h with
  | nil => exact i.elim0
  | cons hc ht ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [liftIso_cons, exceptionalClass_cons_zero, exceptionalClass_cons_zero,
        ht.pullback_toBase]
      simp only [pullback_blowupExceptionalClass]
    · simpa only [liftIso_cons, exceptionalClass_cons_succ] using ih j

end Compatible

/-- Transport a sequence through a scheme isomorphism, taking the scheme-theoretic image
of each center under the isomorphism already constructed at that stage. -/
def transport {X Y : Scheme.{u}} {n : ℕ} (s : BlowupSequence X n) (e : X ≅ Y) :
    { t : BlowupSequence Y n // Compatible e s t } :=
  match s with
  | .nil _ => ⟨.nil Y, .nil e⟩
  | .cons I s =>
    have h : (I.comap e.inv).comap e.hom = I := by rw [← comap_comp]; simp
    let t := s.transport ((I.comap e.inv).blowupIso e h)
    ⟨.cons (I.comap e.inv) t.val, .cons h t.property⟩
termination_by structural s

/-- Transport of an empty sequence is empty. -/
@[simp]
theorem transport_val_nil (e : X ≅ Y) : ((nil X).transport e).val = nil Y :=
  (rfl)

/-- The first transported center is the inverse image along the inverse base isomorphism.
The tail is transported through the induced isomorphism of the first blowups. -/
@[simp]
theorem transport_val_cons (e : X ≅ Y) (I : X.IdealSheafData)
    (s : BlowupSequence I.blowup n) :
    ((cons I s).transport e).val =
      cons (I.comap e.inv)
        (s.transport ((I.comap e.inv).blowupIso e (by rw [← comap_comp]; simp))).val :=
  (rfl)

/-- A compatible target sequence is uniquely determined by the source and the base
isomorphism. -/
theorem Compatible.eq_transport (h : Compatible e s t) : t = (s.transport e).val := by
  induction h with
  | nil => exact (transport_val_nil _).symm
  | @cons X Y e n I J s t hc _ ih =>
    have hJ := congrArg (fun J ↦ IdealSheafData.comap J e.inv) hc
    rw [← comap_comp, Iso.inv_hom_id, comap_id] at hJ
    subst hJ
    simpa only [transport_val_cons] using congrArg (BlowupSequence.cons (I.comap e.inv)) ih

/-- Transport by the identity recovers the original sequence. -/
@[simp]
theorem transport_val_refl (s : BlowupSequence X n) :
    (s.transport (Iso.refl X)).val = s :=
  (Compatible.refl s).eq_transport.symm

/-- Transport by a composite agrees with successive transport. -/
theorem transport_val_trans (s : BlowupSequence X n) (e : X ≅ Y) (f : Y ≅ Z) :
    (s.transport (e ≪≫ f)).val = ((s.transport e).val.transport f).val :=
  ((s.transport e).property.trans ((s.transport e).val.transport f).property).eq_transport.symm

end BlowupSequence

end AlgebraicGeometry.Scheme
