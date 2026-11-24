/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Center
public import QPainleve.Algebra.Cluster.Word.RationalMap
public import QPainleve.SignedClusterModularGroup.Realization.Basic

/-!
# Composing geometric realizations along cluster words

`GeometricRealization.comp` composes successive generator realizations.
`Quiver.Path.centerPartialMap_comp` identifies the composition domain with the
simultaneous noncollision open. The intermediate families are indexed by prefixes
because visits to the same exchange matrix can have different toric presentations.
The construction tracks the marked Picard pullback and the numbered branch action.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Quiver Quiver.Path Scheme.PartialMap
open QPainleve.CharacterTorus QPainleve.Cluster

universe u

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k]
  {ι : Type u} [Fintype ι] [DecidableEq ι] {N : Type*} [AddCommGroup N]
  {n : ℕ} [NeZero n] {B : SkewExchangeMatrix ι}

local notation "A" => (ι → ℤ)
local notation "Centers" => Over.mk (structureMap k A)
local notation "XTor" => scheme k (ι →₀ ℤ)

attribute [local instance] hasUniqueDiv_of_free_int

local instance : PreirreducibleSpace (Centers).left :=
  inferInstanceAs (PreirreducibleSpace (scheme k A))

/-- The word's partial center map is over the ground field in the slice category. -/
instance instIsOverCenterPartialMap {E : SkewExchangeMatrix ι} (w : Word B E)
    (P : ChargeSeed B N) :
    (w.centerPartialMap k P).IsOver (Centers).hom (Centers).hom :=
  inferInstanceAs ((w.centerPartialMap k P).IsOver (structureMap k A) (structureMap k A))

variable {L₀ L₁ : Type u} [AddCommGroup L₀] [AddCommGroup L₁]
  {B₀ : LinearMap.BilinForm ℤ L₀} {B₁ : LinearMap.BilinForm ℤ L₁}
  {M₀ : Point (Over.mk (structureMap k (ι → ℤ))) → MarkedSurface k n B₀ (scheme k (ι →₀ ℤ))}
  {M₁ : Point (Over.mk (structureMap k (ι → ℤ))) → MarkedSurface k n B₁ (scheme k (ι →₀ ℤ))}
  {C : (scheme k (ι → ℤ)).PartialMap (scheme k (ι → ℤ))} [IsDominant C.hom]
  [C.IsOver (Over.mk (structureMap k (ι → ℤ))).hom (Over.mk (structureMap k (ι → ℤ))).hom]
  {F : scheme k (ι →₀ ℤ) ⤏ scheme k (ι →₀ ℤ)} [F.IsDominant]
  {E : SkewExchangeMatrix ι} {w : Word B E} {P : ChargeSeed B N}

/-- Identify the indices of a restricted or composed realization with the two
maps of the word it realizes. -/
private def reindexWord (R : GeometricRealization (T₀ := Centers) (T₁ := Centers) M₀ M₁ C F)
    (hC : C = w.centerPartialMap k P) (hF : F = w.xRationalMap k) :
    GeometricRealization (T₀ := Centers) (T₁ := Centers) M₀ M₁
      (w.centerPartialMap k P) (w.xRationalMap k) := by
  subst C F
  exact R

@[simp]
private theorem reindexWord_picard
    (R : GeometricRealization (T₀ := Centers) (T₁ := Centers) M₀ M₁ C F)
    (hC : C = w.centerPartialMap k P) (hF : F = w.xRationalMap k) :
    (reindexWord R hC hF).picard = R.picard := by
  subst C F
  rfl

@[simp]
private theorem reindexWord_boundaryAction
    (R : GeometricRealization (T₀ := Centers) (T₁ := Centers) M₀ M₁ C F)
    (hC : C = w.centerPartialMap k P) (hF : F = w.xRationalMap k) :
    (reindexWord R hC hF).boundaryAction = R.boundaryAction := by
  subst C F
  rfl

variable (P : ChargeSeed B N)
  {L : ∀ {E : SkewExchangeMatrix ι}, Word B E → AddCommGrpCat.{u}}
  {form : ∀ {E} (p : Word B E), LinearMap.BilinForm ℤ (L p)}
  {family : ∀ {E} (p : Word B E), Point (Over.mk (structureMap k (ι → ℤ))) →
    MarkedSurface k n (form p) (scheme k (ι →₀ ℤ))}

local notation "ε" => (Path.nil : Word B B)

variable (family) in
/-- A realization for each arrow occurrence of a word, with the families indexed by
their prefixes. A suffix witnesses that the specified arrow occurs in the word. -/
abbrev WordStepRealizations {E : SkewExchangeMatrix ι} (w : Word B E) : Type (u + 1) :=
  ∀ {D D' : SkewExchangeMatrix ι} (p : Word B D) (s : D ⟶ D'),
    (∃ q : Word D' E, (p.cons s).comp q = w) →
    GeometricRealization (n := n) (T₀ := Centers) (T₁ := Centers)
      (B₀ := form p) (B₁ := form (p.cons s)) (family p) (family (p.cons s))
      (s.toPath.centerPartialMap k (p.chargeTarget P)) (s.toPath.xRationalMap k)

variable {P} {D E : SkewExchangeMatrix ι} {p : Word B D} {s : D ⟶ E}

variable (P family) in
/-- The empty word requires no generator realizations. -/
def WordStepRealizations.nil : WordStepRealizations P family ε := by
  intro _ _ p s h
  exfalso
  obtain ⟨q, hq⟩ := h
  have h := congrArg Path.length hq
  simp only [Path.length_comp, Path.length_cons, Path.length_nil] at h
  omega

/-- A word with its final step deleted uses the same realizations of the earlier steps. -/
def WordStepRealizations.prefix (step : WordStepRealizations P family (p.cons s)) :
    WordStepRealizations P family p := fun q t h ↦
  step q t (by
    obtain ⟨r, hr⟩ := h
    exact ⟨r.cons s, by rw [Path.comp_cons, hr]⟩)

/-- Restricting the step data to a prefix retains each specified realization. -/
theorem WordStepRealizations.prefix_apply (step : WordStepRealizations P family (p.cons s))
    {D₀ D₁ : SkewExchangeMatrix ι} (q : Word B D₀) (t : D₀ ⟶ D₁)
    (r : Word D₁ D) (hr : (q.cons t).comp r = p) :
    step.prefix q t ⟨r, hr⟩ = step q t ⟨r.cons s, by rw [Path.comp_cons, hr]⟩ :=
  (rfl)

/-- The realization of the final arrow of a nonempty word. -/
def WordStepRealizations.last (step : WordStepRealizations P family (p.cons s)) :
    GeometricRealization (n := n) (T₀ := Centers) (T₁ := Centers)
      (B₀ := form p) (B₁ := form (p.cons s)) (family p) (family (p.cons s))
      (s.toPath.centerPartialMap k (p.chargeTarget P)) (s.toPath.xRationalMap k) :=
  step p s ⟨Path.nil, Path.comp_nil _⟩

/-- The final arrow is selected using the empty suffix. -/
theorem WordStepRealizations.last_eq (step : WordStepRealizations P family (p.cons s)) :
    step.last = step p s ⟨Path.nil, Path.comp_nil _⟩ := (rfl)

variable (P)

/-- Compose the realizations of all steps in a typed word. The realization of an
edge uses the family at the prefix before the edge and the family at the prefix
after it. The result uses the prescribed monomial center map on the common open
and the independent X rational map of the whole word. -/
def ofWord : {E : SkewExchangeMatrix ι} → (w : Word B E) →
    WordStepRealizations P family w →
    GeometricRealization (n := n) (T₀ := Centers) (T₁ := Centers)
      (B₀ := form ε) (B₁ := form w) (family ε) (family w)
      (w.centerPartialMap k P) (w.xRationalMap k)
  | _, .nil, _ =>
    let C := (Scheme.PartialMap.id (scheme k A)).restrict
      ((ε).centerOpen k P) ((ε).dense_centerOpen P) le_top
    have hC : (ε).centerPartialMap k P = C := centerPartialMap_nil P
    letI : IsDominant C.hom := hC ▸ (inferInstance : IsDominant ((ε).centerPartialMap k P).hom)
    letI : C.IsOver (Centers).hom (Centers).hom := hC ▸ (inferInstance :
      ((ε).centerPartialMap k P).IsOver (Centers).hom (Centers).hom)
    reindexWord (C := C) ((GeometricRealization.refl (family ε)).restrict
      ((ε).centerOpen k P) ((ε).dense_centerOpen P) le_top)
      hC.symm (xRationalMap_nil (B := B) k).symm
  | _, .cons p s, step =>
    let R := ofWord p step.prefix
    let T := WordStepRealizations.last (P := P) (family := family) (p := p) (s := s) step
    let C := (p.centerPartialMap k P).comp (s.toPath.centerPartialMap k (p.chargeTarget P))
    have hC : (p.cons s).centerPartialMap k P = C :=
      (congrArg (fun v ↦ v.centerPartialMap k P) (Path.comp_toPath_eq_cons p s)).symm.trans
        (centerPartialMap_comp p s.toPath P)
    letI : C.IsOver (Centers).hom (Centers).hom := hC ▸ (inferInstance :
      ((p.cons s).centerPartialMap k P).IsOver (Centers).hom (Centers).hom)
    reindexWord (C := C) (R.comp T) hC.symm
      (by rw [← xRationalMap_comp, Path.comp_toPath_eq_cons])

/-- The empty word pulls Picard classes back by the identity. -/
@[simp]
theorem ofWord_nil_picard (step : WordStepRealizations P family ε) :
    (ofWord P ε step).picard = .refl (form ε) := by
  simp only [ofWord, reindexWord_picard]
  exact (restrict_picard (refl (family ε)) _ _ _).trans (refl_picard (family ε))

/-- The empty word fixes every numbered branch. -/
@[simp]
theorem ofWord_nil_boundaryAction (step : WordStepRealizations P family ε) :
    (ofWord P ε step).boundaryAction = 1 := by
  simp only [ofWord, reindexWord_boundaryAction]
  exact (restrict_boundaryAction (refl (family ε)) _ _ _).trans
    (refl_boundaryAction (family ε))

/-- Appending an arrow composes the Picard pullbacks in reverse execution order. -/
@[simp]
theorem ofWord_cons_picard (step : WordStepRealizations P family (p.cons s)) :
    (ofWord P (p.cons s) step).picard = step.last.picard.trans (ofWord P p step.prefix).picard := by
  simp [ofWord]

/-- Appending an arrow composes the actions on numbered branches in execution order. -/
@[simp]
theorem ofWord_cons_boundaryAction (step : WordStepRealizations P family (p.cons s)) :
    (ofWord P (p.cons s) step).boundaryAction =
      step.last.boundaryAction * (ofWord P p step.prefix).boundaryAction := by
  simp [ofWord]

/-- A word assembled from orientation-preserving steps preserves the orientation
of the actual branches, including those of self-nodes and two-node boundaries. -/
theorem ofWord_orientation_eq_one (w : Word B E) (step : WordStepRealizations P family w)
    (h : ∀ {D D' : SkewExchangeMatrix ι} (p : Word B D) (s : D ⟶ D')
      (hs : ∃ q : Word D' E, (p.cons s).comp q = w), (step p s hs).orientation = 1) :
    (ofWord P w step).orientation = 1 := by
  induction w with
  | nil => simp [orientation_eq_cycleOrientationSign]
  | cons p s ih =>
    have hlast : step.last.orientation = 1 := by
      rw [WordStepRealizations.last_eq]
      exact h _ _ _
    have hprefix : (ofWord P p step.prefix).orientation = 1 := by
      apply ih
      intro D D' q t ht
      obtain ⟨r, hr⟩ := ht
      rw [WordStepRealizations.prefix_apply _ _ _ r hr]
      exact h _ _ _
    rw [orientation_eq_cycleOrientationSign, ofWord_cons_boundaryAction, map_mul]
    rw [orientation_eq_cycleOrientationSign] at hlast hprefix
    rw [hlast, hprefix, mul_one]

end QPainleve.SignedClusterModularGroup.GeometricRealization
