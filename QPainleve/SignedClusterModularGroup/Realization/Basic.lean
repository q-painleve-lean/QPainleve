/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.Composition.Defined
public import QPainleve.AlgebraicGeometry.RationalMap.Composition.Sections
public import QPainleve.SignedClusterModularGroup.Realization.Surface

import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RationalPoint

/-!
# Geometric realizations of independent X maps

A realization over a dense open of centers specifies an isomorphism of surface
pairs at each rational center. The Picard pullback and the action on the numbered
boundary are constant in the markings. The fixed-center evaluation square lives
on its common rational domain, so it also applies to evaluations with nondense
image.

Restriction and composition use Mathlib's partial maps for the center maps and
the fixed-center square uses `Scheme.RationalMap.compOfDefined`. The dihedral
action retains the ordered branches for a self-node and for parallel nodes.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PartialMap

universe u

namespace QPainleve.SignedClusterModularGroup

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k] {n : ℕ} [NeZero n]
  {L₀ L₁ L₂ : Type u} [AddCommGroup L₀] [AddCommGroup L₁] [AddCommGroup L₂]
  {B₀ : LinearMap.BilinForm ℤ L₀} {B₁ : LinearMap.BilinForm ℤ L₁}
  {B₂ : LinearMap.BilinForm ℤ L₂}
  {X₀ X₁ X₂ : Scheme.{u}} [IsIntegral X₀]
  [X₀.IsSeparated] [X₁.IsSeparated] [X₂.IsSeparated]

local notation "S" => Spec (CommRingCat.of k)

namespace GeometricRealization

section Points

variable {S₀ : Scheme.{u}} {U V : Over S₀} (C : U.left.PartialMap V.left)

/-- A section of the parameter scheme over its ground field. -/
abbrev Point (T : Over S₀) := Over.mk (𝟙 S₀) ⟶ T

/-- The sections with values in the open of definition of the center map. -/
abbrev CenterPoint := Point C.domainOver

end Points

end GeometricRealization

open GeometricRealization (Point CenterPoint)

open MarkedSurface (surfaceIso boundaryIso)

/-- A fixed-center realization records an isomorphism of pairs and its compatibility
with the marked Picard isometry, numbered branches and rational X evaluation. -/
@[ext]
structure FiberRealization (M : MarkedSurface k n B₀ X₀) (N : MarkedSurface k n B₁ X₁)
    (F : X₀ ⤏ X₁) (I : B₁.IsometryEquiv B₀) (g : DihedralGroup n) where
  /-- The isomorphism of the two surface pairs over the field. -/
  iso : M.pair ≅ N.pair
  /-- The Picard pullback in the markings is the specified isometry. -/
  picard_eq (a : L₁) :
    M.picardMarking (I a) =
      Additive.ofMul (LineBundleClass.pullback (surfaceIso iso).hom (N.picardMarking a).toMul)
  /-- The action on the actual numbered branches is the specified dihedral element. -/
  boundaryAction_eq :
    letI : PrestableFamily (M.boundary ↘ S) := M.prestable
    let : PrestableFamily (N.boundary ↘ S) := N.prestable
    (boundaryIso iso).boundaryCycleAction M.cycle N.cycle = g
  /-- The generic evaluation lies in the domain of `F` and the rational square commutes. -/
  evaluation_eq :
    ∃ h : M.evaluation.fromFunctionField (IsLocalRing.closedPoint M.surface.functionField) ∈
        F.domain,
      M.evaluation.compOfDefined F h = (surfaceIso iso).hom.toRationalMap.comp N.evaluation

namespace FiberRealization

variable (M : MarkedSurface k n B₀ X₀)

/-- The identity of a surface pair realizes the identity X map and both identity actions. -/
def refl : FiberRealization M M (Scheme.RationalMap.id X₀) (.refl B₀) 1 where
  iso := Iso.refl _
  picard_eq a := by
    have ha : LinearMap.BilinForm.IsometryEquiv.refl B₀ a = a := rfl
    simp [ha]
  boundaryAction_eq := by
    dsimp only
    simp only [MarkedSurface.boundaryIso_refl]
    let : PrestableFamily (M.boundary ↘ S) := M.prestable
    exact Iso.boundaryCycleAction_refl M.cycle
  evaluation_eq := by
    obtain ⟨h, he⟩ := M.evaluation.compOfDefined_toRationalMap (𝟙 X₀)
    refine ⟨h, he.trans ?_⟩
    simp only [MarkedSurface.surfaceIso_refl, Iso.refl_hom, RationalMap.id_comp]
    obtain ⟨p, hp⟩ := M.evaluation.exists_rep
    rw [← hp, ← RationalMap.compHom_toRationalMap, PartialMap.compHom_id]

variable {M} {N : MarkedSurface k n B₁ X₁} {O : MarkedSurface k n B₂ X₂}
  [IsIntegral X₁] {F : X₀ ⤏ X₁} [F.IsDominant] {G : X₁ ⤏ X₂}
  {I : B₁.IsometryEquiv B₀} {J : B₂.IsometryEquiv B₁} {g h : DihedralGroup n}

/-- Successive fixed-center realizations compose on the common rational domain.
The Picard isometries compose by pullback and the branch actions compose forward. -/
def comp (R : FiberRealization M N F I g) (R' : FiberRealization N O G J h) :
    FiberRealization M O (F.comp G) (J.trans I) (h * g) where
  iso := R.iso ≪≫ R'.iso
  picard_eq a := by
    have ha : (J.trans I) a = I (J a) := rfl
    rw [ha, R.picard_eq, MarkedSurface.surfaceIso_trans, Iso.trans_hom,
      ← LineBundleClass.pullback_comp]
    exact congrArg (fun b : Additive (LineBundleClass N.surface) ↦
      Additive.ofMul (LineBundleClass.pullback (surfaceIso R.iso).hom b.toMul)) (R'.picard_eq a)
  boundaryAction_eq := by
    let : PrestableFamily (N.boundary ↘ S) := N.prestable
    dsimp only
    simp only [MarkedSurface.boundaryIso_trans]
    let : PrestableFamily (M.boundary ↘ S) := M.prestable
    let : PrestableFamily (O.boundary ↘ S) := O.prestable
    exact (Iso.boundaryCycleAction_trans (boundaryIso R.iso) M.cycle N.cycle
      (boundaryIso R'.iso) O.cycle).trans
        (congrArg₂ (· * ·) R'.boundaryAction_eq R.boundaryAction_eq)
  evaluation_eq := by
    obtain ⟨h₀, hR⟩ := R.evaluation_eq
    obtain ⟨h₁, hR'⟩ := R'.evaluation_eq
    simpa only [MarkedSurface.surfaceIso_trans, Iso.trans_hom] using
      RationalMap.compOfDefined_comp_eq_of_comp_eq M.evaluation N.evaluation O.evaluation
        (surfaceIso R.iso).hom (surfaceIso R'.iso).hom F G h₀ h₁ hR hR'

@[simp]
theorem refl_iso : (refl M).iso = Iso.refl M.pair := (rfl)

@[simp]
theorem comp_iso (R : FiberRealization M N F I g) (R' : FiberRealization N O G J h) :
    (R.comp R').iso = R.iso ≪≫ R'.iso := (rfl)

end FiberRealization

/-- A realization between fixed marked families over a dominant center map `C`.
At every rational center in its domain the isomorphism of pairs realizes the same
Picard pullback and the same action on the boundary, and intertwines X evaluation. -/
structure GeometricRealization
    {T₀ T₁ : Over (Spec (CommRingCat.of k))}
    [Nonempty T₀.left] [Smooth T₀.hom]
    (P₀ : Point T₀ → MarkedSurface k n B₀ X₀) (P₁ : Point T₁ → MarkedSurface k n B₁ X₁)
    (C : T₀.left.PartialMap T₁.left) [IsDominant C.hom] [C.IsOver T₀.hom T₁.hom]
    (F : X₀ ⤏ X₁) [F.IsDominant] : Type (u + 1) where
  /-- Pullback on the fixed integral Picard lattices. -/
  picard : B₁.IsometryEquiv B₀
  /-- The forward action on the numbered boundary, including its branch orders. -/
  boundaryAction : DihedralGroup n
  /-- The geometric realization at each rational center of the domain. -/
  fiber (c : CenterPoint C) :
    FiberRealization (P₀ (c ≫ C.domainSource)) (P₁ (c ≫ C.domainTarget)) F picard boundaryAction

namespace GeometricRealization

variable {T₀ T₁ T₂ : Over (Spec (CommRingCat.of k))}
  [Nonempty T₀.left] [Smooth T₀.hom]
  {P₀ : Point T₀ → MarkedSurface k n B₀ X₀} {P₁ : Point T₁ → MarkedSurface k n B₁ X₁}
  {P₂ : Point T₂ → MarkedSurface k n B₂ X₂}
  {C : T₀.left.PartialMap T₁.left} [IsDominant C.hom] [C.IsOver T₀.hom T₁.hom]
  {F : X₀ ⤏ X₁} [F.IsDominant]
  (R : GeometricRealization P₀ P₁ C F)

/-- The forward permutation of the numbered boundary components. -/
def boundaryPerm : Equiv.Perm (ZMod n) := DihedralGroup.cycleVertexPerm R.boundaryAction

/-- The component permutation is the vertex action of the dihedral element. -/
theorem boundaryPerm_def : R.boundaryPerm = DihedralGroup.cycleVertexPerm R.boundaryAction :=
  (rfl)

/-- The orientation sign read on the actual ordered branches. -/
def orientation : ℤˣ := DihedralGroup.cycleOrientationSign R.boundaryAction

/-- The orientation is the sign character of the action on the numbered branches. -/
theorem orientation_def : R.orientation = DihedralGroup.cycleOrientationSign R.boundaryAction :=
  (rfl)

/-- A single fiber isomorphism determines the forward action on the numbered boundary. -/
theorem boundaryAction_eq_of_fiberIso_eq
    (R' : GeometricRealization P₀ P₁ C F) (c : CenterPoint C)
    (h : (R.fiber c).iso = (R'.fiber c).iso) : R.boundaryAction = R'.boundaryAction := by
  rw [← (R.fiber c).boundaryAction_eq, ← (R'.fiber c).boundaryAction_eq, h]

/-- A single fiber isomorphism determines the constant pullback on the Picard marking. -/
theorem picard_eq_of_fiberIso_eq (R' : GeometricRealization P₀ P₁ C F) (c : CenterPoint C)
    (h : (R.fiber c).iso = (R'.fiber c).iso) : R.picard = R'.picard := by
  refine DFunLike.ext _ _ fun a ↦ ?_
  apply (P₀ (c ≫ C.domainSource)).picardMarking.injective
  rw [(R.fiber c).picard_eq, (R'.fiber c).picard_eq, h]

omit [Infinite k] in
/-- A dense center domain in a nonempty smooth parameter scheme has a rational center. -/
theorem nonempty_centerPoint (C : T₀.left.PartialMap T₁.left) : Nonempty (CenterPoint C) := by
  let : Nonempty C.domain.toScheme := C.dense_domain.nonempty.to_subtype
  have : Smooth (C.domain.ι ≫ T₀.hom) := inferInstance
  obtain ⟨⟨p, hp⟩⟩ :=
    (C.domain.ι ≫ T₀.hom).denseRange_rationalSections.nonempty
  exact ⟨Over.homMk p hp⟩

/-- The fiber isomorphisms determine all the data of a realization. -/
@[ext]
theorem ext (R' : GeometricRealization P₀ P₁ C F)
    (h : ∀ c, (R.fiber c).iso = (R'.fiber c).iso) : R = R' := by
  obtain ⟨c⟩ := nonempty_centerPoint C
  have hp := R.picard_eq_of_fiberIso_eq R' c (h c)
  have hb := R.boundaryAction_eq_of_fiberIso_eq R' c (h c)
  cases R
  cases R'
  cases hp
  cases hb
  congr
  funext x
  exact FiberRealization.ext (h x)

/-- Restrict the realization to a dense open of its center domain. -/
def restrict (W : T₀.left.Opens) (hW : Dense (W : Set T₀.left)) (hWC : W ≤ C.domain) :
    GeometricRealization P₀ P₁ (C.restrict W hW hWC) F where
  picard := R.picard
  boundaryAction := R.boundaryAction
  fiber c := by
    simpa only [Category.assoc, restrictDomainHom_source,
      restrictDomainHom_target] using R.fiber (c ≫ C.restrictDomainHom W hW hWC)

@[simp]
theorem restrict_picard (W : T₀.left.Opens) (hW : Dense (W : Set T₀.left)) (hWC : W ≤ C.domain) :
    (R.restrict W hW hWC).picard = R.picard := (rfl)

@[simp]
theorem restrict_boundaryAction (W : T₀.left.Opens) (hW : Dense (W : Set T₀.left))
    (hWC : W ≤ C.domain) : (R.restrict W hW hWC).boundaryAction = R.boundaryAction := (rfl)

/-- The identity realization uses the identity pair isomorphism at each center. -/
def refl (P : Point T₀ → MarkedSurface k n B₀ X₀) :
    GeometricRealization P P (PartialMap.id T₀.left) (RationalMap.id X₀) where
  picard := .refl B₀
  boundaryAction := 1
  fiber c := by
    simpa only [domainTarget_id] using
      FiberRealization.refl (P (c ≫ (PartialMap.id T₀.left).domainSource))

@[simp]
theorem refl_picard (P : Point T₀ → MarkedSurface k n B₀ X₀) :
    (refl P).picard = .refl B₀ := (rfl)

@[simp]
theorem refl_boundaryAction (P : Point T₀ → MarkedSurface k n B₀ X₀) :
    (refl P).boundaryAction = 1 := (rfl)

variable [PreirreducibleSpace T₀.left] [Nonempty T₁.left] [Smooth T₁.hom] [IsIntegral X₁]
  {D : T₁.left.PartialMap T₂.left} [IsDominant D.hom] [D.IsOver T₁.hom T₂.hom]
  {G : X₁ ⤏ X₂} [G.IsDominant]

/-- Successive realizations compose on the inverse image of the next center domain.
At each center the same pair isomorphism realizes the composite Picard pullback,
boundary action, and rational X map. -/
def comp (R' : GeometricRealization P₁ P₂ D G) :
    GeometricRealization P₀ P₂ (C.comp D) (F.comp G) where
  picard := R'.picard.trans R.picard
  boundaryAction := R'.boundaryAction * R.boundaryAction
  fiber c := by
    have hmid : (c ≫ C.compDomainLeft D) ≫ C.domainTarget =
        (c ≫ C.compDomainRight D) ≫ D.domainSource := by
      simp only [Category.assoc, compDomainLeft_target]
    have hsrc : (c ≫ C.compDomainLeft D) ≫ C.domainSource = c ≫ (C.comp D).domainSource := by
      simp only [Category.assoc, compDomainLeft_source]
    have htgt : (c ≫ C.compDomainRight D) ≫ D.domainTarget = c ≫ (C.comp D).domainTarget := by
      simp only [Category.assoc, compDomainRight_target]
    let first := R.fiber (c ≫ C.compDomainLeft D)
    let second := R'.fiber (c ≫ C.compDomainRight D)
    exact hsrc ▸ htgt ▸ first.comp (hmid.symm ▸ second)

@[simp]
theorem comp_picard (R' : GeometricRealization P₁ P₂ D G) :
    (R.comp R').picard = R'.picard.trans R.picard := (rfl)

@[simp]
theorem comp_boundaryAction (R' : GeometricRealization P₁ P₂ D G) :
    (R.comp R').boundaryAction = R'.boundaryAction * R.boundaryAction := (rfl)

/-- The component permutation of the composite is the forward composition. -/
@[simp]
theorem comp_boundaryPerm (R' : GeometricRealization P₁ P₂ D G) :
    (R.comp R').boundaryPerm = R'.boundaryPerm * R.boundaryPerm := by
  simp [boundaryPerm]

/-- The orientation sign of the composite is the product of the two signs. -/
@[simp]
theorem comp_orientation (R' : GeometricRealization P₁ P₂ D G) :
    (R.comp R').orientation = R'.orientation * R.orientation := by
  simp [orientation]

end GeometricRealization
end QPainleve.SignedClusterModularGroup
