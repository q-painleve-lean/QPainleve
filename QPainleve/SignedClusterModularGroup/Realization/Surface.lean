/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection
public import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction
public import QPainleve.Geometry.Toric.CharacterTorus.Scheme
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Marked surfaces with numbered nodal boundary

A surface at a fixed center carries its actual closed boundary, a numbering of the
normalized components and ordered branches, an integral intersection marking,
and a rational evaluation into the independent X-coordinate scheme.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

universe u

namespace QPainleve.SignedClusterModularGroup

variable (k : Type u) [Field k] [IsSepClosed k] [Infinite k] (n : ℕ) [NeZero n]
  {L : Type u} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (X : Scheme.{u})

local notation "S" => Spec (CommRingCat.of k)

/-- A fixed-center surface with its marked Picard group, numbered closed boundary
and rational X evaluation. Families of such surfaces may be specified pointwise. -/
structure MarkedSurface where
  /-- The boundary immersion in schemes over the ground field. -/
  pair : Arrow (Over S)
  /-- The boundary is a closed subscheme. -/
  [closedImmersion : IsClosedImmersion pair.hom.left]
  /-- The surface is integral. -/
  [integral : IsIntegral pair.right.left]
  /-- The surface is smooth of relative dimension two. -/
  [smooth : SmoothOfRelativeDimension 2 pair.right.hom]
  /-- The surface is projective. -/
  [projective : @Scheme.IsProjectiveOver k _ pair.right.left ⟨pair.right.hom⟩]
  /-- The boundary is a prestable curve. -/
  [prestable : PrestableFamily pair.left.hom]
  /-- Numbered components, nodes, and branch orders of the unmarked boundary. -/
  cycle :
    letI : pair.left.left.Over S := ⟨pair.left.hom⟩
    letI : PrestableFamily (pair.left.left ↘ S) := prestable
    Scheme.NodalCycleNumbering (k := k) (X := pair.left.left)
      (Empty.elim : Empty → (pair.left.left ↘ S).smoothLocus) n
  /-- The marking identifies the fixed integral form with the surface intersection pairing. -/
  marking :
    letI : pair.right.left.Over S := ⟨pair.right.hom⟩
    letI : SmoothOfRelativeDimension 2 (pair.right.left ↘ S) := smooth
    B.IsometryEquiv (Chow.intersectionBilinForm k pair.right.left)
  /-- The evaluation in independent X coordinates as a rational map of the surface. -/
  evaluation : pair.right.left ⤏ X

namespace MarkedSurface

variable {k n B X} (M : MarkedSurface k n B X)

/-- The underlying surface of a fixed-center model. -/
abbrev surface : Scheme := M.pair.right.left

/-- The boundary curve of a fixed-center model. -/
abbrev boundary : Scheme := M.pair.left.left

instance : M.surface.Over S := ⟨M.pair.right.hom⟩
instance : M.boundary.Over S := ⟨M.pair.left.hom⟩
attribute [instance] integral
instance : M.surface.IsSeparated := by
  let : M.surface.IsProjectiveOver k := M.projective
  rw [Scheme.isSeparated_iff, ← Limits.terminal.comp_from (M.surface ↘ S)]
  infer_instance

instance : IsLocallyNoetherian M.surface := by
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : Smooth (M.surface ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  exact LocallyOfFiniteType.isLocallyNoetherian (M.surface ↘ S)

/-- The smooth surface underlying a marked pair is normal. -/
instance : IsNormalScheme M.surface := by
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : Smooth (M.surface ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsRegular M.surface := IsRegular.of_smooth (M.surface ↘ S)
  exact IsRegular.isNormal

/-- Postcompose the evaluation of a marked surface, keeping the same underlying pair
so that its identity isomorphism can be used for the resulting realization. -/
@[expose, simps pair evaluation]
def compEvaluation {Y : Scheme.{u}} (g : X ⟶ Y) : MarkedSurface k n B Y where
  pair := M.pair
  closedImmersion := M.closedImmersion
  integral := M.integral
  smooth := M.smooth
  projective := M.projective
  prestable := M.prestable
  cycle := M.cycle
  marking := M.marking
  evaluation := M.evaluation.compHom g

/-- The underlying Picard marking, with tensor product written additively. -/
def picardMarking : L ≃ₗ[ℤ] Additive (LineBundleClass M.surface) :=
  M.marking.toLinearEquiv

/-- The Picard marking sends the fixed form to the intersection form on the surface. -/
@[simp]
theorem intersectionBilinForm_picardMarking (x y : L) :
    letI : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    Chow.intersectionBilinForm k M.surface (M.picardMarking x) (M.picardMarking y) = B x y :=
  M.marking.map_app y x

@[simp]
theorem compEvaluation_picardMarking {Y : Scheme.{u}} (g : X ⟶ Y) (a : L) :
    (M.compEvaluation g).picardMarking a = M.picardMarking a := (rfl)

/-- A perfect pairing on the marked lattice gives a perfect Picard intersection pairing. -/
theorem isPerfPair_intersectionForm [B.IsPerfPair] :
    letI : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    (Chow.intersectionBilinForm k M.surface).IsPerfPair := by
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : M.surface.IsProjectiveOver k := M.projective
  refine LinearMap.IsPerfPair.congr B M.marking.toLinearEquiv.symm
    M.marking.toLinearEquiv.symm _ (LinearMap.ext₂ fun x y ↦ ?_)
  simpa only [LinearMap.compl₁₂_apply, LinearEquiv.symm_symm, LinearEquiv.coe_coe,
    LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv] using M.marking.map_app y x

/-- The closed subscheme defined by the boundary ideal is at worst nodal over the ground field. -/
theorem boundaryIdeal_nodal :
    AtWorstNodalOfRelativeDimensionOne
      (M.pair.hom.left.ker.subschemeι ≫ (M.surface ↘ S)) := by
  have : IsClosedImmersion M.pair.hom.left := M.closedImmersion
  have : PrestableFamily M.pair.left.hom := M.prestable
  have hi : M.pair.hom.left.toImage ≫ M.pair.hom.left.ker.subschemeι = M.pair.hom.left :=
    M.pair.hom.left.toImage_imageι
  have hOver : M.pair.hom.left ≫ (M.surface ↘ S) = M.pair.left.hom := Over.w M.pair.hom
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @AtWorstNodalOfRelativeDimensionOne)
    M.pair.hom.left.toImage, ← Category.assoc, hi, hOver]
  exact PrestableFamily.atWorstNodalOfRelativeDimensionOne

variable {M} {L' : Type u} [AddCommGroup L'] {B' : LinearMap.BilinForm ℤ L'} {X' : Scheme.{u}}
  {N : MarkedSurface k n B' X'}

/-- The surface isomorphism underlying an isomorphism of marked surface pairs. -/
@[expose]
def surfaceIso (e : M.pair ≅ N.pair) : M.surface ≅ N.surface :=
  (Arrow.rightFunc ⋙ Over.forget S).mapIso e

variable (M N) in
/-- A surface isomorphism over the ground field that pulls back the target boundary ideal to
the source boundary ideal lifts to an isomorphism of pairs. -/
theorem exists_pairIso_of_boundaryIdeal (g : M.surface ≅ N.surface)
    (hover : g.hom ≫ (N.surface ↘ S) = M.surface ↘ S)
    (hker : N.pair.hom.left.ker.comap g.hom = M.pair.hom.left.ker) :
    ∃ e : M.pair ≅ N.pair, (surfaceIso e).hom = g.hom := by
  have : IsClosedImmersion M.pair.hom.left := M.closedImmersion
  have : IsClosedImmersion N.pair.hom.left := N.closedImmersion
  obtain ⟨d, hd⟩ := N.pair.hom.left.ker.exists_iso_of_comap_eq_ker g M.pair.hom.left hker
  let d' := d ≪≫ (asIso N.pair.hom.left.toImage).symm
  have hi : N.pair.hom.left.toImage ≫ N.pair.hom.left.ker.subschemeι = N.pair.hom.left :=
    N.pair.hom.left.toImage_imageι
  have hd' : d'.hom ≫ N.pair.hom.left = M.pair.hom.left ≫ g.hom := by
    simpa only [d', Iso.trans_hom, Iso.symm_hom, ← hi, Category.assoc, asIso_inv,
      IsIso.inv_hom_id_assoc] using hd
  have hdOver : d'.hom ≫ N.pair.left.hom = M.pair.left.hom := by
    have hover' : g.hom ≫ N.pair.right.hom = M.pair.right.hom := hover
    rw [← Over.w N.pair.hom, ← Category.assoc, hd', Category.assoc, hover', Over.w M.pair.hom]
  let e := Arrow.isoMk (Over.isoMk d' hdOver) (Over.isoMk g hover) (by ext1; exact hd')
  exact ⟨e, rfl⟩

/-- The boundary isomorphism underlying an isomorphism of marked surface pairs. -/
def boundaryIso (e : M.pair ≅ N.pair) : M.boundary ≅ N.boundary :=
  (Arrow.leftFunc ⋙ Over.forget S).mapIso e

instance (e : M.pair ≅ N.pair) : (surfaceIso e).hom.IsOver S :=
  ⟨Over.w e.hom.right⟩

/-- An isomorphism of marked pairs intertwines the two boundary immersions. -/
@[reassoc]
theorem boundaryIso_hom_comp (e : M.pair ≅ N.pair) :
    (boundaryIso e).hom ≫ N.pair.hom.left = M.pair.hom.left ≫ (surfaceIso e).hom :=
  congrArg (fun f ↦ f.left) (Arrow.w e.hom)

instance (e : M.pair ≅ N.pair) : (boundaryIso e).hom.IsOver S :=
  ⟨Over.w e.hom.left⟩

@[simp]
theorem surfaceIso_refl : surfaceIso (M := M) (N := M) (Iso.refl M.pair) =
    Iso.refl M.surface :=
  Functor.mapIso_refl _ _

@[simp]
theorem boundaryIso_refl : boundaryIso (M := M) (N := M) (Iso.refl M.pair) =
    Iso.refl M.boundary :=
  Functor.mapIso_refl _ _

/-- Changing the evaluation preserves the action of the identity on the numbered branches. -/
theorem boundaryCycleAction_compEvaluation_refl {Y : Scheme.{u}} (g : X ⟶ Y) :
    letI : PrestableFamily (M.boundary ↘ S) := M.prestable
    letI : PrestableFamily ((M.compEvaluation g).boundary ↘ S) := (M.compEvaluation g).prestable
    letI : (boundaryIso (M := M) (N := M.compEvaluation g) (Iso.refl M.pair)).hom.IsOver S :=
      ⟨by erw [boundaryIso_refl (M := M), Iso.refl_hom]; exact Category.id_comp _⟩
    (boundaryIso (M := M) (N := M.compEvaluation g) (Iso.refl M.pair)).boundaryCycleAction
      M.cycle (M.compEvaluation g).cycle = 1 := by
  let : PrestableFamily (M.boundary ↘ S) := M.prestable
  let e : M.boundary ≅ M.boundary := boundaryIso (M := M) (N := M.compEvaluation g) (.refl M.pair)
  have he : e = Iso.refl M.boundary := boundaryIso_refl (M := M)
  let : e.hom.IsOver S := ⟨by
    rw [he, Iso.refl_hom]
    exact Category.id_comp _⟩
  let : (Iso.refl M.boundary).hom.IsOver S := by
    rw [Iso.refl_hom]
    infer_instance
  exact (e.boundaryCycleAction_congr M.cycle M.cycle _ he).trans
    (Iso.boundaryCycleAction_refl (X := M.boundary) M.cycle)

@[simp]
theorem surfaceIso_symm (e : M.pair ≅ N.pair) :
    surfaceIso (M := N) (N := M) e.symm = (surfaceIso e).symm :=
  Functor.mapIso_symm (Arrow.rightFunc ⋙ Over.forget S) e

@[simp]
theorem boundaryIso_symm (e : M.pair ≅ N.pair) :
    boundaryIso (M := N) (N := M) e.symm = (boundaryIso e).symm :=
  Functor.mapIso_symm (Arrow.leftFunc ⋙ Over.forget S) e

variable {L'' : Type u} [AddCommGroup L''] {B'' : LinearMap.BilinForm ℤ L''} {X'' : Scheme.{u}}
  {O : MarkedSurface k n B'' X''}

@[simp]
theorem surfaceIso_trans (e : M.pair ≅ N.pair) (f : N.pair ≅ O.pair) :
    surfaceIso (M := M) (N := O) (e ≪≫ f) = surfaceIso e ≪≫ surfaceIso f :=
  Functor.mapIso_trans _ _ _

@[simp]
theorem boundaryIso_trans (e : M.pair ≅ N.pair) (f : N.pair ≅ O.pair) :
    boundaryIso (M := M) (N := O) (e ≪≫ f) = boundaryIso e ≪≫ boundaryIso f :=
  Functor.mapIso_trans _ _ _

end MarkedSurface

end QPainleve.SignedClusterModularGroup

namespace QPainleve.SignedClusterModularGroup

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k] {n : ℕ} [NeZero n]
  {L : Type u} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}

namespace MarkedSurface

variable {ι : Type u}
  (M : MarkedSurface k n B (QPainleve.CharacterTorus.scheme k (ι →₀ ℤ)))

local notation "invX" => QPainleve.CharacterTorus.map k
  (AddEquiv.toAddMonoidHom (AddEquiv.neg (ι →₀ ℤ)))

/-- Read the same marked pair with the opposite boundary orientation and all
independent X coordinates inverted. The underlying pair is definitionally the
same so its Picard classes and rational maps have the same source. -/
@[expose]
def invert : MarkedSurface k n B (QPainleve.CharacterTorus.scheme k (ι →₀ ℤ)) :=
  letI : PrestableFamily (M.boundary ↘ Spec (.of k)) := M.prestable
  { M.compEvaluation invX with cycle := M.cycle.reverse }

@[simp]
theorem invert_pair : M.invert.pair = M.pair := (rfl)

@[simp]
theorem invert_evaluation :
    M.invert.evaluation = M.evaluation.compHom invX := (rfl)

@[simp]
theorem invert_picardMarking (a : L) :
    M.invert.picardMarking a = M.picardMarking a := (rfl)

@[simp]
theorem invert_cycle :
    let : PrestableFamily (M.boundary ↘ Spec (.of k)) := M.prestable
    M.invert.cycle = M.cycle.reverse := (rfl)

/-- The identity pair isomorphism reverses the numbered boundary of the inverted frame. -/
theorem boundaryCycleAction_invert_refl :
    letI : PrestableFamily (M.boundary ↘ Spec (.of k)) := M.prestable
    letI : PrestableFamily (M.invert.boundary ↘ Spec (.of k)) := M.invert.prestable
    letI : (boundaryIso (M := M) (N := M.invert) (Iso.refl M.pair)).hom.IsOver
        (Spec (.of k)) := ⟨by
          erw [boundaryIso_refl (M := M), Iso.refl_hom]
          exact Category.id_comp (M.boundary ↘ Spec (.of k))⟩
    (boundaryIso (M := M) (N := M.invert) (Iso.refl M.pair)).boundaryCycleAction
      M.cycle M.invert.cycle = DihedralGroup.sr 0 := by
  let : PrestableFamily (M.boundary ↘ Spec (.of k)) := M.prestable
  have he : (boundaryIso (M := M) (N := M.invert) (Iso.refl M.pair)).hom.IsOver
      (Spec (.of k)) := ⟨by
        erw [boundaryIso_refl (M := M), Iso.refl_hom]
        exact Category.id_comp (M.boundary ↘ Spec (.of k))⟩
  have hf : (Iso.refl M.boundary).hom.IsOver (Spec (.of k)) := by
    rw [Iso.refl_hom]
    infer_instance
  exact (Iso.boundaryCycleAction_congr _ M.cycle M.cycle.reverse _
    (boundaryIso_refl (M := M))).trans
    (Iso.boundaryCycleAction_refl_reverse (X := M.boundary) M.cycle)

end MarkedSurface

end QPainleve.SignedClusterModularGroup
