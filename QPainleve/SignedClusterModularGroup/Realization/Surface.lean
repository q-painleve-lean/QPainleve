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

/-- The underlying Picard marking, with tensor product written additively. -/
def picardMarking : L ≃ₗ[ℤ] Additive (LineBundleClass M.surface) :=
  M.marking.toLinearEquiv

variable {M} {L' : Type u} [AddCommGroup L'] {B' : LinearMap.BilinForm ℤ L'} {X' : Scheme.{u}}
  {N : MarkedSurface k n B' X'}

/-- The surface isomorphism underlying an isomorphism of marked surface pairs. -/
@[expose]
def surfaceIso (e : M.pair ≅ N.pair) : M.surface ≅ N.surface :=
  (Arrow.rightFunc ⋙ Over.forget S).mapIso e

/-- The boundary isomorphism underlying an isomorphism of marked surface pairs. -/
def boundaryIso (e : M.pair ≅ N.pair) : M.boundary ≅ N.boundary :=
  (Arrow.leftFunc ⋙ Over.forget S).mapIso e

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
  { M with
    cycle := M.cycle.reverse
    evaluation := M.evaluation.compHom invX }

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
  have compare (e f : M.boundary ≅ M.boundary)
      [e.hom.IsOver (Spec (.of k))] [f.hom.IsOver (Spec (.of k))] (h : e = f) :
      e.boundaryCycleAction M.cycle M.cycle.reverse =
        f.boundaryCycleAction M.cycle M.cycle.reverse := by
    subst f
    rfl
  have he : (boundaryIso (M := M) (N := M.invert) (Iso.refl M.pair)).hom.IsOver
      (Spec (.of k)) := ⟨by
        erw [boundaryIso_refl (M := M), Iso.refl_hom]
        exact Category.id_comp (M.boundary ↘ Spec (.of k))⟩
  have hf : (Iso.refl M.boundary).hom.IsOver (Spec (.of k)) := by
    rw [Iso.refl_hom]
    infer_instance
  exact (@compare _ _ he hf (boundaryIso_refl (M := M))).trans
    (Iso.boundaryCycleAction_refl_reverse (X := M.boundary) M.cycle)

end MarkedSurface

end QPainleve.SignedClusterModularGroup
