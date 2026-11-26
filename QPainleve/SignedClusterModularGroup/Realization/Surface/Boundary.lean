/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Surface

/-!
# Constructing marked surfaces from a numbered boundary

The closed immersion of a numbered boundary, its surface's Picard marking, and
a rational evaluation give a marked surface on the original schemes.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry

namespace QPainleve.SignedClusterModularGroup

universe u

variable {K : Type u} [Field K] [IsSepClosed K] [Infinite K]

local notation "S" => Spec (CommRingCat.of K)

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] [IsIntegral X] [X.IsProjectiveOver K]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (CommRingCat.of K))] {n : ℕ} [NeZero n]
  {L : Type u} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}

/-- Package a numbered closed boundary and a Picard marking with a rational evaluation. -/
-- The underlying surface and boundary must reduce to their given schemes.
@[expose, simps pair evaluation]
def MarkedSurface.ofBoundary (D : X.IdealSheafData)
    [PrestableFamily (D.subscheme ↘ S)]
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (μ : B.IsometryEquiv (Chow.intersectionBilinForm K X))
    {Y : Scheme.{u}} (f : X ⤏ Y) : MarkedSurface K n B Y where
  pair := Arrow.mk (Over.homMk (U := Over.mk (D.subscheme ↘ S)) (V := Over.mk (X ↘ S))
    D.subschemeι (D.over_eq_subschemeι_comp.symm))
  closedImmersion := inferInstanceAs (IsClosedImmersion D.subschemeι)
  integral := inferInstanceAs (IsIntegral X)
  smooth := inferInstanceAs (SmoothOfRelativeDimension 2 (X ↘ S))
  projective := inferInstanceAs (X.IsProjectiveOver K)
  prestable := inferInstanceAs (PrestableFamily (D.subscheme ↘ S))
  cycle := A
  marking := μ
  evaluation := f

/-- The Picard marking of a packaged boundary is the supplied isometry. -/
@[simp]
theorem MarkedSurface.ofBoundary_picardMarking (D : X.IdealSheafData)
    [PrestableFamily (D.subscheme ↘ S)]
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (μ : B.IsometryEquiv (Chow.intersectionBilinForm K X))
    {Y : Scheme.{u}} (f : X ⤏ Y) (x : L) :
    (MarkedSurface.ofBoundary D A μ f).picardMarking x = μ x := by
  rw [MarkedSurface.picardMarking_apply]
  rfl

/-- The defining ideal of the packaged boundary is the original ideal. -/
@[simp]
theorem MarkedSurface.ofBoundary_ker (D : X.IdealSheafData)
    [PrestableFamily (D.subscheme ↘ S)]
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (μ : B.IsometryEquiv (Chow.intersectionBilinForm K X))
    {Y : Scheme.{u}} (f : X ⤏ Y) :
    (MarkedSurface.ofBoundary D A μ f).pair.hom.left.ker = D :=
  D.ker_subschemeι

/-- The line bundle of the packaged boundary has the class of the original Cartier divisor. -/
theorem MarkedSurface.ofBoundary_boundaryIdeal_class (D : X.IdealSheafData)
    [PrestableFamily (D.subscheme ↘ S)]
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (μ : B.IsometryEquiv (Chow.intersectionBilinForm K X))
    {Y : Scheme.{u}} (f : X ⤏ Y)
    (hD' : (MarkedSurface.ofBoundary D A μ f).pair.hom.left.ker.IsEffectiveCartier)
    (hD : D.IsEffectiveCartier) :
    (LineBundleClass.mk hD'.toInvertibleSheaf)⁻¹ = (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ :=
  congrArg Inv.inv (LineBundleClass.mk_toInvertibleSheaf_congr _ _
    (MarkedSurface.ofBoundary_ker D A μ f))

/-- The packaged cycle retains the specified numbering on the closed boundary. -/
@[simp]
theorem MarkedSurface.ofBoundary_cycle (D : X.IdealSheafData)
    [PrestableFamily (D.subscheme ↘ S)]
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (μ : B.IsometryEquiv (Chow.intersectionBilinForm K X))
    {Y : Scheme.{u}} (f : X ⤏ Y) :
    (MarkedSurface.ofBoundary D A μ f).cycle = A :=
  (rfl)

end QPainleve.SignedClusterModularGroup
