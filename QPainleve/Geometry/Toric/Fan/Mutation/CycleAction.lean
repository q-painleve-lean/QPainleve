/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.Period.Orientation
public import QPainleve.Geometry.Toric.Fan.Mutation.Orientation

/-!
# Dihedral action of a toric mutation

The elementary transformation of Gross, Hacking and Keel
([*Birational geometry of cluster algebras*, §3.1](https://arxiv.org/html/1309.2573v2#S3.SS1))
carries each normalized toric boundary component to the component of the sheared ray.
The determinant on adjacent rays identifies its dihedral action as a rotation. The
orientation also passes to the original cycles through oriented conductor subdivisions.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Module PointedCone
open Scheme (NodalCycleNumbering)
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : ℂˣ) (hΦ : Φ.IsRegular)

local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hOpp) hΦ
local notation "shear" => Φ.mutationFanRayEquiv b hv hp hOpp
local notation "base" => Spec (CommRingCat.of ℂ)

variable [hΦ₀ : Nonempty Φ.cones]
  [hΨ₀ : Nonempty (Φ.mutationFan b ρ.primitiveGenerator_ne_zero
    ρ.hull_primitiveGenerator_mem hOpp).cones]

local notation "C₀" => Scheme.IdealSheafData.subscheme (Φ.boundaryIdeal hΦ₀)
local notation "C₁" => Scheme.IdealSheafData.subscheme (boundaryIdeal (Ψ) hΨ₀)
local notation "e" => ρ.mutationBoundaryIso b hOpp c hΦ

variable [PrestableFamily ((Φ.boundaryIdeal hΦ₀).subscheme ↘ base)]
  [PrestableFamily (((Φ.mutationFan b ρ.primitiveGenerator_ne_zero
    ρ.hull_primitiveGenerator_mem hOpp).boundaryIdeal hΨ₀).subscheme ↘ base)]
  {m : ℕ} [NeZero m] {ι₀ ι₁ : Type*}
  {p₀ : ι₀ → ((Φ.boundaryIdeal hΦ₀).subscheme ↘ base).smoothLocus}
  {p₁ : ι₁ → (((Φ.mutationFan b ρ.primitiveGenerator_ne_zero
    ρ.hull_primitiveGenerator_mem hOpp).boundaryIdeal hΨ₀).subscheme ↘ base).smoothLocus}
  (A : NodalCycleNumbering p₀ m) (B : NodalCycleNumbering p₁ m)
  {u : ZMod m ≃ Φ.Ray} {w : ZMod m ≃ (Φ.mutationFan b ρ.primitiveGenerator_ne_zero
    ρ.hull_primitiveGenerator_mem hOpp).Ray}
  (hu : ∀ j, A.component j = Φ.boundaryNormalizationComponentEquiv hΦ (u j))
  (hw : ∀ j, B.component j = (Φ.mutationFan b ρ.primitiveGenerator_ne_zero
      ρ.hull_primitiveGenerator_mem hOpp).boundaryNormalizationComponentEquiv
    ((Φ.isRegular_mutationFan_iff b ρ.primitiveGenerator_ne_zero
      ρ.hull_primitiveGenerator_mem hOpp).mpr hΦ) (w j))

include hu hw in
/-- The vertex action on the numbered boundary of a mutation is the shear on ray labels. -/
theorem Ray.mutationBoundaryIso_cycleVertexPerm (j : ZMod m) :
    w (cycleVertexPerm ((e).boundaryCycleAction A B) j) = shear (u j) := by
  have h := (e).component_boundaryCycleAction A B j
  rw [hu, hw, ρ.image_boundaryNormalizationComponent_mutationBoundaryIso b hOpp c hΦ] at h
  exact (boundaryNormalizationComponentEquiv (Ψ) hΨ).injective (Subtype.ext h)

variable
  (hAdjacent : b.detDualEquiv (u 0).primitiveGenerator (u 1).primitiveGenerator = 1 ∧
    ∃ σ : Φ.cones, (u 0).toCone ≤ σ ∧ (u 1).toCone ≤ σ)
  (hPositive : ∀ j, b.detDualEquiv (w j).primitiveGenerator (w (j + 1)).primitiveGenerator = 1)

include hu hw hAdjacent hPositive in
/-- Mutation preserves the branch order at every node when the target numbering is
positive and the first consecutive pair of source rays is positive in a common cone. -/
theorem Ray.cycleOrientationSign_mutationBoundaryIso :
    cycleOrientationSign ((e).boundaryCycleAction A B) = 1 := by
  set g := (e).boundaryCycleAction A B
  have hRay := ρ.mutationBoundaryIso_cycleVertexPerm b hOpp c hΦ A B hu hw
  obtain ⟨hdet, σ, h₀, h₁⟩ := hAdjacent
  have himage := Φ.detDualEquiv_mutationFanRayEquiv_of_le b hv hp hOpp h₀ h₁
  rw [← hRay 0, ← hRay 1, hdet] at himage
  rcases hg : g with l | l
  · exact cycleOrientationSign_r l
  · have hstep : cycleVertexPerm g 1 + 1 = cycleVertexPerm g 0 := by
      simp [hg]
    have hpos := hPositive (cycleVertexPerm g 1)
    rw [hstep, b.detDualEquiv_swap, himage] at hpos
    norm_num at hpos

variable {X Y : Scheme} [X.Over base] [Y.Over base]
  [PrestableFamily (X ↘ base)] [PrestableFamily (Y ↘ base)]
  {n : ℕ} [NeZero n]
  {α β : Type*} {pX : α → (X ↘ base).smoothLocus} {pY : β → (Y ↘ base).smoothLocus}

include hu hw hAdjacent hPositive in
/-- When a toric mutation descends through oriented conductor subdivisions, the
descended boundary isomorphism preserves orientation, including on cycles with
one or two components. -/
theorem Ray.cycleOrientationSign_of_mutationBoundaryIso_descends
    (D : NodalCycleNumbering pX n) (E : NodalCycleNumbering pY n)
    (d : X ≅ Y) [d.hom.IsOver base]
    {f : C₀ ⟶ X} {g : C₁ ⟶ Y} [f.IsOver base] [g.IsOver base]
    (hf : f.IsOrientedCycleSubdivision A D) (hg : g.IsOrientedCycleSubdivision B E)
    (h : CommSq (e).hom f g d.hom) :
    cycleOrientationSign (d.boundaryCycleAction D E) = 1 :=
  (d.cycleOrientationSign_eq_of_orientedCycleSubdivisions D E A B e hf hg h).trans
    (ρ.cycleOrientationSign_mutationBoundaryIso b hOpp c hΦ A B hu hw hAdjacent hPositive)

end TauCeti.Toric.Fan
