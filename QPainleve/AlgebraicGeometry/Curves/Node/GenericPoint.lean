/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction
public import QPainleve.AlgebraicGeometry.Curves.Node.NormalizationComponent

import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus

/-!
# Generic points of numbered boundary components

The dihedral action of an isomorphism of numbered nodal curves can be read on
the images of the normalized components' generic points in the curves themselves.
This compares the cycle numbering with the boundary primes of an ambient surface.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory DihedralGroup TopologicalSpace
open TauCeti.AlgebraicGeometry
open Scheme (NodalCycleNumbering)

universe u v w

variable {k : Type u} [Field k] [IsSepClosed k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [PrestableFamily (X ↘ Spec (.of k))] [PrestableFamily (Y ↘ Spec (.of k))]
  {α : Type v} {β : Type w}
  {p : α → (X ↘ Spec (.of k)).smoothLocus} {q : β → (Y ↘ Spec (.of k)).smoothLocus}
  {n : ℕ} [NeZero n]

local notation "ν[" Z "]" => Scheme.IdealSheafData.blowupToBase (Scheme.singularLocus k Z)
local notation "η" => genericPoints.ofComponent

namespace AlgebraicGeometry.Scheme.NodalCycleNumbering

variable (A : NodalCycleNumbering p n)

/-- The generic point of a numbered component, viewed as a point of the nodal curve. -/
def componentGenericPoint (j : ZMod n) : X := ν[X] (η (A.component j))

/-- The generic point is the image of the corresponding normalized generic point. -/
theorem componentGenericPoint_def (j : ZMod n) :
    A.componentGenericPoint j = ν[X] (η (A.component j)) :=
  (rfl)

/-- Reversing the cycle negates the index of each component's generic point. -/
@[simp]
theorem reverse_componentGenericPoint (j : ZMod n) :
    A.reverse.componentGenericPoint j = A.componentGenericPoint (-j) := by
  simp only [componentGenericPoint_def, reverse_component]

/-- Distinct numbered components have distinct generic points in the nodal curve. -/
theorem componentGenericPoint_injective : Function.Injective A.componentGenericPoint := by
  intro j l h
  have hη : η (A.component j) = η (A.component l) := Subtype.ext
    ((ν[X]).injOn_preimage_isoLocus
      (X.blowupComponentGeneric_mem_isoLocus (A.component j))
      (X.blowupComponentGeneric_mem_isoLocus (A.component l))
      (by simpa only [componentGenericPoint_def] using h))
  apply A.component.injective
  simpa only [genericPoints.component_ofComponent] using congrArg genericPoints.component hη

end AlgebraicGeometry.Scheme.NodalCycleNumbering

namespace CategoryTheory.Iso

/-- An isomorphism sends each component's generic point to that of its dihedral image. -/
theorem apply_componentGenericPoint (e : X ≅ Y) [e.hom.IsOver (Spec (.of k))]
    (A : NodalCycleNumbering p n) (B : NodalCycleNumbering q n) (j : ZMod n) :
    e.hom (A.componentGenericPoint j) =
      B.componentGenericPoint (cycleVertexPerm (e.boundaryCycleAction A B) j) := by
  let t := e.singularLocusBlowupIso (R := k)
  let l := cycleVertexPerm (e.boundaryCycleAction A B) j
  have h := (genericPoints.isGenericPoint_ofComponent (A.component j)).image t.hom.continuous
  have hγ : t.hom (η (A.component j)) = η (B.component l) := by
    rw [← e.component_boundaryCycleAction A B j,
      (isClosed_of_mem_irreducibleComponents _ (B.component l).property).closure_eq] at h
    exact h.eq (genericPoints.isGenericPoint_ofComponent (B.component l))
  rw [A.componentGenericPoint_def, B.componentGenericPoint_def, ← hγ]
  simpa only [Scheme.Hom.comp_apply] using
    congrArg (fun f : (X.singularLocus k).blowup ⟶ Y ↦ f (η (A.component j)))
      (e.singularLocusBlowupIso_hom_blowupToBase (R := k)).symm

end CategoryTheory.Iso
