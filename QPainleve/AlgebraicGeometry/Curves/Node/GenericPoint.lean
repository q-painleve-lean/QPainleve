/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction
public import QPainleve.AlgebraicGeometry.Curves.Node.NormalizationComponent

import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Map
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

/-- A numbered node lies on a numbered component exactly when that component is an
endpoint of one of the node's ordered branches. -/
theorem node_mem_closure_componentGenericPoint_iff (i j : ZMod n) :
    (X.singularLocus k).subschemeι (A.node i) ∈ closure {A.componentGenericPoint j} ↔
      ∃ b : Fin 2, (TauCeti.DualGraph.cycle n).endpoint i b = j := by
  let z := (X.singularLocus k).subschemeι (A.node i)
  let e := X.branchSchemeToBlowup k
  have hrange : Set.range ((X.blowupComponent (K := k) (A.component j)).ι ≫ ν[X]) =
      closure {A.componentGenericPoint j} := by
    simpa [← A.componentGenericPoint_def] using
      X.range_blowupComponent_comp (A.component j) (𝟙 X) (𝟙 X : X ⟶ X).isClosedMap
  rw [← hrange]
  constructor
  · rintro ⟨x, hx⟩
    have hz : (ν[X]) x.val = z := hx
    have hr : x.val ∈ Set.range e := by
      dsimp only [e]
      rw [X.range_branchSchemeToBlowup, Set.mem_preimage, hz,
        ← (X.singularLocus k).range_subschemeι]
      exact Set.mem_range_self _
    obtain ⟨q, hq⟩ := hr
    obtain ⟨⟨a, b⟩, rfl⟩ := A.branch.surjective q
    have ha : a = i := by
      apply A.node.injective
      apply (X.singularLocus k).subschemeι.injective
      have h := congrArg (ν[X]) hq
      dsimp only [e] at h
      rw [X.blowupToBase_branchSchemeToBlowup_apply,
        A.branchSchemeToSingularLocus_branch, hz] at h
      exact h
    subst a
    refine ⟨b, A.component.injective
      ((A.branchSchemeToBlowup_branch_mem_component_iff i b (A.component j)).mp ?_)⟩
    rw [hq, ← X.coe_blowupComponent]
    exact x.property
  · rintro ⟨b, hb⟩
    have h := (A.branchSchemeToBlowup_branch_mem_component_iff i b (A.component j)).mpr
      (congrArg A.component hb)
    rw [← X.coe_blowupComponent] at h
    refine ⟨⟨e (A.branch (i, b)), h⟩, ?_⟩
    -- Evaluate the composite on the point represented in the component open.
    change (ν[X]) (e (A.branch (i, b))) = z
    dsimp only [e, z]
    rw [X.blowupToBase_branchSchemeToBlowup_apply, A.branchSchemeToSingularLocus_branch]

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
