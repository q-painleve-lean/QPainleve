/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Subdivision
public import QPainleve.AlgebraicGeometry.Curves.Node.GenericPoint

import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.Data.ZMod.CyclicOrder

/-!
# Component order under oriented nodal contractions

Cutting a source cycle at the component over target component zero orders the
surviving components linearly. The ordered branches at the retained nodes
force this order to agree with the target numbering.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti TauCeti.AlgebraicGeometry
open Scheme (NodalCycleNumbering)

universe u v w

namespace AlgebraicGeometry.Scheme.Hom.IsOrientedCycleSubdivision

variable {k : Type u} [Field k] [IsSepClosed k] {X Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [PrestableFamily (X ↘ Spec (.of k))] [PrestableFamily (Z ↘ Spec (.of k))]
  {α : Type v} {β : Type w}
  {pX : α → (X ↘ Spec (.of k)).smoothLocus} {pZ : β → (Z ↘ Spec (.of k)).smoothLocus}
  {n m : ℕ} [NeZero n] [NeZero m]
  {C : NodalCycleNumbering pZ m} {A : NodalCycleNumbering pX n} {f : Z ⟶ X}

local notation "ν[" Y "]" => Scheme.IdealSheafData.blowupToBase (Scheme.singularLocus k Y)
local notation "Yν[" Y "]" => Scheme.IdealSheafData.blowup (Scheme.singularLocus k Y)
local notation "η" => genericPoints.ofComponent
local notation "branch[" Y "," A "," j "," b "]" =>
  Scheme.branchSchemeToBlowup k Y (NodalCycleNumbering.branch A (j, b))

private theorem exists_componentIndex (g : Yν[Z] ⟶ Yν[X]) :
    ∃ a : ZMod m → ZMod n, ∀ j,
      Set.MapsTo g (C.component j : Set Yν[Z]) (A.component (a j) : Set Yν[X]) := by
  classical
  have h j : ∃ l, Set.MapsTo g (C.component j : Set Yν[Z]) (A.component l : Set Yν[X]) := by
    have hirr := (C.component j).property.1.image g g.continuous.continuousOn
    obtain ⟨U, hU, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hirr
    obtain ⟨l, hl⟩ := A.component.surjective ⟨U, hU⟩
    refine ⟨l, fun x hx ↦ ?_⟩
    rw [hl]
    exact hsub (Set.mem_image_of_mem g hx)
  choose a ha using h
  exact ⟨a, ha⟩

private theorem componentIndex_of_genericPoint
    {g : Yν[Z] ⟶ Yν[X]} (hcomm : CommSq ν[Z] g f ν[X])
    {a : ZMod m → ZMod n}
    (ha : ∀ j, Set.MapsTo g (C.component j : Set Yν[Z]) (A.component (a j) : Set Yν[X]))
    {j : ZMod m} {l : ZMod n} (h : f (C.componentGenericPoint j) = A.componentGenericPoint l) :
    a j = l := by
  have hν : ν[X] (g (η (C.component j))) = ν[X] (η (A.component l)) := by
    rw [← Scheme.Hom.comp_apply, ← hcomm.w, Scheme.Hom.comp_apply,
      ← C.componentGenericPoint_def, ← A.componentGenericPoint_def, h]
  have hl := X.blowupComponentGeneric_mem_isoLocus (A.component l)
  have he := (ν[X]).injOn_preimage_isoLocus (by rwa [Set.mem_preimage, hν]) hl hν
  have hmem := ha j (genericPoints.isGenericPoint_ofComponent (C.component j)).mem
  rw [he] at hmem
  have : IsRegular Yν[X] := X.isRegular_blowup_singularLocus
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  apply A.component.injective
  exact (irreducibleComponentOf_eq_iff.mpr hmem).symm.trans
    (irreducibleComponentOf_eq_iff.mpr (genericPoints.isGenericPoint_ofComponent
      (A.component l)).mem)

private theorem componentIndex_succ
    {g : Yν[Z] ⟶ Yν[X]} {retain : ZMod n ↪ ZMod m}
    (hkeep : ∀ j b, g branch[Z,C,retain j,b] = branch[X,A,j,b])
    (hcollapse : ∀ j ∉ Set.range retain, g branch[Z,C,j,1] = g branch[Z,C,j,0])
    {a : ZMod m → ZMod n}
    (ha : ∀ j, Set.MapsTo g (C.component j : Set Yν[Z]) (A.component (a j) : Set Yν[X]))
    (j : ZMod m) :
    a (j + 1) = a j + if j ∈ Set.range retain then (1 : ZMod n) else 0 := by
  classical
  have hmem (j : ZMod m) (b : Fin 2) :=
    ha ((DualGraph.cycle m).endpoint j b)
      ((C.branchSchemeToBlowup_branch_mem_component_iff j b _).mpr rfl)
  by_cases hj : j ∈ Set.range retain
  · obtain ⟨l, rfl⟩ := hj
    have hindex (b : Fin 2) :
        a ((DualGraph.cycle m).endpoint (retain l) b) = (DualGraph.cycle n).endpoint l b := by
      have hm := hmem (retain l) b
      rw [hkeep] at hm
      exact (A.component.injective
        ((A.branchSchemeToBlowup_branch_mem_component_iff l b _).mp hm)).symm
    rw [ite_eq_left (Set.mem_range_self l)]
    have h₀ := hindex 0
    have h₁ := hindex 1
    simp only [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)] at h₁
    exact h₁.trans (congrArg (· + 1) h₀).symm
  · have hm₀ := hmem j 0
    have hm₁ := hmem j 1
    rw [hcollapse j hj] at hm₁
    have : IsRegular Yν[X] := X.isRegular_blowup_singularLocus
      PrestableFamily.atWorstNodalOfRelativeDimensionOne
    rw [ite_eq_right hj, add_zero]
    apply A.component.injective
    exact (irreducibleComponentOf_eq_iff.mpr hm₁).symm.trans
      (irreducibleComponentOf_eq_iff.mpr hm₀)

/-- In an oriented subdivision, the generic points over the surviving target components
occur in the target order, starting from the source component over component zero. -/
theorem strictMono_componentSection (hf : f.IsOrientedCycleSubdivision C A)
    (survive : ZMod n → ZMod m)
    (hs : ∀ j, f (C.componentGenericPoint (survive j)) = A.componentGenericPoint j) :
    StrictMono fun j : Fin n ↦ (survive (ZMod.finEquiv n j) - survive 0).val := by
  obtain ⟨g, hcomm, _, keep, hkeep, hcollapse⟩ := hf
  obtain ⟨a, ha⟩ := exists_componentIndex (C := C) (A := A) g
  let retain := (A.node.toEmbedding.trans keep).trans C.node.symm.toEmbedding
  have hn (j : ZMod n) : C.node (retain j) = keep (A.node j) := C.node.apply_symm_apply _
  have hretain (j : ZMod m) : j ∈ Set.range retain ↔ C.node j ∈ Set.range keep := by
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨A.node l, (hn l).symm⟩
    · rintro ⟨l, hl⟩
      obtain ⟨l, rfl⟩ := A.node.surjective l
      exact ⟨l, C.node.injective ((hn l).trans hl)⟩
  refine ZMod.strictMono_val_sub_of_succ_eq_add_ite survive retain a
    (fun j ↦ componentIndex_of_genericPoint hcomm ha (hs j)) (componentIndex_succ ?_ ?_ ha)
  · intro j b
    rw [C.branch_eq_branchOrderOfDualGraph, A.branch_eq_branchOrderOfDualGraph, hn]
    exact hkeep (A.node j) b
  · intro j hj
    simpa only [NodalCycleNumbering.branch_eq_branchOrderOfDualGraph] using
      hcollapse (C.node j) (mt (hretain j).mpr hj)

end AlgebraicGeometry.Scheme.Hom.IsOrientedCycleSubdivision
