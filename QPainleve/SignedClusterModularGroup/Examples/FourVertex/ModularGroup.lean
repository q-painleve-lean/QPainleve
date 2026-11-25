/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Words

import QPainleve.SignedClusterModularGroup.Examples.FourVertex.MarkedAction
import QPainleve.SignedClusterModularGroup.Examples.FourVertex.PicardAction

/-!
# Generators of the four-vertex cluster modular groups

The rotation and translation generate the unsigned group of independent X maps.
Adjoining the reflection generates the signed group. The words are those of
Bershtein, Gavrylenko and Marshakov, equation (3.1), in reciprocal coordinates.
Completeness comes from the Picard lattice generation theorem applied to the
marked octagon.
-/

public section

open CategoryTheory MulOpposite Quiver

namespace QPainleve.FourVertex

open Cluster SignedBoundaryIsometryGroup

local notation "B" => exchangeMatrix
local notation "Γ" => ClusterModularGroup ℂ B
local notation "Γ̂" => SignedClusterModularGroup ℂ B
local notation "G" => signedBoundaryIsometryGroup intersectionForm boundaryClass
local notation "η" => sign intersectionForm boundaryClass
local notation "signed[" w "]" => signedClusterModularGroupMap ℂ B (End.of w)
local notation "unsigned[" w "," h "]" =>
  clusterModularGroupMap ℂ B
    (Subtype.mk (End.of w) (Iff.mpr (mem_inversionFreeLoops_iff B (End.of w)) h))
local notation "invariants[" w "]" =>
  Path.signedLoopInvariants w (fun j ↦ (exchangeKernelBasis j : Fin 4 → ℤ))
    boundaryOrders (boundaryOrders 0)

private theorem exists_picardEquiv_with_invariants :
    ∃ ρ : Γ̂ᵐᵒᵖ ≃* G,
      (∀ f : Γᵐᵒᵖ, η (ρ ((clusterModularGroupInclusion ℂ B).op f)) = 1) ∧
      ∀ w : Word B B, picardInvariants (ρ (op signed[w])) = invariants[w] := by
  obtain ⟨ρ, hker, hword⟩ := exists_four_vertex_marked_picard_equiv
  refine ⟨ρ, ?_, ?_⟩
  · intro f
    have hm : clusterModularGroupInclusion ℂ B f.unop ∈
        ((η).comp ρ.toMonoidHom).ker.unop := by
      rw [hker]
      exact ⟨f.unop, rfl⟩
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MonoidHom.op_apply_apply, Function.comp_apply] using
      (MonoidHom.mem_ker.mp (Subgroup.mem_unop.mp hm))
  · intro w
    obtain ⟨hsign, hkernel, j, horders, hpullback⟩ := hword w
    exact (picardInvariants_eq_signedLoopInvariants_iff _ w).mpr
      ⟨hsign, hkernel, j, hpullback, horders.symm⟩

/-- The reflection, rotation and translation generate the signed group of
independent X maps of the four-vertex seed over ℂ. -/
theorem closure_signedClusterModularGroup_generators :
    Subgroup.closure ({signed[reflectionWord], signed[rotationWord], signed[translationWord]} :
      Set Γ̂) = ⊤ := by
  obtain ⟨ρ, _, hword⟩ := exists_picardEquiv_with_invariants
  have h := closure_four_vertex_signed_words ℂ ρ.toMonoidHom ρ.injective
    (hword rotationWord) (hword translationWord) (hword reflectionWord)
  rw [← Subgroup.unop_eq_top, Subgroup.unop_closure, ← Set.image_singleton,
    ← Set.image_insert_eq, ← Set.image_insert_eq, Set.preimage_image_eq _ op_injective] at h
  exact h

/-- The rotation and translation generate the unsigned group of independent X
maps of the four-vertex seed over ℂ. -/
theorem closure_clusterModularGroup_generators :
    Subgroup.closure ({unsigned[rotationWord,inversionCount_rotationWord],
      unsigned[translationWord,inversionCount_translationWord]} : Set Γ) = ⊤ := by
  obtain ⟨ρ, hpos, hword⟩ := exists_picardEquiv_with_invariants
  have h := closure_four_vertex_unsigned_words ℂ ρ.toMonoidHom ρ.injective
    hpos (hword rotationWord) (hword translationWord)
  rw [← Subgroup.unop_eq_top, Subgroup.unop_closure, ← Set.image_singleton,
    ← Set.image_insert_eq, Set.preimage_image_eq _ op_injective] at h
  exact h

end QPainleve.FourVertex
