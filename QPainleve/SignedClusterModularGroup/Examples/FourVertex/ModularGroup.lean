/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Words

import QPainleve.SignedClusterModularGroup.Examples.FourVertex.MarkedAction

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

open Cluster

local notation "B" => exchangeMatrix
local notation "Γ" => ClusterModularGroup ℂ B
local notation "Γ̂" => SignedClusterModularGroup ℂ B
local notation "signed[" w "]" => signedClusterModularGroupMap ℂ B (End.of w)
local notation "unsigned[" w "," h "]" =>
  clusterModularGroupMap ℂ B
    (Subtype.mk (End.of w) (Iff.mpr (mem_inversionFreeLoops_iff B (End.of w)) h))

/-- The reflection, rotation and translation generate the signed group of
independent X maps of the four-vertex seed over ℂ. -/
theorem closure_signedClusterModularGroup_generators :
    Subgroup.closure ({signed[reflectionWord], signed[rotationWord], signed[translationWord]} :
      Set Γ̂) = ⊤ := by
  have h := closure_four_vertex_signed_words ℂ markedPicardEquiv.toMonoidHom
    markedPicardEquiv.injective (picardInvariants_markedPicardEquiv_loop rotationWord)
    (picardInvariants_markedPicardEquiv_loop translationWord)
    (picardInvariants_markedPicardEquiv_loop reflectionWord)
  rw [← Subgroup.unop_eq_top, Subgroup.unop_closure, ← Set.image_singleton,
    ← Set.image_insert_eq, ← Set.image_insert_eq, Set.preimage_image_eq _ op_injective] at h
  exact h

/-- The rotation and translation generate the unsigned group of independent X
maps of the four-vertex seed over ℂ. -/
theorem closure_clusterModularGroup_generators :
    Subgroup.closure ({unsigned[rotationWord,inversionCount_rotationWord],
      unsigned[translationWord,inversionCount_translationWord]} : Set Γ) = ⊤ := by
  have h := closure_four_vertex_unsigned_words ℂ markedPicardEquiv.toMonoidHom
    markedPicardEquiv.injective (fun g ↦ by
      simpa only [SignedBoundaryIsometryGroup.sign_apply, MonoidHom.op_apply_apply,
        Function.comp_apply, MulEquiv.coe_toMonoidHom] using sign_markedPicardEquiv_inclusion g)
    (picardInvariants_markedPicardEquiv_loop rotationWord)
    (picardInvariants_markedPicardEquiv_loop translationWord)
  rw [← Subgroup.unop_eq_top, Subgroup.unop_closure, ← Set.image_singleton,
    ← Set.image_insert_eq, Set.preimage_image_eq _ op_injective] at h
  exact h

end QPainleve.FourVertex
