/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Words

import QPainleve.SignedClusterModularGroup.Examples.FourVertex.NormalForm

/-!
# Generators of the four-vertex cluster modular groups

The rotation and translation generate the unsigned group of independent X maps.
Adjoining the reflection generates the signed group. The words are those of
Bershtein, Gavrylenko and Marshakov, equation (3.1), in reciprocal coordinates.
Completeness follows from the normal forms in the rotation, translation,
and reflection.
-/

public section

open CategoryTheory

namespace QPainleve.FourVertex

open Cluster
open Subgroup (eq_top_iff' mul_mem pow_mem subset_closure zpow_mem)

variable (k : Type*) [Field k]

local notation "B" => exchangeMatrix
local notation "Γ" => ClusterModularGroup k B
local notation "Γ̂" => SignedClusterModularGroup k B
local notation "signed[" w "]" => signedClusterModularGroupMap k B (End.of w)
local notation "unsigned[" w "," h "]" =>
  clusterModularGroupMap k B
    (Subtype.mk (End.of w) (Iff.mpr (mem_inversionFreeLoops_iff B (End.of w)) h))

/-- The reflection, rotation and translation generate the signed group of
independent X maps of the four-vertex seed over `k`. -/
theorem closure_signedClusterModularGroup_generators :
    Subgroup.closure ({signed[reflectionWord], signed[rotationWord], signed[translationWord]} :
      Set Γ̂) = ⊤ := by
  apply (eq_top_iff' _).mpr
  intro g
  obtain ⟨a, rfl⟩ := (signedNormalFormEquiv k).surjective g
  rw [signedNormalFormEquiv_apply]
  exact mul_mem (mul_mem (pow_mem (subset_closure (by simp)) _)
    (zpow_mem (subset_closure (by simp)) _)) (pow_mem (subset_closure (by simp)) _)

/-- The rotation and translation generate the unsigned group of independent X
maps of the four-vertex seed over `k`. -/
theorem closure_clusterModularGroup_generators :
    Subgroup.closure ({unsigned[rotationWord,inversionCount_rotationWord],
      unsigned[translationWord,inversionCount_translationWord]} : Set Γ) = ⊤ := by
  apply (eq_top_iff' _).mpr
  intro g
  obtain ⟨a, rfl⟩ := (unsignedNormalFormEquiv k).surjective g
  rw [unsignedNormalFormEquiv_apply]
  exact mul_mem (pow_mem (subset_closure (by simp)) _) (zpow_mem (subset_closure (by simp)) _)

end QPainleve.FourVertex
