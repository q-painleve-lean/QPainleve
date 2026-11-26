/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import QPainleve.Algebra.Cluster.Word.Specialization
public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Words

import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Relations

/-!
# Field specialization of the four-vertex cluster modular groups

The octagon's integer relation criterion shows that specialization preserves the signed
and unsigned point-map groups over any coefficient field. The isomorphisms evaluate
the same word over the target field, so the complex Picard calculation determines the
group of point maps in positive characteristic as well.
-/

public noncomputable section

open CategoryTheory QPainleve.Cluster

namespace QPainleve.FourVertex

local notation "B" => exchangeMatrix

variable (k : Type*) [Field k]

private theorem signedSpecialization_injective :
    Function.Injective (signedClusterModularGroupSpecialization ℂ k B) := by
  intro x y h
  obtain ⟨w, rfl⟩ := signedClusterModularGroupMap_surjective ℂ B x
  obtain ⟨v, rfl⟩ := signedClusterModularGroupMap_surjective ℂ B y
  simp only [signedClusterModularGroupSpecialization_apply, signedClusterModularGroupMap_eq_iff]
    at h ⊢
  exact (xPullback_eq_iff_signedLoopInvariants_eq ℂ w.asHom v.asHom).mpr
    ((xPullback_eq_iff_signedLoopInvariants_eq k w.asHom v.asHom).mp h)

/-- Specialization of the signed four-vertex point maps from `ℂ` to an arbitrary field. -/
def signedSpecializationEquiv :
    SignedClusterModularGroup ℂ B ≃* SignedClusterModularGroup k B :=
  MulEquiv.ofBijective (signedClusterModularGroupSpecialization ℂ k B)
    ⟨signedSpecialization_injective k, signedClusterModularGroupSpecialization_surjective ℂ k B⟩

/-- On a signed point map, the equivalence applies the coefficient specialization homomorphism. -/
@[simp]
theorem signedSpecializationEquiv_apply (g : SignedClusterModularGroup ℂ B) :
    signedSpecializationEquiv k g = signedClusterModularGroupSpecialization ℂ k B g :=
  (rfl)

/-- Specialization of the unsigned four-vertex point maps from `ℂ` to an arbitrary field. -/
def unsignedSpecializationEquiv :
    ClusterModularGroup ℂ B ≃* ClusterModularGroup k B :=
  MulEquiv.ofBijective (clusterModularGroupSpecialization ℂ k B)
    ⟨clusterModularGroupSpecialization_injective_of_signed ℂ k B
      (signedSpecialization_injective k), clusterModularGroupSpecialization_surjective ℂ k B⟩

/-- On an unsigned point map, the equivalence applies the coefficient specialization
homomorphism. -/
@[simp]
theorem unsignedSpecializationEquiv_apply (g : ClusterModularGroup ℂ B) :
    unsignedSpecializationEquiv k g = clusterModularGroupSpecialization ℂ k B g :=
  (rfl)

end QPainleve.FourVertex
