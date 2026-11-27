/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Specialization
public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Words

import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Relations

/-!
# Field specialization of the four-vertex cluster modular groups

The octagon's integer relation criterion shows that specialization preserves the signed
and unsigned point-map groups over any coefficient field. The isomorphisms evaluate
the same word over the target field, so the Picard calculation over an algebraically closed field
  of characteristic zero determines the
group of point maps in positive characteristic as well.
-/

public noncomputable section

open CategoryTheory QPainleve.Cluster

namespace QPainleve.FourVertex

local notation "B" => exchangeMatrix

variable (K k : Type*) [Field K] [CharZero K] [Field k]

private theorem signedSpecialization_injective :
    Function.Injective (signedClusterModularGroupSpecialization K k B) := by
  intro x y h
  obtain ⟨w, rfl⟩ := signedClusterModularGroupMap_surjective K B x
  obtain ⟨v, rfl⟩ := signedClusterModularGroupMap_surjective K B y
  simp only [signedClusterModularGroupSpecialization_apply, signedClusterModularGroupMap_eq_iff]
    at h ⊢
  exact (xPullback_eq_iff_signedLoopInvariants_eq K w.asHom v.asHom).mpr
    ((xPullback_eq_iff_signedLoopInvariants_eq k w.asHom v.asHom).mp h)

/-- Specialization of the signed four-vertex point maps from a characteristic-zero field
to an arbitrary field. -/
def signedSpecializationEquiv :
    SignedClusterModularGroup K B ≃* SignedClusterModularGroup k B :=
  MulEquiv.ofBijective (signedClusterModularGroupSpecialization K k B)
    ⟨signedSpecialization_injective K k, signedClusterModularGroupSpecialization_surjective K k B⟩

/-- On a signed point map, the equivalence applies the coefficient specialization homomorphism. -/
@[simp]
theorem signedSpecializationEquiv_apply (g : SignedClusterModularGroup K B) :
    signedSpecializationEquiv K k g = signedClusterModularGroupSpecialization K k B g :=
  (rfl)

/-- Specialization of the unsigned four-vertex point maps from a characteristic-zero field
to an arbitrary field. -/
def unsignedSpecializationEquiv :
    ClusterModularGroup K B ≃* ClusterModularGroup k B :=
  MulEquiv.ofBijective (clusterModularGroupSpecialization K k B)
    ⟨clusterModularGroupSpecialization_injective_of_signed K k B
      (signedSpecialization_injective K k), clusterModularGroupSpecialization_surjective K k B⟩

/-- On an unsigned point map, the equivalence applies the coefficient specialization
homomorphism. -/
@[simp]
theorem unsignedSpecializationEquiv_apply (g : ClusterModularGroup K B) :
    unsignedSpecializationEquiv K k g = clusterModularGroupSpecialization K k B g :=
  (rfl)

end QPainleve.FourVertex
