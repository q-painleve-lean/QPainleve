/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Parity
import QPainleve.Algebra.Cluster.Word.CoefficientChange

/-!
# Specializing coefficients of cluster modular groups

An equality of X pullbacks in characteristic zero survives over every field by
`Quiver.Path.xPullback_eq_of_charZero`. The loop quotients therefore give surjective
specialization homomorphisms on both point-map groups. These homomorphisms retain the
word representing each element, so they commute with the unsigned inclusion and with
the inversion sign wherever it is defined.
-/

public noncomputable section

open CategoryTheory Quiver

namespace QPainleve.Cluster

variable (K k : Type*) [Field K] [CharZero K] [Field k]
  {ι : Type*} [DecidableEq ι] (B : SkewExchangeMatrix ι)

local notation "Loops" => End (Prefunctor.obj (Paths.of (SkewExchangeMatrix ι)) B)
local notation "signed[" k "]" => signedClusterModularGroupMap k B
local notation "unsigned[" k "]" => clusterModularGroupMap k B

/-- Specialization of signed cluster point maps sends the map represented by a loop over
a characteristic-zero field to the map represented by the same loop over the target field. -/
def signedClusterModularGroupSpecialization :
    SignedClusterModularGroup K B →* SignedClusterModularGroup k B :=
  ((Con.ker signed[K]).lift signed[k] fun w v h ↦ by
    rw [Con.ker_rel, signedClusterModularGroupMap_eq_iff] at h ⊢
    exact Path.xPullback_eq_of_charZero k K h).comp
    (signedLoopQuotientMulEquiv K B).symm.toMonoidHom

/-- Specialization evaluates the same signed loop over the target field. -/
@[simp]
theorem signedClusterModularGroupSpecialization_apply (w : Loops) :
    signedClusterModularGroupSpecialization K k B (signed[K] w) = signed[k] w := by
  rw [← signedLoopQuotientMulEquiv_mk K B w]
  simp only [signedClusterModularGroupSpecialization, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, Con.lift_coe]

/-- Every signed point map over the target field comes from specialization. -/
theorem signedClusterModularGroupSpecialization_surjective :
    Function.Surjective (signedClusterModularGroupSpecialization K k B) := by
  intro g
  obtain ⟨w, rfl⟩ := signedClusterModularGroupMap_surjective k B g
  exact ⟨signed[K] w, signedClusterModularGroupSpecialization_apply K k B w⟩

/-- Specialization of unsigned cluster point maps evaluates inversion-free loops over the
target field. -/
def clusterModularGroupSpecialization :
    ClusterModularGroup K B →* ClusterModularGroup k B :=
  ((Con.ker unsigned[K]).lift unsigned[k] fun w v h ↦ by
    rw [Con.ker_rel, clusterModularGroupMap_eq_iff] at h ⊢
    exact Path.xPullback_eq_of_charZero k K h).comp
    (unsignedLoopQuotientMulEquiv K B).symm.toMonoidHom

/-- Specialization evaluates the same inversion-free loop over the target field. -/
@[simp]
theorem clusterModularGroupSpecialization_apply (w : inversionFreeLoops B) :
    clusterModularGroupSpecialization K k B (unsigned[K] w) = unsigned[k] w := by
  rw [← unsignedLoopQuotientMulEquiv_mk K B w]
  simp only [clusterModularGroupSpecialization, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, Con.lift_coe]

/-- Every unsigned point map over the target field comes from specialization. -/
theorem clusterModularGroupSpecialization_surjective :
    Function.Surjective (clusterModularGroupSpecialization K k B) := by
  intro g
  obtain ⟨w, rfl⟩ := clusterModularGroupMap_surjective k B g
  exact ⟨unsigned[K] w, clusterModularGroupSpecialization_apply K k B w⟩

/-- Specialization commutes with the inclusion of unsigned point maps. -/
@[simp]
theorem signedClusterModularGroupSpecialization_inclusion (g : ClusterModularGroup K B) :
    signedClusterModularGroupSpecialization K k B (clusterModularGroupInclusion K B g) =
      clusterModularGroupInclusion k B (clusterModularGroupSpecialization K k B g) := by
  obtain ⟨w, rfl⟩ := clusterModularGroupMap_surjective K B g
  simp

/-- If specialization is faithful on signed point maps, it is faithful on the unsigned
subgroup as well. -/
theorem clusterModularGroupSpecialization_injective_of_signed
    (h : Function.Injective (signedClusterModularGroupSpecialization K k B)) :
    Function.Injective (clusterModularGroupSpecialization K k B) := by
  intro g g' hgg'
  apply clusterModularGroupInclusion_injective K B
  apply h
  rw [signedClusterModularGroupSpecialization_inclusion,
    signedClusterModularGroupSpecialization_inclusion, hgg']

/-- Specialization preserves the inversion sign at a nonzero exchange matrix. -/
@[simp]
theorem signedInversionSign_specialization [Finite ι] (hB : B.matrix ≠ 0)
    (g : SignedClusterModularGroup K B) :
    signedInversionSign k B hB (signedClusterModularGroupSpecialization K k B g) =
      signedInversionSign K B hB g := by
  obtain ⟨w, rfl⟩ := signedClusterModularGroupMap_surjective K B g
  simp

end QPainleve.Cluster
