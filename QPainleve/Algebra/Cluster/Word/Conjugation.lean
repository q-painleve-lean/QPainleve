/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Parity

import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Change of base seed for cluster modular groups

A word between two exchange matrices conjugates the X maps of loops at the two
seeds, both for signed loops and for the unsigned subgroup. If the original loop
is inversion-free, the transported word has even inversion count even if the
connecting word reverses the sign.
-/

public noncomputable section

namespace QPainleve.Cluster

open CategoryTheory MulOpposite Quiver

variable (k : Type*) [Field k] {ι : Type*} [DecidableEq ι]
  {B C : SkewExchangeMatrix ι}

local notation "Aut" => (FractionRing (AddMonoidAlgebra k (ι →₀ ℤ)) ≃ₐ[k]
  FractionRing (AddMonoidAlgebra k (ι →₀ ℤ)))

private theorem conj_mem_signedLoopPullbacks (w : Word B C)
    {f : Aut} (hf : f ∈ signedLoopPullbacks k B) :
    MulAut.conj (w.xPullback k)⁻¹ f ∈ signedLoopPullbacks k C := by
  obtain ⟨v, rfl⟩ := (mem_signedLoopPullbacks_iff k B f).mp hf
  exact (mem_signedLoopPullbacks_iff k C _).mpr
    ⟨(w.reverse.comp v).comp w, by simp [mul_assoc]⟩

private theorem map_signedLoopPullbacks_conj (w : Word B C) :
    (signedLoopPullbacks k B).map (MulAut.conj (w.xPullback k)⁻¹).toMonoidHom =
      signedLoopPullbacks k C := by
  ext f
  rw [Subgroup.mem_map_equiv]
  exact ⟨fun h ↦ by simpa [mul_assoc] using conj_mem_signedLoopPullbacks k w h,
    fun h ↦ by simpa using conj_mem_signedLoopPullbacks k w.reverse h⟩

/-- Conjugation of signed point maps by a connecting word. A transported loop
travels along the reverse word, executes the original loop, then returns along the word. -/
def signedClusterModularGroupCongr (w : Word B C) :
    SignedClusterModularGroup k B ≃* SignedClusterModularGroup k C :=
  MulEquiv.op (TauCeti.Subgroup.congrOfMapEq (MulAut.conj (w.xPullback k)⁻¹)
    (map_signedLoopPullbacks_conj k w))

@[simp]
theorem signedClusterModularGroupCongr_unop_coe (w : Word B C) (f : SignedClusterModularGroup k B) :
    ((signedClusterModularGroupCongr k w f).unop : Aut) =
      (w.xPullback k)⁻¹ * (f.unop : Aut) * w.xPullback k := by
  simp [signedClusterModularGroupCongr]

/-- The empty word induces the identity change of base. -/
@[simp]
theorem signedClusterModularGroupCongr_nil :
    signedClusterModularGroupCongr k (Path.nil : Word B B) = MulEquiv.refl _ := by
  apply MulEquiv.ext
  intro f
  apply unop_injective
  apply Subtype.ext
  simp

/-- Successive changes of base agree with transport along the concatenated word. -/
theorem signedClusterModularGroupCongr_comp {D : SkewExchangeMatrix ι}
    (w : Word B C) (v : Word C D) :
    signedClusterModularGroupCongr k (w.comp v) =
      (signedClusterModularGroupCongr k w).trans (signedClusterModularGroupCongr k v) := by
  apply MulEquiv.ext
  intro f
  apply unop_injective
  apply Subtype.ext
  simp [mul_assoc]

@[simp]
theorem signedClusterModularGroupCongr_map (w : Word B C)
    (v : End (Prefunctor.obj (Paths.of (SkewExchangeMatrix ι)) B)) :
    signedClusterModularGroupCongr k w (signedClusterModularGroupMap k B v) =
      signedClusterModularGroupMap k C (End.of ((w.reverse.comp v.asHom).comp w)) := by
  apply unop_injective
  apply Subtype.ext
  rw [signedClusterModularGroupCongr_unop_coe, signedClusterModularGroupMap_unop_coe,
    signedClusterModularGroupMap_unop_coe]
  -- Unwrap the categorical endomorphism to apply the path composition formula.
  change _ = ((w.reverse.comp v.asHom).comp w).xPullback k
  rw [Path.xPullback_comp k (w.reverse.comp v.asHom) w,
    Path.xPullback_comp k w.reverse v.asHom, Path.xPullback_reverse]
  exact (mul_assoc (w.xPullback k)⁻¹ (v.asHom.xPullback k) (w.xPullback k)).symm

/-- At nonzero exchange matrices, transport by a connecting word preserves the descended sign. -/
@[simp]
theorem signedInversionSign_signedClusterModularGroupCongr [CharZero k] [Finite ι]
    (w : Word B C) (hB : B.matrix ≠ 0) (hC : C.matrix ≠ 0) (f : SignedClusterModularGroup k B) :
    signedInversionSign k C hC (signedClusterModularGroupCongr k w f) =
      signedInversionSign k B hB f := by
  obtain ⟨v, rfl⟩ := signedClusterModularGroupMap_surjective k B f
  rw [signedClusterModularGroupCongr_map, signedInversionSign_apply, signedInversionSign_apply]
  exact w.neg_one_pow_inversionCount_reverse_comp_comp v.asHom

private theorem conj_mem_unsignedLoopPullbacks (w : Word B C)
    {f : Aut} (hf : f ∈ unsignedLoopPullbacks k B) :
    MulAut.conj (w.xPullback k)⁻¹ f ∈ unsignedLoopPullbacks k C := by
  obtain ⟨v, hv, rfl⟩ := (mem_unsignedLoopPullbacks_iff k B f).mp hf
  refine (mem_unsignedLoopPullbacks_iff_exists_even k C _).mpr
    ⟨(w.reverse.comp v).comp w, ?_, by simp [mul_assoc]⟩
  simp only [Path.inversionCount_comp, Path.inversionCount_reverse, hv, add_zero]
  exact ⟨_, rfl⟩

private theorem map_unsignedLoopPullbacks_conj (w : Word B C) :
    (unsignedLoopPullbacks k B).map (MulAut.conj (w.xPullback k)⁻¹).toMonoidHom =
      unsignedLoopPullbacks k C := by
  ext f
  rw [Subgroup.mem_map_equiv]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [mul_assoc] using conj_mem_unsignedLoopPullbacks k w h
  · simpa using conj_mem_unsignedLoopPullbacks k w.reverse h

/-- A connecting word transports unsigned point maps by conjugation. At the target
seed a transported loop first travels back along the word, then executes the
original loop and returns along the word. -/
def clusterModularGroupCongr (w : Word B C) : ClusterModularGroup k B ≃* ClusterModularGroup k C :=
  MulEquiv.op (TauCeti.Subgroup.congrOfMapEq (MulAut.conj (w.xPullback k)⁻¹)
    (map_unsignedLoopPullbacks_conj k w))

@[simp]
theorem clusterModularGroupCongr_unop_coe (w : Word B C) (f : ClusterModularGroup k B) :
    ((clusterModularGroupCongr k w f).unop : Aut) =
      (w.xPullback k)⁻¹ * (f.unop : Aut) * w.xPullback k := by
  simp [clusterModularGroupCongr]

/-- The change of base seed commutes with inclusion of the unsigned point maps. -/
@[simp]
theorem signedClusterModularGroupCongr_inclusion (w : Word B C) (f : ClusterModularGroup k B) :
    signedClusterModularGroupCongr k w (clusterModularGroupInclusion k B f) =
      clusterModularGroupInclusion k C (clusterModularGroupCongr k w f) := by
  apply unop_injective
  apply Subtype.ext
  simp [clusterModularGroupInclusion, MonoidHom.op_apply_apply]

/-- An inversion-free representative of the transported group element induces the
same X pullback as the reverse word, the original loop, and the connecting word. -/
theorem clusterModularGroupMap_eq_congr_iff (w : Word B C)
    (v : Word B B) (hv : v.inversionCount = 0) (u : Word C C) (hu : u.inversionCount = 0) :
    clusterModularGroupMap k C ⟨End.of u, (mem_inversionFreeLoops_iff C _).mpr hu⟩ =
      clusterModularGroupCongr k w
        (clusterModularGroupMap k B ⟨End.of v, (mem_inversionFreeLoops_iff B _).mpr hv⟩) ↔
      u.xPullback k = ((w.reverse.comp v).comp w).xPullback k := by
  rw [← unop_injective.eq_iff, ← Subtype.coe_injective.eq_iff]
  simp only [clusterModularGroupMap_unop_coe, clusterModularGroupCongr_unop_coe,
    Path.xPullback_comp, Path.xPullback_reverse]
  exact Iff.rfl

end QPainleve.Cluster
