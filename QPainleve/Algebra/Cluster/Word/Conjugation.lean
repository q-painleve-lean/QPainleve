/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.ModularGroup

import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Change of base seed for cluster modular groups

A word between two exchange matrices conjugates the X maps of loops at the two
seeds. The transported word has even inversion count when the original loop
is inversion-free, even if the connecting word reverses the sign.
-/

public noncomputable section

namespace QPainleve.Cluster

open CategoryTheory MulOpposite Quiver

variable (k : Type*) [Field k] {ι : Type*} [DecidableEq ι]
  {B C : SkewExchangeMatrix ι}

local notation "Aut" => (FractionRing (AddMonoidAlgebra k (ι →₀ ℤ)) ≃ₐ[k]
  FractionRing (AddMonoidAlgebra k (ι →₀ ℤ)))

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
