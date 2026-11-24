/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Parity
public import TauCeti.GroupTheory.GroupExtension.Of.Surjective

import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.Int.Order.Units
import Mathlib.GroupTheory.Index

/-!
# The sign extension of cluster modular groups

The unsigned group is included in the signed group by retaining the same X map.
At a nonzero exchange matrix, an odd loop makes the descended inversion sign
surjective. Its kernel is canonically the unsigned cluster modular group, so the
inclusion has index two.
-/

public noncomputable section

open CategoryTheory MulOpposite Quiver

namespace QPainleve.Cluster

variable (k : Type*) [Field k] {ι : Type*} [DecidableEq ι] (B : SkewExchangeMatrix ι)

/-- Include the inversion-free X maps in the signed point-map group. -/
def clusterModularGroupInclusion : ClusterModularGroup k B →* SignedClusterModularGroup k B :=
  (Subgroup.inclusion (unsignedLoopPullbacks_le_signedLoopPullbacks k B)).op

@[simp]
theorem clusterModularGroupInclusion_clusterModularGroupMap (w : inversionFreeLoops B) :
    clusterModularGroupInclusion k B (clusterModularGroupMap k B w) =
      signedClusterModularGroupMap k B w.val := by
  apply unop_injective
  apply Subtype.coe_injective
  simp only [clusterModularGroupInclusion, MonoidHom.op_apply_apply, Function.comp_apply,
    unop_op, Subgroup.coe_inclusion, clusterModularGroupMap_unop_coe,
    signedClusterModularGroupMap_unop_coe]

theorem clusterModularGroupInclusion_injective :
    Function.Injective (clusterModularGroupInclusion k B) :=
  op_injective.comp
    ((Subgroup.inclusion_injective (unsignedLoopPullbacks_le_signedLoopPullbacks k B)).comp
      unop_injective)

variable [CharZero k] [Finite ι]

/-- The sign homomorphism is onto as soon as an odd loop exists. -/
theorem signedInversionSign_surjective (hB : B.matrix ≠ 0) {w : Word B B}
    (hw : Odd w.inversionCount) : Function.Surjective (signedInversionSign k B hB) := by
  intro ε
  rcases Int.units_eq_one_or ε with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨signedClusterModularGroupMap k B (End.of w),
      (signedInversionSign_apply k B hB (End.of w)).trans hw.neg_one_pow⟩

private def unsignedEquivSignKer (hB : B.matrix ≠ 0) :
    ClusterModularGroup k B ≃* (signedInversionSign k B hB).ker :=
  ((Subgroup.subgroupOfEquivOfLe (unsignedLoopPullbacks_le_signedLoopPullbacks k B)).symm.op.trans
    (Subgroup.mopMulEquivOp _)).trans (MulEquiv.subgroupCongr (ker_signedInversionSign k B hB).symm)

/-- The exact sequence of unsigned maps, signed maps, and inversion signs. -/
def signedInversionSignExtension (hB : B.matrix ≠ 0)
    (hs : Function.Surjective (signedInversionSign k B hB)) :
    GroupExtension (ClusterModularGroup k B) (SignedClusterModularGroup k B) ℤˣ :=
  GroupExtension.ofMulEquivKer hs (unsignedEquivSignKer k B hB)

@[simp]
theorem signedInversionSignExtension_inl (hB : B.matrix ≠ 0)
    (hs : Function.Surjective (signedInversionSign k B hB)) :
    (signedInversionSignExtension k B hB hs).inl = clusterModularGroupInclusion k B := by
  rw [signedInversionSignExtension, GroupExtension.ofMulEquivKer_inl]
  rfl

@[simp]
theorem signedInversionSignExtension_rightHom (hB : B.matrix ≠ 0)
    (hs : Function.Surjective (signedInversionSign k B hB)) :
    (signedInversionSignExtension k B hB hs).rightHom = signedInversionSign k B hB :=
  GroupExtension.ofMulEquivKer_rightHom hs _

/-- If there is an odd loop, the unsigned cluster modular group has index two. -/
theorem index_range_clusterModularGroupInclusion (hB : B.matrix ≠ 0) {w : Word B B}
    (hw : Odd w.inversionCount) : (clusterModularGroupInclusion k B).range.index = 2 := by
  have hs := signedInversionSign_surjective k B hB hw
  have hker := (signedInversionSignExtension k B hB hs).range_inl_eq_ker_rightHom
  rw [signedInversionSignExtension_inl, signedInversionSignExtension_rightHom] at hker
  rw [hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hs,
    Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup ℤˣ) ≃* ℤˣ).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_units_int]

end QPainleve.Cluster
