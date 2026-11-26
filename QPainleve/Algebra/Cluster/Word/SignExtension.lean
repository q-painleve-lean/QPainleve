/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import QPainleve.Algebra.Cluster.Word.Parity
public import TauCeti.GroupTheory.GroupExtension.Of.Surjective

import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.ZMod.QuotientGroup
import TauCeti.Algebra.Group.Prod
import TauCeti.GroupTheory.GroupExtension.Splitting

/-!
# The sign extension of cluster modular groups

The unsigned group is included in the signed group by retaining the same X map.
At a nonzero exchange matrix, the range of this inclusion is the kernel of the
descended inversion sign. An odd loop makes the sign surjective and gives the
unsigned inclusion index two. A negative-sign point map of order two splits the
extension and, when central, generates a direct product complement.
-/

public noncomputable section

open CategoryTheory MulOpposite Quiver

namespace QPainleve.Cluster

variable (k : Type*) [Field k] {ι : Type*} [DecidableEq ι] (B : SkewExchangeMatrix ι)
variable [Finite ι]

/-- A signed point map of sign `-1` makes the sign homomorphism surjective. -/
theorem signedInversionSign_surjective (hB : B.matrix ≠ 0) {z : SignedClusterModularGroup k B}
    (hz : signedInversionSign k B hB z = -1) :
    Function.Surjective (signedInversionSign k B hB) := by
  intro ε
  rcases Int.units_eq_one_or ε with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨z, hz⟩

private def unsignedEquivSignKer (hB : B.matrix ≠ 0) :
    ClusterModularGroup k B ≃* (signedInversionSign k B hB).ker :=
  ((Subgroup.subgroupOfEquivOfLe (unsignedLoopPullbacks_le_signedLoopPullbacks k B)).symm.op.trans
    (Subgroup.mopMulEquivOp _)).trans (MulEquiv.subgroupCongr (ker_signedInversionSign k B hB).symm)

/-- The inclusion of unsigned point maps has range equal to the kernel of the inversion sign. -/
theorem range_clusterModularGroupInclusion (hB : B.matrix ≠ 0) :
    (clusterModularGroupInclusion k B).range = (signedInversionSign k B hB).ker := by
  change ((signedInversionSign k B hB).ker.subtype.comp
    (unsignedEquivSignKer k B hB).toMonoidHom).range = _
  rw [MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective _ (unsignedEquivSignKer k B hB).surjective,
    Subgroup.map_top, Subgroup.range_subtype]

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

/-- If the inversion sign is surjective, the unsigned cluster modular group has index two. -/
theorem index_range_clusterModularGroupInclusion (hB : B.matrix ≠ 0)
    (hs : Function.Surjective (signedInversionSign k B hB)) :
    (clusterModularGroupInclusion k B).range.index = 2 := by
  let S := signedInversionSignExtension k B hB hs
  rw [← signedInversionSignExtension_inl k B hB hs, Subgroup.index_eq_card]
  exact (Nat.card_congr S.quotientRangeInlEquivRight.toEquiv).trans
    (Nat.card_eq_fintype_card.trans Fintype.card_units_int)

section SignInvolution

variable {hB : B.matrix ≠ 0} {z : SignedClusterModularGroup k B}
  (hz : signedInversionSign k B hB z = -1) (ho : orderOf z = 2)

private def involutionZPowersEquivSign : Subgroup.zpowers z ≃* ℤˣ := by
  let f := (signedInversionSign k B hB).comp (Subgroup.zpowers z).subtype
  have hcard : Nat.card (Subgroup.zpowers z) = 2 := (Nat.card_zpowers z).trans ho
  letI := Nat.finite_of_card_ne_zero (hcard.trans_ne (by decide : (2 : ℕ) ≠ 0))
  refine MulEquiv.ofBijective f ((Nat.bijective_iff_surjective_and_card f).mpr ⟨?_, ?_⟩)
  · intro ε
    rcases Int.units_eq_one_or ε with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨⟨z, Subgroup.mem_zpowers z⟩, hz⟩
  · rw [hcard, Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- A negative-sign point map of order two splits the inversion-sign extension. -/
def signSplittingOfInvolution :
    (signedInversionSignExtension k B hB (signedInversionSign_surjective k B hB hz)).Splitting where
  __ := (Subgroup.zpowers z).subtype.comp (involutionZPowersEquivSign k B hz ho).symm.toMonoidHom
  rightInverse_rightHom ε := by
    rw [signedInversionSignExtension_rightHom]
    exact (involutionZPowersEquivSign k B hz ho).apply_symm_apply ε

/-- The section sends the negative sign to the specified involution. -/
@[simp]
theorem signSplittingOfInvolution_neg_one : signSplittingOfInvolution k B hz ho (-1) = z := by
  let e := involutionZPowersEquivSign k B hz ho
  have h : e ⟨z, Subgroup.mem_zpowers z⟩ = -1 := hz
  exact congrArg Subtype.val (e.symm_apply_eq.mpr h.symm)

variable (hc : z ∈ Subgroup.center (SignedClusterModularGroup k B))

local notation "t" => signSplittingOfInvolution k B hz ho

include hc in
private theorem signSplittingOfInvolution_conjAct_eq_one : (t).conjAct = 1 := by
  ext ε f
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp
  · apply clusterModularGroupInclusion_injective k B
    have h := (t).inl_conjAct (-1) f
    rw [signedInversionSignExtension_inl, signSplittingOfInvolution_neg_one] at h
    have hcomm := Subgroup.mem_center_iff.mp hc (clusterModularGroupInclusion k B f)
    simpa only [← hcomm, mul_inv_cancel_right, MonoidHom.one_apply, MulAut.one_apply] using h

include hc in
/-- Multiplication identifies the signed group with the product of the unsigned group and
the cyclic subgroup of a central negative-sign involution.
The complement calculation follows [the signed Picard splitting proof]
(https://github.com/q-painleve-lean/QPainleve/pull/753). -/
def mulEquivProdZPowersOfCentralInvolution :
    ClusterModularGroup k B × Subgroup.zpowers z ≃* SignedClusterModularGroup k B :=
  (MulEquiv.prodCongr (MulEquiv.refl _) (involutionZPowersEquivSign k B hz ho)).trans
    (SemidirectProduct.mulEquivProd.symm.trans
      ((SemidirectProduct.congr (MulEquiv.refl _) (MulEquiv.refl _) (by
        rw [signSplittingOfInvolution_conjAct_eq_one k B hz ho hc]
        intro ε
        rfl)).trans (t).semidirectProductMulEquiv))

@[simp]
theorem mulEquivProdZPowersOfCentralInvolution_apply
    (x : ClusterModularGroup k B × Subgroup.zpowers z) :
    mulEquivProdZPowersOfCentralInvolution k B hz ho hc x =
      clusterModularGroupInclusion k B x.1 * x.2.val := by
  obtain ⟨f, y⟩ := x
  let e := involutionZPowersEquivSign k B hz ho
  obtain ⟨ε, rfl⟩ := e.symm.surjective y
  have hsection : t ε = (e.symm ε).val := rfl
  simp [mulEquivProdZPowersOfCentralInvolution, e, ← hsection,
    GroupExtension.Splitting.semidirectProductMulEquiv_apply]

end SignInvolution

end QPainleve.Cluster
