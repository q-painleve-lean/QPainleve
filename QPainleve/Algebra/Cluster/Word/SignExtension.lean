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
unsigned inclusion index two. An odd involution splits the extension and, when
central, generates a direct product complement.
-/

public noncomputable section

open CategoryTheory MulOpposite Quiver

namespace QPainleve.Cluster

variable (k : Type*) [Field k] {ι : Type*} [DecidableEq ι] (B : SkewExchangeMatrix ι)
variable [Finite ι]

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

private def oddInvolutionZPowersEquivSign {hB : B.matrix ≠ 0} (w : Word B B)
    (hw : Odd w.inversionCount) (ho : orderOf (signedClusterModularGroupMap k B (End.of w)) = 2) :
    Subgroup.zpowers (signedClusterModularGroupMap k B (End.of w)) ≃* ℤˣ := by
  let z := signedClusterModularGroupMap k B (End.of w)
  let f := (signedInversionSign k B hB).comp (Subgroup.zpowers z).subtype
  have hcard : Nat.card (Subgroup.zpowers z) = 2 := (Nat.card_zpowers z).trans ho
  letI := Nat.finite_of_card_ne_zero (hcard.trans_ne (by decide : (2 : ℕ) ≠ 0))
  refine MulEquiv.ofBijective f ((Nat.bijective_iff_surjective_and_card f).mpr ⟨?_, ?_⟩)
  · intro ε
    rcases Int.units_eq_one_or ε with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨⟨z, Subgroup.mem_zpowers z⟩,
        (signedInversionSign_apply k B hB (End.of w)).trans hw.neg_one_pow⟩
  · rw [hcard, Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- An odd loop whose signed point map has order two splits the inversion-sign extension. -/
def signSplittingOfOddInvolution {hB : B.matrix ≠ 0} (w : Word B B)
    (hw : Odd w.inversionCount) (ho : orderOf (signedClusterModularGroupMap k B (End.of w)) = 2) :
    (signedInversionSignExtension k B hB (signedInversionSign_surjective k B hB hw)).Splitting where
  __ := (Subgroup.zpowers _).subtype.comp
    (oddInvolutionZPowersEquivSign k B (hB := hB) w hw ho).symm.toMonoidHom
  rightInverse_rightHom ε := by
    rw [signedInversionSignExtension_rightHom]
    exact (oddInvolutionZPowersEquivSign k B (hB := hB) w hw ho).apply_symm_apply ε

/-- The section defined by an odd involution sends minus one to the loop's point map. -/
theorem signSplittingOfOddInvolution_neg_one {hB : B.matrix ≠ 0}
    (w : Word B B) (hw : Odd w.inversionCount)
    (ho : orderOf (signedClusterModularGroupMap k B (End.of w)) = 2) :
    signSplittingOfOddInvolution k B (hB := hB) w hw ho (-1) =
      signedClusterModularGroupMap k B (End.of w) := by
  let z := signedClusterModularGroupMap k B (End.of w)
  let e := oddInvolutionZPowersEquivSign k B (hB := hB) w hw ho
  have h : e ⟨z, Subgroup.mem_zpowers z⟩ = -1 :=
    (signedInversionSign_apply k B hB (End.of w)).trans hw.neg_one_pow
  exact congrArg Subtype.val (e.symm_apply_eq.mpr h.symm)

/-- A central odd involution gives the direct product of the unsigned group and the
cyclic group generated by the involution, with the equivalence given by multiplication.
The complement calculation follows [the signed Picard splitting proof]
(https://github.com/q-painleve-lean/QPainleve/pull/753). -/
theorem exists_mulEquiv_prod_zpowers_of_central_odd_loop {hB : B.matrix ≠ 0}
    (w : Word B B) (hw : Odd w.inversionCount)
    (ho : orderOf (signedClusterModularGroupMap k B (End.of w)) = 2)
    (hc : signedClusterModularGroupMap k B (End.of w) ∈
      Subgroup.center (SignedClusterModularGroup k B)) :
    let z := signedClusterModularGroupMap k B (End.of w)
    ∃ e : ClusterModularGroup k B × Subgroup.zpowers z ≃* SignedClusterModularGroup k B,
      ∀ (f : ClusterModularGroup k B) (u : Subgroup.zpowers z),
        e (f, u) = clusterModularGroupInclusion k B f * u.val := by
  let z := signedClusterModularGroupMap k B (End.of w)
  let t := signSplittingOfOddInvolution k B (hB := hB) w hw ho
  have hneg : t (-1) = z := signSplittingOfOddInvolution_neg_one k B w hw ho
  have hact : t.conjAct = 1 := by
    ext ε f
    rcases Int.units_eq_one_or ε with rfl | rfl
    · simp
    · apply clusterModularGroupInclusion_injective k B
      have h := t.inl_conjAct (-1) f
      rw [signedInversionSignExtension_inl, hneg] at h
      have hcomm : clusterModularGroupInclusion k B f * z =
          z * clusterModularGroupInclusion k B f :=
        Subgroup.mem_center_iff.mp hc (clusterModularGroupInclusion k B f)
      simpa only [← hcomm, mul_inv_cancel_right, MonoidHom.one_apply, MulAut.one_apply] using h
  let u := (oddInvolutionZPowersEquivSign k B (hB := hB) w hw ho).symm
  let e₀ : ClusterModularGroup k B ⋊[(1 : ℤˣ →* MulAut (ClusterModularGroup k B))] ℤˣ ≃*
      ClusterModularGroup k B ⋊[t.conjAct] ℤˣ :=
    SemidirectProduct.congr (MulEquiv.refl _) (MulEquiv.refl _) (by rw [hact]; intro ε; rfl)
  refine ⟨(MulEquiv.prodCongr (MulEquiv.refl _) u.symm).trans
    (SemidirectProduct.mulEquivProd.symm.trans (e₀.trans t.semidirectProductMulEquiv)), ?_⟩
  intro f y
  obtain ⟨ε, rfl⟩ := u.surjective y
  have hu : t ε = (u ε).val := rfl
  simp [e₀, GroupExtension.Splitting.semidirectProductMulEquiv_apply, hu]

end QPainleve.Cluster
