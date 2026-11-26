/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.SignExtension
public import QPainleve.SignedClusterModularGroup.Boundary.Isometry

import TauCeti.GroupTheory.GroupExtension.Splitting

/-!
# Transport of the Picard sign splitting to point maps

The signed and unsigned Picard identifications are contravariant. Inversion makes them
covariant as equivalences of the two sign extensions. Since signs are self-inverse, the
quotient map is unchanged by this conversion. Tau Ceti's
`GroupExtension.splittingEquivOfMulEquiv` transports a Picard section, and the resulting
conjugation actions identify the two semidirect products.

The signed Picard equivalence also lifts odd involutions to cluster words. For at most
two boundary components, the pure sign change gives a central cyclic complement.
-/

public section

open CategoryTheory MulOpposite Quiver
open QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup

namespace QPainleve.SignedClusterModularGroup

variable {k : Type*} [Field k] {ι : Type*} [DecidableEq ι] [Finite ι]
  {E : SkewExchangeMatrix ι} {L : Type*} [AddCommGroup L] {n : ℕ}
  {B : LinearMap.BilinForm ℤ L} {D : ZMod n → L}

local notation "Γ₀" => ClusterModularGroup k E
local notation "Γₛ" => SignedClusterModularGroup k E
local notation "inclusion" => clusterModularGroupInclusion k E
local notation "eval[" w "]" => op (signedClusterModularGroupMap k E (End.of w))

/-- If a Picard action gives the inversion parity on each loop, its sign on every
signed point map is the descended inversion sign. -/
theorem sign_picardHom_apply_op
    (ρ : Γₛᵐᵒᵖ →* signedBoundaryIsometryGroup B D)
    (hρ : ∀ w : Word E E, sign B D (ρ eval[w]) = (-1 : ℤˣ) ^ w.inversionCount)
    (hE : E.matrix ≠ 0) (x : Γₛ) :
    sign B D (ρ (op x)) = signedInversionSign k E hE x := by
  obtain ⟨w, rfl⟩ := signedClusterModularGroupMap_surjective k E x
  exact (hρ (End.asHom w)).trans (signedInversionSign_apply k E hE w).symm

/-- For a Picard action with the prescribed sign on loops, the sign kernel on
point maps is the image of the unsigned cluster modular group. -/
theorem sign_ker_unop_eq_range_of_apply_word
    (ρ : Γₛᵐᵒᵖ →* signedBoundaryIsometryGroup B D)
    (hρ : ∀ w : Word E E, sign B D (ρ eval[w]) = (-1 : ℤˣ) ^ w.inversionCount)
    (hE : E.matrix ≠ 0) :
    ((sign B D).comp ρ).ker.unop = MonoidHom.range inclusion := by
  rw [range_clusterModularGroupInclusion k E hE]
  ext x
  simp only [Subgroup.mem_unop, MonoidHom.mem_ker, MonoidHom.comp_apply,
    sign_picardHom_apply_op ρ hρ hE]

section Splitting

variable (Θ : (SignedClusterModularGroup k E)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B D)
variable (hΘ : ∀ w : Word E E,
  sign B D (Θ (op (signedClusterModularGroupMap k E (End.of w)))) = (-1 : ℤˣ) ^ w.inversionCount)
variable (hE : E.matrix ≠ 0) {hsign : Function.Surjective (sign B D)}

include hΘ in
/-- A sign-compatible Picard equivalence transfers surjectivity of the boundary sign to the
inversion sign of the signed cluster modular group. -/
theorem signedInversionSign_surjective_of_picardEquiv
    (hsign : Function.Surjective (sign B D)) :
    Function.Surjective (signedInversionSign k E hE) := by
  rw [← funext (sign_picardHom_apply_op Θ.toMonoidHom hΘ hE)]
  exact hsign.comp (Θ.surjective.comp op_surjective)

/-- Transport the boundary sign section to signed point maps through the Picard equivalence
composed with inversion. -/
noncomputable def picardSignSplitting (t : (signExtension B D hsign).Splitting) :
    (signedInversionSignExtension k E hE
      (signedInversionSign_surjective_of_picardEquiv Θ hΘ hE hsign)).Splitting :=
  let e := (MulEquiv.inv' Γₛ).trans Θ
  ((signedInversionSignExtension k E hE
      (signedInversionSign_surjective_of_picardEquiv Θ hΘ hE hsign)).splittingEquivOfMulEquiv
    (signExtension B D hsign) e (MulEquiv.refl ℤˣ) (by
      apply MonoidHom.ext
      intro x
      simpa only [e, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
        MulEquiv.inv'_apply, Function.comp_apply, MulEquiv.refl_apply, signExtension_rightHom,
        signedInversionSignExtension_rightHom, map_inv, Int.units_inv_eq_self]
        using sign_picardHom_apply_op Θ.toMonoidHom hΘ hE x⁻¹)).symm t

variable (t : (signExtension B D hsign).Splitting)

private theorem picardSignSplitting_apply_inv (ε : ℤˣ) :
    Θ (op (picardSignSplitting Θ hΘ hE t ε)⁻¹) = t ε := by
  have he : ((MulEquiv.inv' Γₛ).trans Θ) (picardSignSplitting Θ hΘ hE t ε) = t ε := by
    simp [picardSignSplitting]
  simpa only [MulEquiv.trans_apply, MulEquiv.inv'_apply, Function.comp_apply] using he

/-- The transported section takes a sign to the point map with the prescribed Picard pullback. -/
@[simp]
theorem picardSignSplitting_apply (ε : ℤˣ) :
    picardSignSplitting Θ hΘ hE t ε = (Θ.symm (t ε)).unop := by
  apply op_injective
  apply Θ.injective
  simpa only [← map_inv, Int.units_inv_eq_self, op_unop, MulEquiv.apply_symm_apply]
    using picardSignSplitting_apply_inv Θ hΘ hE t ε

variable (Θrot : (ClusterModularGroup k E)ᵐᵒᵖ ≃* boundaryRotationGroup B D)
variable (hrot : ∀ x : (ClusterModularGroup k E)ᵐᵒᵖ,
  rotationInclusion B D (Θrot x) = Θ (MonoidHom.op (clusterModularGroupInclusion k E) x))

omit [Finite ι] in
include hrot in
private theorem picardRotationInclusion_apply (x : Γ₀) :
    rotationInclusion B D (Θrot (op x⁻¹)) = Θ (op (inclusion x)⁻¹) := by
  simpa only [MonoidHom.op_apply_apply, map_inv, Function.comp_apply, unop_op]
    using hrot (op x⁻¹)

include hrot in
/-- The Picard equivalence after inversion intertwines the conjugation actions of the
transported section and the boundary section on the unsigned groups. -/
theorem picardSignSplitting_conjAct (ε : ℤˣ) (x : Γ₀) :
    Θrot (op ((picardSignSplitting Θ hΘ hE t).conjAct ε x)⁻¹) =
      t.conjAct ε (Θrot (op x⁻¹)) := by
  apply rotationInclusion_injective B D
  have h := congrArg ((MulEquiv.inv' Γₛ).trans Θ)
    ((picardSignSplitting Θ hΘ hE t).inl_conjAct ε x)
  simp only [map_mul, map_inv, signedInversionSignExtension_inl, MulEquiv.trans_apply,
    MulEquiv.inv'_apply, Function.comp_apply, picardSignSplitting_apply_inv,
    ← picardRotationInclusion_apply Θ Θrot hrot] at h
  exact h.trans (by simpa only [signExtension_inl] using (t.inl_conjAct ε (Θrot (op x⁻¹))).symm)

include hrot in
/-- Under Picard pullback after inversion, the semidirect product decomposition sends the
unsigned coordinate to its Picard rotation and preserves the sign coordinate. -/
theorem picardSignSplitting_semidirectProductMulEquiv
    (x : Γ₀ ⋊[(picardSignSplitting Θ hΘ hE t).conjAct] ℤˣ) :
    Θ (op ((picardSignSplitting Θ hΘ hE t).semidirectProductMulEquiv x)⁻¹) =
      t.semidirectProductMulEquiv ⟨Θrot (op x.left⁻¹), x.right⟩ := by
  simp only [GroupExtension.Splitting.semidirectProductMulEquiv_apply,
    signedInversionSignExtension_inl, signExtension_inl, mul_inv_rev, op_mul, map_mul,
    picardSignSplitting_apply_inv, picardRotationInclusion_apply Θ Θrot hrot]

end Splitting

omit [Finite ι] in
/-- Under a sign-compatible Picard equivalence, a negative-sign involution is represented
by an odd cluster word whose signed point map has order two. -/
theorem exists_odd_word_of_picard_involution
    (Θ : Γₛᵐᵒᵖ ≃* signedBoundaryIsometryGroup B D)
    (hΘ : ∀ (w : Word E E), sign B D (Θ eval[w]) = (-1 : ℤˣ) ^ w.inversionCount)
    (g : signedBoundaryIsometryGroup B D) (hg : sign B D g = -1) (hgg : g * g = 1) :
    ∃ w : Word E E, Θ eval[w] = g ∧ Odd w.inversionCount ∧
      orderOf (signedClusterModularGroupMap k E (End.of w)) = 2 := by
  obtain ⟨w, hw⟩ := signedClusterModularGroupMap_surjective k E (Θ.symm g).unop
  have hwg : Θ eval[End.asHom w] = g := by
    simp only [hw, op_unop, MulEquiv.apply_symm_apply]
  have hodd := (neg_one_pow_eq_neg_one_iff_odd (by decide : (-1 : ℤˣ) ≠ 1)).mp
    ((hΘ (End.asHom w)).symm.trans (hwg ▸ hg))
  let e := (MulEquiv.inv' Γₛ).trans Θ
  have he : e (signedClusterModularGroupMap k E w) = g⁻¹ := by
    rw [MulEquiv.trans_apply, MulEquiv.inv'_apply, Function.comp_apply, MulOpposite.op_inv,
      map_inv, hwg]
  have horder := (e.orderOf_eq (signedClusterModularGroupMap k E w)).symm.trans
    (he.symm ▸ (orderOf_inv g).trans (orderOf_eq_two_of_sign_eq_neg_one B D g hg hgg))
  exact ⟨End.asHom w, hwg, hodd, horder⟩

section CentralInvolution

variable [NeZero n]

omit [Finite ι] in
/-- The point map whose Picard pullback is the identity with negative branch sign. -/
noncomputable def picardCentralInvolution
    (Θ : Γₛᵐᵒᵖ ≃* signedBoundaryIsometryGroup B D) (hn : n ≤ 2) : Γₛ :=
  (Θ.symm (centralSign B D hn)).unop

variable (Θ : (SignedClusterModularGroup k E)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B D)
  (hn : n ≤ 2)

omit [Finite ι] in
/-- The Picard pullback of the central involution is the pure sign change. -/
@[simp]
theorem signedEquiv_apply_picardCentralInvolution :
    Θ (op (picardCentralInvolution Θ hn)) = centralSign B D hn := by
  simp only [picardCentralInvolution, op_unop, MulEquiv.apply_symm_apply]

omit [Finite ι] in
/-- A signed point map with pure sign-change Picard pullback is the central involution. -/
theorem eq_picardCentralInvolution_iff (z : Γₛ) :
    z = picardCentralInvolution Θ hn ↔ Θ (op z) = centralSign B D hn := by
  rw [← signedEquiv_apply_picardCentralInvolution Θ hn, Θ.injective.eq_iff, op_injective.eq_iff]

omit [Finite ι] in
/-- The lift of the pure sign change commutes with every signed point map. -/
theorem picardCentralInvolution_mem_center :
    picardCentralInvolution Θ hn ∈ Subgroup.center Γₛ := by
  have h : op (picardCentralInvolution Θ hn) ∈ Subgroup.center Γₛᵐᵒᵖ := by
    apply (MulEquivClass.apply_mem_center_iff Θ).mp
    simpa only [signedEquiv_apply_picardCentralInvolution, ← Subgroup.coe_center, SetLike.mem_coe]
      using centralSign_mem_center B D hn
  exact ((Subgroup.centerToMulOpposite Γₛ).symm ⟨_, h⟩).property

omit [Finite ι] in
/-- The lift of the pure sign change has order two. -/
@[simp]
theorem orderOf_picardCentralInvolution : orderOf (picardCentralInvolution Θ hn) = 2 := by
  calc
    orderOf (picardCentralInvolution Θ hn) = orderOf (op (picardCentralInvolution Θ hn)) := by
      simpa only [MulEquiv.inv'_apply, Function.comp_apply, MulOpposite.op_inv, orderOf_inv] using
        ((MulEquiv.inv' Γₛ).orderOf_eq (picardCentralInvolution Θ hn)).symm
    _ = orderOf (centralSign B D hn) := by
      rw [← Θ.orderOf_eq, signedEquiv_apply_picardCentralInvolution]
    _ = 2 := orderOf_centralSign B D hn

variable
  (hΘ : ∀ w : Word E E, sign B D (Θ (op (signedClusterModularGroupMap k E (End.of w)))) =
    (-1 : ℤˣ) ^ w.inversionCount)
  (hE : E.matrix ≠ 0)

include hΘ in
/-- The central Picard involution has negative inversion sign. -/
@[simp]
theorem signedInversionSign_picardCentralInvolution :
    signedInversionSign k E hE (picardCentralInvolution Θ hn) = -1 := by
  rw [← sign_picardHom_apply_op Θ.toMonoidHom hΘ hE, MulEquiv.coe_toMonoidHom,
    signedEquiv_apply_picardCentralInvolution]
  simp

include hΘ hE in
/-- For at most two boundary components, multiplication identifies the signed point maps
with the product of the unsigned maps and the cyclic subgroup of the pure sign change. -/
noncomputable def picardCentralInvolutionMulEquiv :
    Γ₀ × Subgroup.zpowers (picardCentralInvolution Θ hn) ≃* Γₛ :=
  mulEquivProdZPowersOfCentralInvolution k E
    (signedInversionSign_picardCentralInvolution Θ hn hΘ hE)
    (orderOf_picardCentralInvolution Θ hn) (picardCentralInvolution_mem_center Θ hn)

/-- The direct-product equivalence evaluates by multiplication of point maps. -/
@[simp]
theorem picardCentralInvolutionMulEquiv_apply
    (x : Γ₀ × Subgroup.zpowers (picardCentralInvolution Θ hn)) :
    picardCentralInvolutionMulEquiv Θ hn hΘ hE x = inclusion x.1 * x.2.val :=
  mulEquivProdZPowersOfCentralInvolution_apply k E _ _ _ x

end CentralInvolution

end QPainleve.SignedClusterModularGroup
