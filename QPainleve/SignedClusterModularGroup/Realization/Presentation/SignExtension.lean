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
-/

public section

open CategoryTheory MulOpposite Quiver
open QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup

namespace QPainleve.SignedClusterModularGroup

variable {k : Type*} [Field k] [CharZero k] {ι : Type*} [DecidableEq ι] [Finite ι]
  {E : SkewExchangeMatrix ι} {L : Type*} [AddCommGroup L] {n : ℕ}
  {B : LinearMap.BilinForm ℤ L} {D : ZMod n → L}

local notation "Γ₀" => ClusterModularGroup k E
local notation "Γₛ" => SignedClusterModularGroup k E
local notation "inclusion" => clusterModularGroupInclusion k E

/-- A sign-compatible pair of Picard equivalences transports a boundary sign section to the
point-map group. The section values correspond under pullback. The actions and semidirect
products correspond under the multiplicative equivalences given by inversion followed by
pullback. -/
theorem exists_signSplitting_of_picardEquivs
    (Θ : Γₛᵐᵒᵖ ≃* signedBoundaryIsometryGroup B D)
    (Θrot : Γ₀ᵐᵒᵖ ≃* boundaryRotationGroup B D)
    (hΘ : ∀ (w : Word E E), sign B D (Θ (op (signedClusterModularGroupMap k E (End.of w)))) =
      (-1 : ℤˣ) ^ w.inversionCount)
    (hrot : ∀ x, rotationInclusion B D (Θrot x) = Θ (MonoidHom.op inclusion x))
    (hE : E.matrix ≠ 0) {hsign : Function.Surjective (sign B D)}
    (t : (signExtension B D hsign).Splitting) :
    ∃ (hs : Function.Surjective (signedInversionSign k E hE))
      (s : (signedInversionSignExtension k E hE hs).Splitting),
      (∀ ε, Θ (op (s ε)) = t ε) ∧
      (∀ ε x, Θrot (op (s.conjAct ε x)⁻¹) = t.conjAct ε (Θrot (op x⁻¹))) ∧
      ∀ x : Γ₀ ⋊[s.conjAct] ℤˣ,
        Θ (op (s.semidirectProductMulEquiv x)⁻¹) =
          t.semidirectProductMulEquiv ⟨Θrot (op x.left⁻¹), x.right⟩ := by
  let e := (MulEquiv.inv' Γₛ).trans Θ
  let er := (MulEquiv.inv' Γ₀).trans Θrot
  have hsignWord (x : Γₛ) : sign B D (Θ (op x)) = signedInversionSign k E hE x := by
    obtain ⟨w, rfl⟩ := signedClusterModularGroupMap_surjective k E x
    exact (hΘ (End.asHom w)).trans (signedInversionSign_apply k E hE w).symm
  have hsignE (x : Γₛ) : sign B D (e x) = signedInversionSign k E hE x := by
    simpa only [e, MulEquiv.trans_apply, MulEquiv.inv'_apply, Function.comp_apply, map_inv,
      Int.units_inv_eq_self]
      using hsignWord x⁻¹
  have hs : Function.Surjective (signedInversionSign k E hE) := by
    rw [← funext hsignE]
    exact hsign.comp e.surjective
  have hright : (signExtension B D hsign).rightHom.comp e.toMonoidHom =
      (MulEquiv.refl ℤˣ).toMonoidHom.comp (signedInversionSignExtension k E hE hs).rightHom := by
    apply MonoidHom.ext
    intro x
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, signExtension_rightHom,
      signedInversionSignExtension_rightHom, MulEquiv.refl_apply] using hsignE x
  let s := ((signedInversionSignExtension k E hE hs).splittingEquivOfMulEquiv
    (signExtension B D hsign) e (MulEquiv.refl ℤˣ) hright).symm t
  have hsection (ε : ℤˣ) : e (s ε) = t ε := by simp [s]
  have hinclusion (x : Γ₀) : rotationInclusion B D (er x) = e (inclusion x) := by
    simpa only [er, e, MulEquiv.trans_apply, MulEquiv.inv'_apply, MonoidHom.op_apply_apply,
      map_inv, Function.comp_apply, unop_op] using hrot (op x⁻¹)
  refine ⟨hs, s, ?_, ?_, ?_⟩
  · intro ε
    have hinv : (s ε)⁻¹ = s ε := by rw [← map_inv, Int.units_inv_eq_self]
    simpa only [e, MulEquiv.trans_apply, MulEquiv.inv'_apply, Function.comp_apply, hinv]
      using hsection ε
  · intro ε x
    have hc : er (s.conjAct ε x) = t.conjAct ε (er x) := by
      apply rotationInclusion_injective B D
      have h := congrArg e (s.inl_conjAct ε x)
      simp only [signedInversionSignExtension_inl, map_mul, map_inv, hsection, ← hinclusion] at h
      exact h.trans (by simpa only [signExtension_inl] using (t.inl_conjAct ε (er x)).symm)
    simpa only [er, MulEquiv.trans_apply, MulEquiv.inv'_apply, Function.comp_apply] using hc
  · intro x
    have h := GroupExtension.Splitting.semidirectProductMulEquiv_apply s x
    rw [signedInversionSignExtension_inl] at h
    have hm : e (s.semidirectProductMulEquiv x) =
        t.semidirectProductMulEquiv ⟨er x.left, x.right⟩ := by
      rw [h, GroupExtension.Splitting.semidirectProductMulEquiv_apply, signExtension_inl,
        map_mul, ← hinclusion, hsection]
    simpa only [e, er, MulEquiv.trans_apply, MulEquiv.inv'_apply, Function.comp_apply] using hm

end QPainleve.SignedClusterModularGroup
