/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.SignExtension
public import QPainleve.SignedClusterModularGroup.Boundary.Isometry

import Mathlib.Data.Int.Order.Units
import TauCeti.GroupTheory.GroupExtension.Splitting

/-!
# Transport of the signed Picard splitting

The Picard sign of a realized loop agrees with its descended inversion sign.
For a sign-preserving Picard isomorphism on the opposite cluster modular group,
inversion gives an isomorphism of the point-map group with the signed boundary
isometry group that still preserves the sign. This transports the lattice
splitting by `GroupExtension.splittingEquivOfMulEquiv`. On a boundary of length
one or two, the central lift of the negative sign gives a direct product.
-/

public noncomputable section

open CategoryTheory MulOpposite Quiver
open QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup

namespace QPainleve.SignedClusterModularGroup

variable {k : Type*} [Field k] {ι : Type*} [DecidableEq ι]
  {E : SkewExchangeMatrix ι} {L : Type*} [AddCommGroup L] [Module ℤ L]
  {n : ℕ} {B : LinearMap.BilinForm ℤ L} {D : ZMod n → L}

local notation "Γ" => ClusterModularGroup k E
local notation "Γ'" => Cluster.SignedClusterModularGroup k E
local notation "Ĝ" => signedBoundaryIsometryGroup B D
local notation "Loops" => End (Prefunctor.obj (Paths.of (SkewExchangeMatrix ι)) E)

section Sign

variable [CharZero k] [Finite ι]

/-- The sign formula on representatives identifies the Picard sign with the
intrinsic inversion sign on every signed X map. -/
theorem sign_picardHom_eq_signedInversionSign (hE : E.matrix ≠ 0) (ρ : (Γ')ᵐᵒᵖ →* Ĝ)
    (hρ : ∀ w : Loops, sign B D (ρ (op (signedClusterModularGroupMap k E w))) =
      (-1 : ℤˣ) ^ w.asHom.inversionCount) (f : Γ') :
    sign B D (ρ (op f)) = signedInversionSign k E hE f := by
  obtain ⟨w, rfl⟩ := signedClusterModularGroupMap_surjective k E f
  rw [hρ, signedInversionSign_apply]

local notation "pointEquiv(" e ")" => MulEquiv.trans (MulEquiv.inv' Γ') e

/-- The isomorphism on point maps obtained by composing the Picard pullback
with inversion still preserves the sign. -/
theorem sign_signedPicardEquiv_inv (hE : E.matrix ≠ 0) (picard : (Γ')ᵐᵒᵖ ≃* Ĝ)
    (hpicard : ∀ f : Γ', sign B D (picard (op f)) = signedInversionSign k E hE f) (f : Γ') :
    sign B D (pointEquiv(picard) f) = signedInversionSign k E hE f := by
  simp only [MulEquiv.trans_apply, MulEquiv.inv'_apply, Function.comp_apply, hpicard,
    map_inv, Int.units_inv_eq_self]

/-- Transport a splitting of the lattice sign to a splitting of the inversion
sign on point maps. Its semidirect-product isomorphism is supplied by
`GroupExtension.Splitting.semidirectProductMulEquiv`. -/
def splittingOfSignedPicardEquiv
    (hE : E.matrix ≠ 0) (picard : (Γ')ᵐᵒᵖ ≃* Ĝ)
    (hpicard : ∀ f : Γ', sign B D (picard (op f)) = signedInversionSign k E hE f)
    {hs : Function.Surjective (signedInversionSign k E hE)}
    {ht : Function.Surjective (sign B D)} (s : (signExtension B D ht).Splitting) :
    (signedInversionSignExtension k E hE hs).Splitting :=
  ((signedInversionSignExtension k E hE hs).splittingEquivOfMulEquiv (signExtension B D ht)
    pointEquiv(picard) (MulEquiv.refl ℤˣ) (MonoidHom.ext fun f ↦ by
      simpa using sign_signedPicardEquiv_inv hE picard hpicard f)).symm s

@[simp]
theorem splittingOfSignedPicardEquiv_apply
    (hE : E.matrix ≠ 0) (picard : (Γ')ᵐᵒᵖ ≃* Ĝ)
    (hpicard : ∀ f : Γ', sign B D (picard (op f)) = signedInversionSign k E hE f)
    {hs : Function.Surjective (signedInversionSign k E hE)}
    {ht : Function.Surjective (sign B D)} (s : (signExtension B D ht).Splitting) (ε : ℤˣ) :
    splittingOfSignedPicardEquiv hE picard hpicard (hs := hs) s ε =
      (pointEquiv(picard)).symm (s ε) := by
  simp [splittingOfSignedPicardEquiv]

/-- The involutive negative-sign lattice lift gives a point-map splitting whose
negative-sign element is the Picard preimage of the chosen involution. -/
theorem exists_splitting_signedInversionSignExtension
    (hE : E.matrix ≠ 0) (picard : (Γ')ᵐᵒᵖ ≃* Ĝ)
    (hpicard : ∀ f : Γ', sign B D (picard (op f)) = signedInversionSign k E hE f)
    (g : Ĝ) (hg : sign B D g = -1) (hg₂ : g * g = 1) :
    ∃ (hs : Function.Surjective (signedInversionSign k E hE))
      (s : (signedInversionSignExtension k E hE hs).Splitting),
      s (-1) = (picard.symm g).unop ∧ orderOf (s (-1)) = 2 := by
  have hs : Function.Surjective (signedInversionSign k E hE) := by
    simpa only [Function.Surjective, Function.comp_apply,
      sign_signedPicardEquiv_inv hE picard hpicard] using
        (sign_surjective B D g hg).comp (pointEquiv(picard)).surjective
  let s := splittingOfSignedPicardEquiv hE picard hpicard (hs := hs) (signSplitting B D g hg hg₂)
  have horder := orderOf_eq_two_of_sign_eq_neg_one B D g hg hg₂
  have hs' : s (-1) = (pointEquiv(picard)).symm g := by simp [s]
  have he : (pointEquiv(picard)).symm g = (picard.symm g).unop := by
    have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg₂
    rw [MulEquiv.symm_trans_apply, MulEquiv.inv'_symm_apply, Function.comp_apply,
      ← MulOpposite.unop_inv, ← map_inv, hinv]
  refine ⟨hs, s, hs'.trans he, ?_⟩
  rw [hs', (pointEquiv(picard)).symm.orderOf_eq, horder]

/-- With one or two boundary components, the pure sign change gives a central
involution on point maps and a direct product with the unsigned group. The
product coordinates preserve the unsigned inclusion and the inversion sign. -/
theorem exists_clusterModularGroup_mulEquiv_prod_of_le_two [NeZero n] (hn : n ≤ 2)
    (hE : E.matrix ≠ 0) (picard : (Γ')ᵐᵒᵖ ≃* Ĝ)
    (hpicard : ∀ f : Γ', sign B D (picard (op f)) = signedInversionSign k E hE f) :
    let z := (picard.symm (centralSign B D hn)).unop
    z ∈ Subgroup.center Γ' ∧ orderOf z = 2 ∧
      ∃ p : Γ × ℤˣ ≃* Γ', (∀ g, p (g, 1) = clusterModularGroupInclusion k E g) ∧
        p (1, -1) = z ∧ ∀ x, signedInversionSign k E hE (p x) = x.2 := by
  intro z
  let c := centralSign B D hn
  have hc : sign B D c = -1 := by simp [c]
  have hc₂ : c * c = 1 := by
    simpa [pow_two, c, orderOf_centralSign] using pow_orderOf_eq_one c
  obtain ⟨hs, s, hz, ho⟩ :=
    exists_splitting_signedInversionSignExtension hE picard hpicard c hc hc₂
  let S := signedInversionSignExtension k E hE hs
  have hsz : s (-1) = z := hz
  have hpreimage : (pointEquiv(picard)) z = c := by
    rw [MulEquiv.trans_apply, MulEquiv.inv'_apply, Function.comp_apply, MulOpposite.op_inv]
    simp only [z, c, op_unop, map_inv, MulEquiv.apply_symm_apply]
    exact inv_eq_of_mul_eq_one_right hc₂
  have hcenter : z ∈ Subgroup.center Γ' :=
    Subgroup.comap_center_le_center (f := pointEquiv(picard)) (pointEquiv(picard)).injective
      (Subgroup.mem_comap.mpr (hpreimage ▸ centralSign_mem_center B D hn))
  have htriv : s.conjAct = 1 := by
    ext ε g
    rcases Int.units_eq_one_or ε with rfl | rfl
    · simp
    · apply S.inl_injective
      rw [GroupExtension.Splitting.conjAct, MonoidHom.comp_apply,
        GroupExtension.inl_conjAct_comm, MonoidHom.one_apply, MulAut.one_apply,
        MonoidHom.coe_ofClass, hsz,
        ← Subgroup.mem_center_iff.mp hcenter (S.inl g), mul_inv_cancel_right]
  let e : Γ ⋊[(1 : ℤˣ →* MulAut Γ)] ℤˣ ≃* Γ ⋊[s.conjAct] ℤˣ :=
    SemidirectProduct.congr (MulEquiv.refl Γ) (MulEquiv.refl ℤˣ) (fun ε ↦ by ext g; simp [htriv])
  let p := (SemidirectProduct.mulEquivProd.symm.trans e).trans s.semidirectProductMulEquiv
  have hp (x : Γ × ℤˣ) : p x = S.inl x.1 * s x.2 := by
    simp [p, e, S, GroupExtension.Splitting.semidirectProductMulEquiv_apply]
  refine ⟨hcenter, hsz ▸ ho, p, fun g ↦ ?_, ?_, fun x ↦ ?_⟩
  · simp [hp, S]
  · simpa [hp, S] using hsz
  · have hr := s.rightHom_splitting x.2
    rw [signedInversionSignExtension_rightHom] at hr
    have hi := S.rightHom_inl x.1
    simp only [S, signedInversionSignExtension_rightHom] at hi
    rw [hp, map_mul, hi, hr, one_mul]

end Sign

/-- For an injectively indexed boundary of length at least three, the opposite
point-map group is isomorphic to the image of the signed boundary isometries
in the ambient isometry group. -/
def signedPicardEquivToIsometryRange (picard : (Γ')ᵐᵒᵖ ≃* Ĝ)
    (hn : 3 ≤ n) (hD : Function.Injective D) : (Γ')ᵐᵒᵖ ≃* (toIsometry B D).range :=
  picard.trans (MonoidHom.ofInjective (toIsometry_injective B D hn hD))

@[simp]
theorem coe_signedPicardEquivToIsometryRange_apply (picard : (Γ')ᵐᵒᵖ ≃* Ĝ)
    (hn : 3 ≤ n) (hD : Function.Injective D) (f : (Γ')ᵐᵒᵖ) :
    (signedPicardEquivToIsometryRange picard hn hD f : B.isometryGroup) =
      toIsometry B D (picard f) := by
  rw [signedPicardEquivToIsometryRange, MulEquiv.trans_apply, MonoidHom.ofInjective_apply]

end QPainleve.SignedClusterModularGroup
