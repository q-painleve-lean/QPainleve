/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.SignExtension
public import QPainleve.SignedClusterModularGroup.Boundary.Isometry
public import TauCeti.GroupTheory.GroupExtension.Splitting

/-!
# Splitting the signed cluster modular group

The signed Picard equivalence identifies pullbacks with signed boundary
isometries. Inversion turns it into a multiplicative equivalence on point
maps and preserves the sign. This transports the section of the boundary
sign extension to the sign extension of cluster modular groups, using
`GroupExtension.splittingEquivOfMulEquiv`.

For a boundary of one or two components, the pure sign change gives a central
involution of the signed cluster modular group. Its section makes the group a
direct product with the unsigned cluster modular group. For a longer boundary
with distinct classes, the underlying Picard isometry determines the signed map.
-/

public noncomputable section

open CategoryTheory MulOpposite Quiver
open QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup

namespace QPainleve.SignedClusterModularGroup

variable {k : Type*} [Field k] {ι : Type*} [DecidableEq ι] {E : SkewExchangeMatrix ι}
  {L : Type*} [AddCommGroup L] {n : ℕ} {B : LinearMap.BilinForm ℤ L} {D : ZMod n → L}

local notation "Γ" => ClusterModularGroup k E
local notation "Γs" => SignedClusterModularGroup k E
local notation "G" => signedBoundaryIsometryGroup B D

variable (Θ : (SignedClusterModularGroup k E)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B D)

section Sign

variable [CharZero k] [Finite ι] {hE : E.matrix ≠ 0}

/-- Agreement of the signs on loop representatives gives agreement on all point maps. -/
theorem sign_signedPicardEquiv_of_loop
    (h : ∀ w : Word E E,
      sign B D (Θ (op (signedClusterModularGroupMap k E (End.of w)))) =
        (-1 : ℤˣ) ^ w.inversionCount)
    (f : Γs) : sign B D (Θ (op f)) = signedInversionSign k E hE f := by
  obtain ⟨⟨w⟩, rfl⟩ := signedClusterModularGroupMap_surjective k E f
  exact (h w).trans (signedInversionSign_apply k E hE (End.of w)).symm

variable (hΘ : ∀ f : SignedClusterModularGroup k E,
    sign B D (Θ (op f)) = signedInversionSign k E hE f)
  {hs : Function.Surjective (sign B D)}

include Θ hΘ in
/-- A sign-preserving Picard equivalence transfers surjectivity to the point-map sign. -/
theorem signedInversionSign_surjective_of_signedPicardEquiv
    (hs : Function.Surjective (sign B D)) : Function.Surjective (signedInversionSign k E hE) := by
  intro ε
  obtain ⟨g, hg⟩ := hs ε
  refine ⟨(Θ.symm g).unop, ?_⟩
  rw [← hΘ, op_unop, MulEquiv.apply_symm_apply, hg]

include Θ hΘ in
/-- A surjective Picard sign gives the unsigned point maps index two in the signed group. -/
theorem index_range_clusterModularGroupInclusion_of_signedPicardEquiv
    (hs : Function.Surjective (sign B D)) : (clusterModularGroupInclusion k E).range.index = 2 := by
  obtain ⟨f, hf⟩ := signedInversionSign_surjective_of_signedPicardEquiv Θ hΘ hs (-1)
  obtain ⟨w, rfl⟩ := signedClusterModularGroupMap_surjective k E f
  rw [signedInversionSign_apply] at hf
  exact index_range_clusterModularGroupInclusion k E hE
    ((neg_one_pow_eq_neg_one_iff_odd (by decide : (-1 : ℤˣ) ≠ 1)).mp hf)

/-- Transport a lattice-side sign splitting to the group of signed point maps. -/
def signedPicardSplitting (Θ : (Γs)ᵐᵒᵖ ≃* G)
    (hΘ : ∀ f : Γs, sign B D (Θ (op f)) = signedInversionSign k E hE f)
    (s : (signExtension B D hs).Splitting) :
    (signedInversionSignExtension k E hE
      (signedInversionSign_surjective_of_signedPicardEquiv Θ hΘ hs)).Splitting := by
  let e := (MulEquiv.inv' Γs).trans Θ
  have he (f : Γs) : sign B D (e f) = signedInversionSign k E hE f := by
    -- The inverse in the point group appears because the Picard action is a pullback.
    simpa only [e, MulEquiv.trans_apply, MulEquiv.inv'_apply, Function.comp_apply,
      map_inv, Int.units_inv_eq_self] using hΘ f⁻¹
  refine (signExtension B D hs).splittingEquivOfMulEquiv _ e.symm (MulEquiv.refl ℤˣ) ?_ s
  ext g
  simp only [signedInversionSignExtension_rightHom, signExtension_rightHom, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.refl_apply]
  rw [← he, e.apply_symm_apply]

/-- The transported section has the prescribed signed Picard action at each sign. -/
@[simp]
theorem signedPicardEquiv_op_signedPicardSplitting_apply
    (s : (signExtension B D hs).Splitting) (ε : ℤˣ) :
    Θ (op (signedPicardSplitting Θ hΘ s ε)) = s ε := by
  rw [signedPicardSplitting, GroupExtension.splittingEquivOfMulEquiv_apply]
  simp only [MulEquiv.refl_symm, MulEquiv.refl_apply, MulEquiv.symm_trans_apply,
    MulEquiv.inv'_symm_apply, Function.comp_apply, MulOpposite.op_inv, op_unop,
    MulEquiv.apply_symm_apply, map_inv]
  rw [← map_inv s, Int.units_inv_eq_self]

/-- The signed point map supplied by the negative sign of a Picard splitting has order two. -/
theorem orderOf_signedPicardSplitting_neg_one (s : (signExtension B D hs).Splitting) :
    orderOf (signedPicardSplitting Θ hΘ s (-1)) = 2 := by
  let t := signedPicardSplitting Θ hΘ s
  rw [← t.toMonoidHom_apply, orderOf_injective _ t.rightInverse_rightHom.injective]
  simp [Units.orderOf_neg_one]

/-- In the split point-map group, the sign factor acts on the unsigned maps by conjugation
by the point map with the lattice section's signed Picard action. -/
theorem clusterModularGroupInclusion_signedPicardSplitting_conjAct
    (s : (signExtension B D hs).Splitting) (ε : ℤˣ) (f : Γ) :
    let z := (Θ.symm (s ε)).unop
    clusterModularGroupInclusion k E ((signedPicardSplitting Θ hΘ s).conjAct ε f) =
      z * clusterModularGroupInclusion k E f * z⁻¹ := by
  have hz : signedPicardSplitting Θ hΘ s ε = (Θ.symm (s ε)).unop :=
    (Θ.injective.comp op_injective) (by simp)
  simpa only [signedInversionSignExtension_inl, hz] using
    (signedPicardSplitting Θ hΘ s).inl_conjAct ε f

end Sign

/-- For at least three distinct boundary classes, the signed Picard equivalence identifies
the opposite group of signed point maps with the subgroup of underlying boundary isometries. -/
def signedPicardMulEquivToIsometryRange (Θ : (Γs)ᵐᵒᵖ ≃* G)
    (hn : 3 ≤ n) (hD : Function.Injective D) :
    (Γs)ᵐᵒᵖ ≃* (toIsometry B D).range :=
  Θ.trans (MonoidHom.ofInjective (toIsometry_injective B D hn hD))

@[simp]
theorem coe_signedPicardMulEquivToIsometryRange_apply
    (hn : 3 ≤ n) (hD : Function.Injective D) (f : (Γs)ᵐᵒᵖ) :
    (signedPicardMulEquivToIsometryRange Θ hn hD f).val = toIsometry B D (Θ f) :=
  (rfl)

section SmallBoundary

variable [NeZero n] (hn : n ≤ 2)

/-- The signed point map with identity Picard isometry and negative boundary sign
for a one- or two-component boundary. -/
def signedPicardCentralInvolution (Θ : (Γs)ᵐᵒᵖ ≃* G) (hn : n ≤ 2) : Γs :=
  (Θ.symm (centralSign B D hn)).unop

@[simp]
theorem signedPicardEquiv_op_centralInvolution :
    Θ (op (signedPicardCentralInvolution Θ hn)) = centralSign B D hn := by
  simp [signedPicardCentralInvolution]

/-- The pure sign change commutes with every signed point map. -/
theorem signedPicardCentralInvolution_mem_center :
    signedPicardCentralInvolution Θ hn ∈ Subgroup.center Γs := by
  rw [Subgroup.mem_center_iff]
  intro f
  apply (Θ.injective.comp op_injective)
  simp only [Function.comp_apply, op_mul, map_mul, signedPicardEquiv_op_centralInvolution]
  exact (Subgroup.mem_center_iff.mp (centralSign_mem_center B D hn) _).symm

/-- The central sign change is a nonidentity involution. -/
theorem orderOf_signedPicardCentralInvolution :
    orderOf (signedPicardCentralInvolution Θ hn) = 2 := by
  let e := (MulEquiv.inv' Γs).trans Θ
  have he : e (signedPicardCentralInvolution Θ hn) = (centralSign B D hn)⁻¹ := by
    simp [e, MulEquiv.inv'_apply, MulOpposite.op_inv]
  rw [← e.orderOf_eq, he, orderOf_inv, orderOf_centralSign]

variable [CharZero k] [Finite ι] {hE : E.matrix ≠ 0}
  (hΘ : ∀ f : SignedClusterModularGroup k E,
    sign B D (Θ (op f)) = signedInversionSign k E hE f)

private def centralPicardSplitting (Θ : (Γs)ᵐᵒᵖ ≃* G) (hn : n ≤ 2)
    (hΘ : ∀ f : Γs, sign B D (Θ (op f)) = signedInversionSign k E hE f) :
    (signedInversionSignExtension k E hE (signedInversionSign_surjective_of_signedPicardEquiv Θ hΘ
      (sign_surjective B D (centralSign B D hn) (by simp)))).Splitting :=
  signedPicardSplitting Θ hΘ (signSplitting B D (centralSign B D hn) (by simp)
    (by rw [← pow_two, ← orderOf_centralSign B D hn, pow_orderOf_eq_one]))

private theorem centralPicardSplitting_neg_one :
    centralPicardSplitting Θ hn hΘ (-1) = signedPicardCentralInvolution Θ hn := by
  apply Θ.injective.comp op_injective
  simp [centralPicardSplitting]

private theorem centralPicardSplitting_conjAct_eq_one :
    (centralPicardSplitting Θ hn hΘ).conjAct = 1 := by
  apply MonoidHom.ext
  intro ε
  apply MulEquiv.ext
  intro f
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp
  · apply clusterModularGroupInclusion_injective k E
    have hact := (centralPicardSplitting Θ hn hΘ).inl_conjAct (-1) f
    rw [signedInversionSignExtension_inl, centralPicardSplitting_neg_one] at hact
    have h := Subgroup.mem_center_iff.mp (signedPicardCentralInvolution_mem_center Θ hn)
      (clusterModularGroupInclusion k E f)
    simpa only [← h, mul_inv_cancel_right, MonoidHom.one_apply, MulAut.one_apply] using hact

/-- A boundary with one or two components gives the direct product of unsigned maps
with the sign group. The negative generator of the sign factor is the central point
map with identity Picard action. -/
def signedPicardMulEquivProdOfLeTwo (Θ : (Γs)ᵐᵒᵖ ≃* G) (hn : n ≤ 2)
    (hΘ : ∀ f : Γs, sign B D (Θ (op f)) = signedInversionSign k E hE f) : Γ × ℤˣ ≃* Γs :=
  let s := centralPicardSplitting Θ hn hΘ
  let e : Γ ⋊[(1 : ℤˣ →* MulAut Γ)] ℤˣ ≃* Γ ⋊[s.conjAct] ℤˣ :=
    SemidirectProduct.congr (MulEquiv.refl Γ) (MulEquiv.refl ℤˣ) (by
      rw [centralPicardSplitting_conjAct_eq_one Θ hn hΘ]
      intro ε
      rfl)
  SemidirectProduct.mulEquivProd.symm.trans (e.trans s.semidirectProductMulEquiv)

@[simp]
theorem signedPicardMulEquivProdOfLeTwo_apply_one (f : Γ) :
    signedPicardMulEquivProdOfLeTwo Θ hn hΘ (f, 1) = clusterModularGroupInclusion k E f := by
  simp [signedPicardMulEquivProdOfLeTwo, GroupExtension.Splitting.semidirectProductMulEquiv_apply]

@[simp]
theorem signedPicardMulEquivProdOfLeTwo_apply_neg_one :
    signedPicardMulEquivProdOfLeTwo Θ hn hΘ (1, -1) = signedPicardCentralInvolution Θ hn := by
  simp [signedPicardMulEquivProdOfLeTwo, GroupExtension.Splitting.semidirectProductMulEquiv_apply,
    centralPicardSplitting_neg_one]

@[simp]
theorem signedPicardMulEquivProdOfLeTwo_symm_snd (f : Γs) :
    ((signedPicardMulEquivProdOfLeTwo Θ hn hΘ).symm f).2 = signedInversionSign k E hE f := by
  simp [signedPicardMulEquivProdOfLeTwo]

private theorem range_centralPicardSplitting :
    (centralPicardSplitting Θ hn hΘ).toMonoidHom.range =
      Subgroup.zpowers (signedPicardCentralInvolution Θ hn) := by
  have hgen : Subgroup.zpowers (-1 : ℤˣ) = ⊤ := by
    refine top_unique fun ε _ ↦ ?_
    rcases Int.units_eq_one_or ε with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_zpowers,
    GroupExtension.Splitting.toMonoidHom_apply, centralPicardSplitting_neg_one]

private def centralPicardSplittingEquivZPowers (Θ : (Γs)ᵐᵒᵖ ≃* G) (hn : n ≤ 2)
    (hΘ : ∀ f : Γs, sign B D (Θ (op f)) = signedInversionSign k E hE f) :
    ℤˣ ≃* Subgroup.zpowers (signedPicardCentralInvolution Θ hn) :=
  let s := centralPicardSplitting Θ hn hΘ
  (MonoidHom.ofInjective (f := s.toMonoidHom) s.rightInverse_rightHom.injective).trans
    (MulEquiv.subgroupCongr (range_centralPicardSplitting Θ hn hΘ))

/-- For a one- or two-component boundary, the unsigned group and the subgroup generated by
the central sign change multiply to the signed group as a direct product. -/
def signedPicardMulEquivProdZPowersOfLeTwo (Θ : (Γs)ᵐᵒᵖ ≃* G) (hn : n ≤ 2)
    (hΘ : ∀ f : Γs, sign B D (Θ (op f)) = signedInversionSign k E hE f) :
    Γ × Subgroup.zpowers (signedPicardCentralInvolution Θ hn) ≃* Γs :=
  (MulEquiv.prodCongr (MulEquiv.refl Γ) (centralPicardSplittingEquivZPowers Θ hn hΘ).symm).trans
    (signedPicardMulEquivProdOfLeTwo Θ hn hΘ)

@[simp]
theorem signedPicardMulEquivProdZPowersOfLeTwo_apply
    (f : Γ) (z : Subgroup.zpowers (signedPicardCentralInvolution Θ hn)) :
    signedPicardMulEquivProdZPowersOfLeTwo Θ hn hΘ (f, z) =
      clusterModularGroupInclusion k E f * z.val := by
  let e := centralPicardSplittingEquivZPowers Θ hn hΘ
  obtain ⟨ε, rfl⟩ := e.surjective z
  have hp : (MulEquiv.prodCongr (MulEquiv.refl Γ) e.symm) (f, e ε) = (f, ε) :=
    Prod.ext rfl (e.symm_apply_apply ε)
  rw [signedPicardMulEquivProdZPowersOfLeTwo, MulEquiv.trans_apply, hp]
  simp [e, centralPicardSplittingEquivZPowers, signedPicardMulEquivProdOfLeTwo,
    GroupExtension.Splitting.semidirectProductMulEquiv_apply, MonoidHom.ofInjective_apply]

end SmallBoundary

end QPainleve.SignedClusterModularGroup
