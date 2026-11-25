/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Action
public import QPainleve.SignedClusterModularGroup.Boundary.Restriction

import QPainleve.SignedClusterModularGroup.Realization.PicardAction

/-!
# Images of signed cluster actions on Casimir monomials

The Picard equivalence transports the boundary rotation image to the unsigned Casimir image.
The full Casimir image contains one further right coset, represented by the restriction of a
signed Picard reflection. The two cosets act with opposite signs on the total boundary exponent.
The reflection is Mathlib's `Module.reflection`, transported from
`SignedBoundaryIsometryGroup.exists_signedOrthogonalRestriction_eq_reflection`.
-/

public section

open MulOpposite
open scoped Pointwise RightActions

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

open Cluster SignedBoundaryIsometryGroup

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : SkewExchangeMatrix ι}
  {L : Type*} [AddCommGroup L] {n : ℕ} {B : LinearMap.BilinForm ℤ L} {D : ZMod n → L}

local notation "orth[" B "," D "]" => LinearMap.BilinForm.orthogonal B
  (Submodule.span ℤ (Set.range D))
local notation "exch[" E "]" => LinearMap.ker (Matrix.mulVecLin (SkewExchangeMatrix.matrix E))
local notation "total[" D "]" => ∑ i, D i
local notation "restr[" B "," D "]" => signedOrthogonalRestriction B D
local notation "incl[" k "," E "]" => MonoidHom.op (clusterModularGroupInclusion k E)
local notation "act[" k "," E "]" => exchangeKernelAction k E
local notation "unsignedImage[" k "," E "]" =>
  MonoidHom.range (MonoidHom.comp act[k,E] incl[k,E])

variable (Θ : (SignedClusterModularGroup k E)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B D)
  (e : orth[B,D] ≃ₗ[ℤ] exch[E])

local notation "coords[" B "," D "," a "]" =>
  MonoidHom.comp (MulEquiv.toMonoidHom (LinearEquiv.autCongr a))
    (Subgroup.subtype (LinearMap.BilinForm.isometryGroup
      (LinearMap.BilinForm.restrict B orth[B,D])))

variable (hCasimir : act[k,E] =
    MonoidHom.comp coords[B,D,e] (MonoidHom.comp restr[B,D] Θ.toMonoidHom))
  (hker : ((sign B D).comp Θ.toMonoidHom).ker.unop = (clusterModularGroupInclusion k E).range)

omit [Fintype ι] in
include hker in
private theorem range_picardEquiv_comp_unsignedInclusion :
    (Θ.toMonoidHom.comp incl[k,E]).range = (rotationInclusion B D).range := by
  let Θrot := picardRotationEquiv Θ hker
  have hcomp : (rotationInclusion B D).comp Θrot.toMonoidHom =
      Θ.toMonoidHom.comp incl[k,E] :=
    MonoidHom.ext (rotationInclusion_picardRotationEquiv_apply Θ hker)
  have hrange : Θrot.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr Θrot.surjective
  rw [← hcomp, MonoidHom.range_comp, hrange, Subgroup.map_top]

include hCasimir hker in
/-- The unsigned Casimir image is the image of the boundary rotations, restricted to the
boundary orthogonal and written in exchange-kernel coordinates. -/
theorem range_unsignedExchangeKernelAction_eq_rotationImage :
    unsignedImage[k,E] = (((restr[B,D]).comp (rotationInclusion B D)).range).map coords[B,D,e] := by
  rw [MonoidHom.range_comp (restr[B,D]), ← range_picardEquiv_comp_unsignedInclusion Θ hker]
  simp only [hCasimir, MonoidHom.range_comp, Subgroup.map_map, MonoidHom.comp_assoc]

include hCasimir in
private theorem exchangeKernelAction_picardEquiv_symm (s : signedBoundaryIsometryGroup B D) :
    act[k,E] (Θ.symm s) = LinearEquiv.autCongr e (restr[B,D] s).val := by
  rw [hCasimir]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    Subgroup.subtype_apply]

variable [NeZero n]

include hCasimir in
/-- A signed cluster pullback scales the total boundary exponent by the sign of its marked
Picard action. -/
theorem exchangeKernelAction_apply_boundary_sum (hδ : total[D] ∈ orth[B,D])
    (g : (SignedClusterModularGroup k E)ᵐᵒᵖ) :
    act[k,E] g (e ⟨total[D], hδ⟩) = sign B D (Θ g) • e ⟨total[D], hδ⟩ := by
  have hg := DFunLike.congr_fun hCasimir g
  rw [hg]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply,
    LinearEquiv.autCongr_apply_apply, LinearEquiv.symm_apply_apply,
    signedOrthogonalRestriction_apply_sum, Units.smul_def, map_smul]

include hCasimir hker in
/-- The signed Casimir image is the disjoint union of the unsigned image and its right coset
by the Casimir action of any lift with negative Picard sign. -/
theorem range_exchangeKernelAction_eq_disjoint_union [IsAddTorsionFree L]
    (hδ : total[D] ∈ orth[B,D]) (hδ₀ : total[D] ≠ 0)
    (s : signedBoundaryIsometryGroup B D) (hs : sign B D s = -1) :
    let unsigned : Set (exch[E] ≃ₗ[ℤ] exch[E]) := unsignedImage[k,E]
    let q := act[k,E] (Θ.symm s)
    (↑(act[k,E]).range : Set (exch[E] ≃ₗ[ℤ] exch[E])) = unsigned ∪ (unsigned <• q) ∧
      Disjoint unsigned (unsigned <• q) := by
  dsimp only
  have hW := range_unsignedExchangeKernelAction_eq_rotationImage Θ e hCasimir hker
  have hfull : (act[k,E]).range = ((restr[B,D]).range).map coords[B,D,e] := by
    rw [hCasimir, MonoidHom.range_comp coords[B,D,e], MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective Θ.toMonoidHom Θ.surjective, Subgroup.map_top]
  have hC : Function.Injective coords[B,D,e] :=
    (LinearEquiv.autCongr e).injective.comp Subtype.val_injective
  have hq : act[k,E] (Θ.symm s) = coords[B,D,e] (restr[B,D] s) :=
    exchangeKernelAction_picardEquiv_symm Θ e hCasimir s
  rw [hfull, hW, Subgroup.coe_map, Subgroup.coe_map, hq, ← Set.image_op_smul_distrib]
  constructor
  · rw [← Set.image_union, range_signedOrthogonalRestriction_eq_union B D s hs]
  · exact Set.disjoint_image_of_injective hC (disjoint_rotationRange_rightCoset hδ hδ₀ s hs)

variable {Θ e}

include hCasimir in
/-- For a boundary of length one or two, the central sign change acts on the exchange kernel
by negation. -/
theorem exchangeKernelAction_picardEquiv_symm_centralSign (hn : n ≤ 2) (x : exch[E]) :
    act[k,E] (Θ.symm (centralSign B D hn)) x = -x := by
  rw [exchangeKernelAction_picardEquiv_symm Θ e hCasimir,
    LinearEquiv.autCongr_apply_apply, signedOrthogonalRestriction_centralSign_apply, map_neg,
    LinearEquiv.apply_symm_apply]

variable (Θ e)

include hCasimir hker in
/-- For a unimodular symmetric cycle lattice with primitive characteristic total class,
a signed Picard involution acts on the exchange kernel by reflection along the total
boundary exponent. This reflection represents the odd coset of the unsigned Casimir
image and acts trivially modulo the total boundary exponent. -/
theorem exists_exchangeKernelAction_reflection [Module.Free ℤ L] [Module.Finite ℤ L]
    [B.IsPerfPair] (hSymm : B.IsSymm)
    (hGram : ∀ i j : ZMod n, B (D i) (D j) = (-2 : ℤ) * (if i = j then 1 else 0) +
      (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))
    (hPrimitive : TauCeti.IsPrimitive total[D]) (hCharacteristic : B.IsCharacteristic total[D]) :
    ∃ (hδ : total[D] ∈ orth[B,D]) (a : L) (s : signedBoundaryIsometryGroup B D),
      let v := e ⟨total[D], hδ⟩
      let ℓ := ((2 : ℤ) • (B.flip a).comp (orth[B,D]).subtype).comp
        (e.symm : exch[E] →ₗ[ℤ] orth[B,D])
      ∃ hℓ : ℓ v = 2,
        let q := Module.reflection hℓ
        let unsigned : Set (exch[E] ≃ₗ[ℤ] exch[E]) := unsignedImage[k,E]
        sign B D s = -1 ∧ s * s = 1 ∧ act[k,E] (Θ.symm s) = q ∧
          (↑(act[k,E]).range : Set (exch[E] ≃ₗ[ℤ] exch[E])) = unsigned ∪ (unsigned <• q) ∧
          Disjoint unsigned (unsigned <• q) ∧
          ∀ x, (ℤ ∙ v).mkQ (q x) = (ℤ ∙ v).mkQ x := by
  obtain ⟨hδ, a, s, hℓ, hs, hss, hreflect, -⟩ :=
    exists_signedOrthogonalRestriction_eq_reflection B D hSymm hGram hPrimitive hCharacteristic
  let v := e ⟨total[D], hδ⟩
  let ℓ := ((2 : ℤ) • (B.flip a).comp (orth[B,D]).subtype).comp (e.symm : exch[E] →ₗ[ℤ] orth[B,D])
  have hℓ' : ℓ v = 2 := by
    simpa only [ℓ, v, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      using hℓ
  have hq : act[k,E] (Θ.symm s) = Module.reflection hℓ' := by
    rw [exchangeKernelAction_picardEquiv_symm Θ e hCasimir, hreflect]
    ext x : 1
    simp only [LinearEquiv.autCongr_apply_apply, Module.reflection_apply, map_sub, map_smul,
      LinearEquiv.apply_symm_apply, ℓ, v, LinearMap.comp_apply, LinearEquiv.coe_coe]
  let : HasUniqueDiv L := HasUniqueDiv.of_isTorsionFree ℤ L
  obtain ⟨himage, hdisjoint⟩ :=
    range_exchangeKernelAction_eq_disjoint_union Θ e hCasimir hker hδ hPrimitive.ne_zero s hs
  refine ⟨hδ, a, s, hℓ', hs, hss, hq, ?_, ?_, ?_⟩
  · simpa only [hq] using himage
  · simpa only [hq] using hdisjoint
  · intro x
    rw [Module.reflection_apply, map_sub, sub_eq_self, ← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end QPainleve.SignedClusterModularGroup.GeometricRealization
