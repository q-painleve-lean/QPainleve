/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Group
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.SignExtension

import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Reflection

/-!
# The sign extension of marked cluster modular groups

The marked Picard equivalence transports a boundary reflection to an involution
of the signed group of independent X point maps. Its section gives the
semidirect product of unsigned maps and signs with the corresponding Picard
conjugation action. For one or two boundary components, the pure sign change
gives a central involution and a direct product.
-/

public noncomputable section

open CategoryTheory MulOpposite Quiver
open QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup

namespace QPainleve.SignedClusterModularGroup

namespace CompleteToricPresentation

open AlgebraicGeometry QPainleve.CharacterTorus
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData
open GeometricRealization (Point)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)} (Q : CompleteToricPresentation i b r L γ)
  (P : ChargeSeed E N) {c : Point Centers[r]} {M : MarkedSurface ℂ n B XTor[r]}

local notation "d" => M.boundaryClass M.isEffectiveCartier_boundaryIdeal
local notation "δ" => classOf(M.isEffectiveCartier_boundaryIdeal)
local notation "δL" => ∑ j, d j
local notation "Γ₀" => ClusterModularGroup ℂ E
local notation "Γₛ" => SignedClusterModularGroup ℂ E

local instance splittingFanNonempty : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance splittingCycleNeZero : NeZero Q.length := Q.neZero
local instance splittingBoundaryPrestable :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "χ[" t "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left t) (Over.w t))
local notation "eval[" w "]" => op (signedClusterModularGroupMap ℂ E (End.of w))
local notation "models[" F "," C "]" =>
  GeometricRealization.HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r])
    (b := b) (s := Q.rays) (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin)
    (ι := Q.inclusion) (P₁ := F) (fun t ↦ χ[t]) C

local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))

omit [NeZero n] in
private theorem exists_odd_word_of_picard_involution
    {dc : ZMod n → L} (Θ : (Γₛ)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B dc)
    (hΘ : ∀ (w : Word E E), sign B dc (Θ eval[w]) = (-1 : ℤˣ) ^ w.inversionCount)
    (g : signedBoundaryIsometryGroup B dc) (hg : sign B dc g = -1) (hgg : g * g = 1) :
    ∃ w : Word E E, Θ eval[w] = g ∧ Odd w.inversionCount ∧
      orderOf (signedClusterModularGroupMap ℂ E (End.of w)) = 2 := by
  obtain ⟨w, hw⟩ := signedClusterModularGroupMap_surjective ℂ E (Θ.symm g).unop
  have hwg : Θ eval[End.asHom w] = g := by
    simp only [hw, op_unop, MulEquiv.apply_symm_apply]
  have hodd := (neg_one_pow_eq_neg_one_iff_odd (by decide : (-1 : ℤˣ) ≠ 1)).mp
    ((hΘ (End.asHom w)).symm.trans (hwg ▸ hg))
  let e := (MulEquiv.inv' Γₛ).trans Θ
  have he : e (signedClusterModularGroupMap ℂ E w) = g⁻¹ := by
    rw [MulEquiv.trans_apply, MulEquiv.inv'_apply, Function.comp_apply, MulOpposite.op_inv,
      map_inv, hwg]
  have horder := (e.orderOf_eq (signedClusterModularGroupMap ℂ E w)).symm.trans
    (he.symm ▸ (orderOf_inv g).trans (orderOf_eq_two_of_sign_eq_neg_one B dc g hg hgg))
  exact ⟨End.asHom w, hwg, hodd, horder⟩

private theorem exists_central_involution
    {dc : ZMod n → L} (Θ : (Γₛ)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B dc)
    (hΘ : ∀ (w : Word E E), sign B dc (Θ eval[w]) = (-1 : ℤˣ) ^ w.inversionCount)
    (hE : E.matrix ≠ 0) (hn : n ≤ 2) :
    ∃ z : Γₛ, Θ (op z) = centralSign B dc hn ∧ z ∈ Subgroup.center Γₛ ∧ orderOf z = 2 ∧
      ∃ e : Γ₀ × Subgroup.zpowers z ≃* Γₛ, ∀ (f : Γ₀) (u : Subgroup.zpowers z),
        e (f, u) = clusterModularGroupInclusion ℂ E f * u.val := by
  let g := centralSign B dc hn
  have hgg : g * g = 1 := by
    rw [← pow_two, ← orderOf_centralSign B dc hn]
    exact pow_orderOf_eq_one _
  obtain ⟨w, hw, hodd, horder⟩ := exists_odd_word_of_picard_involution Θ hΘ g (by simp [g]) hgg
  have hc : signedClusterModularGroupMap ℂ E (End.of w) ∈ Subgroup.center Γₛ := by
    rw [Subgroup.mem_center_iff]
    intro f
    apply op_injective
    apply Θ.injective
    simpa only [op_mul, map_mul, hw] using
      (Subgroup.mem_center_iff.mp (centralSign_mem_center B dc hn) (Θ (op f))).symm
  exact ⟨_, hw, hc, horder,
    exists_mulEquiv_prod_zpowers_of_central_odd_loop ℂ E (hB := hE) w hodd horder hc⟩

/-- The signed Picard lift of a boundary reflection has order two and splits
the inversion-sign extension for a primitive nef square-zero anticanonical cycle.
The unsigned subgroup has index two. The signed and unsigned Picard equivalences
identify the resulting conjugation actions and semidirect products after inversion.
For a cycle of one or two components, the pure sign change lifts to a central
involution and multiplication gives the product with its cyclic subgroup.
The reference marked nodal model may have repeated centers. -/
theorem exists_signedPicardSplitting_of_nodal_model
    (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (href : Q.HasNodalModel c M)
    (hnef : (δ).IsNef ℂ (M.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M.surface δ δ = 0)
    (hprim : IsPrimitive (Additive.ofMul δ)) :
    ∃ (F : Point Centers[r] → MarkedSurface ℂ n B XTor[r])
      (hmark : ∀ t j, (F t).boundaryClass (F t).isEffectiveCartier_boundaryIdeal j = d j),
      F c = M ∧ (∀ t, Q.HasNodalModel t (F t)) ∧
      ∃ (Θ : (Γₛ)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B d)
        (Θrot : (Γ₀)ᵐᵒᵖ ≃* boundaryRotationGroup B d) (hE : E.matrix ≠ 0)
        (hs : Function.Surjective (signedInversionSign ℂ E hE))
        (s : (signedInversionSignExtension ℂ E hE hs).Splitting),
        (∀ x, rotationInclusion B d (Θrot x) =
          Θ (MonoidHom.op (clusterModularGroupInclusion ℂ E) x)) ∧
        (∀ w : Word E E, sign B d (Θ eval[w]) = (-1 : ℤˣ) ^ w.inversionCount ∧
          ∀ {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
            [C.IsOver Centers[r].hom Centers[r].hom]
            (R : GeometricRealization F F C (w.xRationalMap ℂ)), models[F,C] →
            Θ eval[w] = R.toSignedBoundaryIsometry d
              (fun t ↦ (F t).isEffectiveCartier_boundaryIdeal) hmark) ∧
        (clusterModularGroupInclusion ℂ E).range.index = 2 ∧
        orderOf (s (-1)) = 2 ∧
        (∃ (j₀ : ZMod n) (a : L) (g : signedBoundaryIsometryGroup B d)
          (hg : sign B d g = -1) (hgg : g * g = 1),
          let t := signSplitting B d g hg hgg
          let g₀ := (toIsometry B d g).val
          B a a = -1 ∧ (∀ j, B a (d j) = if j = j₀ then 1 else 0) ∧
          g₀ a = a ∧ g₀ δL = δL ∧ (∀ j, g₀ (d j) = d (2 * j₀ - j)) ∧
          (∀ x ∈ B.orthogonal (Submodule.span ℤ (Set.range d)), g₀ x = -x + (2 * B x a) • δL) ∧
          (∀ ε, Θ (op (s ε)) = t ε) ∧
          (∀ ε x, Θrot (op (s.conjAct ε x)⁻¹) = t.conjAct ε (Θrot (op x⁻¹))) ∧
          ∀ x : Γ₀ ⋊[s.conjAct] ℤˣ,
            Θ (op (s.semidirectProductMulEquiv x)⁻¹) =
              t.semidirectProductMulEquiv ⟨Θrot (op x.left⁻¹), x.right⟩) ∧
        ∀ hn : n ≤ 2, ∃ z : Γₛ,
          Θ (op z) = centralSign B d hn ∧ z ∈ Subgroup.center Γₛ ∧ orderOf z = 2 ∧
          ∃ e : Γ₀ × Subgroup.zpowers z ≃* Γₛ, ∀ (f : Γ₀) (u : Subgroup.zpowers z),
            e (f, u) = clusterModularGroupInclusion ℂ E f * u.val := by
  let : IsRationalOver (M.surface ↘ S) := href.isRationalOver
  have hcan := congrArg Inv.inv (href.canonicalClass M.isEffectiveCartier_boundaryIdeal)
  have hindex := Q.chargeIndex_ne_zero_of_anticanonical_cycle
    (M := fun _ ↦ M) href M.isEffectiveCartier_boundaryIdeal hnef hsq hcan hprim
  have hE := Q.exchangeMatrix_ne_zero_of_chargeIndex_ne_zero P hform hcharge hindex
  have hmatrix := P.matrix_eq.symm.trans (congrArg₂ chargeExchangeMatrix hform hcharge)
  obtain ⟨F, hD, hmark, Θ, Θrot, hFc, hfamily, hΘ, -, hrot⟩ :=
    Q.exists_picardGroupEquivs_of_nodal_model href hmatrix hprim hnef hsq
  obtain ⟨j₀, a, g, haa, ha, hg, hgg, hfix, hsum, hreflect, horth⟩ :=
    M.exists_marked_boundary_reversing_involution hcan hnef hsq hprim
  have hsign (w : Word E E) := (hΘ w).1
  obtain ⟨hs, s, hsection, hconj, hsemi⟩ :=
    exists_signSplitting_of_picardEquivs Θ Θrot hsign hrot hE (signSplitting B d g hg hgg)
  obtain ⟨w, hw, hodd, horder⟩ := exists_odd_word_of_picard_involution Θ hsign g hg hgg
  have hsect : s (-1) = signedClusterModularGroupMap ℂ E (End.of w) := by
    apply op_injective
    apply Θ.injective
    rw [hsection, signSplitting_neg_one, hw]
  exact ⟨F, hmark, hFc, hfamily, Θ, Θrot, hE, hs, s, hrot, hΘ,
    index_range_clusterModularGroupInclusion ℂ E hE hodd, hsect ▸ horder,
    ⟨j₀, a, g, hg, hgg, haa, ha, hfix, hsum, hreflect, horth, hsection, hconj, hsemi⟩,
    exists_central_involution Θ hsign hE⟩

end CompleteToricPresentation

end QPainleve.SignedClusterModularGroup
