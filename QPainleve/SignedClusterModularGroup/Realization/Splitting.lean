/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.SignExtension
public import QPainleve.SignedClusterModularGroup.Realization.Boundary
public import QPainleve.SignedClusterModularGroup.Realization.Presentation

import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.Endpoint.Kernel
import QPainleve.SignedClusterModularGroup.Realization.Endpoint.PicardAction
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Family
import QPainleve.SignedClusterModularGroup.Realization.Reflection
import QPainleve.SignedClusterModularGroup.Realization.Surjectivity.Torelli
import QPainleve.SignedClusterModularGroup.Realization.Surjectivity.Word

/-!
# The sign extension of marked cluster modular groups

A reversing reflection of a marked anticanonical cycle lifts to an involution of the
group of independent X point maps. The proof uses Torelli and specified word realization
to lift the designated reflection, then uses faithfulness of the signed Picard action to
compute the order of the lift. A central lift yields a direct product for short
boundary cycles.

The word-lifting argument follows [the Picard surjectivity proof]
(https://github.com/q-painleve-lean/QPainleve/pull/780) for the two involutions used here.
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

private theorem exists_word_orderOf_eq_two_of_signed_involution
    {F : Point Centers[r] → MarkedSurface ℂ n B XTor[r]}
    {hF : ∀ t, D[F t].IsEffectiveCartier}
    {dc : ZMod n → L} (hmark : ∀ t j, (F t).boundaryClass (hF t) j = dc j)
    (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (models : ∀ t : Point Centers[r], t.left (default : S) ∈ Path.nil.centerOpen ℂ P →
      Q.HasNodalModel t (F t))
    {c : Point Centers[r]} (href : Q.HasNodalModel c (F c))
    (hnef : (classOf(hF c)).IsNef ℂ ((F c).surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ (F c).surface classOf(hF c) classOf(hF c) = 0)
    (hprim : IsPrimitive (Additive.ofMul classOf(hF c)))
    (ρ : (Γₛ)ᵐᵒᵖ →* signedBoundaryIsometryGroup B dc) (hρinj : Function.Injective ρ)
    (hρ : ∀ (w : Word E E)
      (R : GeometricRealization F F (w.centerPartialMap ℂ P) (w.xRationalMap ℂ)),
      models[F,w.centerPartialMap ℂ P] → ρ eval[w] = R.toSignedBoundaryIsometry dc hF hmark)
    {g : signedBoundaryIsometryGroup B dc} (hg : sign B dc g = -1) (hgg : g * g = 1) :
    ∃ w : Word E E, ρ eval[w] = g ∧
      orderOf (signedClusterModularGroupMap ℂ E (End.of w)) = 2 := by
  have hK : P.charge.ker ≤ (Fan.rayChargeMap Q.rays).ker :=
    le_of_eq (congrArg LinearMap.ker hcharge)
  obtain ⟨c₀, c₁, -, hm₁, hword, hprim₀, hnef₀, hsq₀, -, -, e, act, hsign, -, hact, hpic⟩ :=
    Q.exists_root_free_pair_iso_of_signed_boundary_isometry P hK hF
      (fun t ↦ funext (hmark t)) href hprim hnef hsq models g
  have hsgn :
      letI : PrestableFamily ((F c₀).boundary ↘ S) := (F c₀).prestable
      letI : PrestableFamily ((F c₁).boundary ↘ S) := (F c₁).prestable
      DihedralGroup.cycleOrientationSign ((MarkedSurface.boundaryIso e).boundaryCycleAction
        (F c₀).cycle (F c₁).cycle) = sign B dc g := by
    rw [hact, hsign]
  obtain ⟨w, hw, -, -⟩ := GeometricRealization.exists_word_signedPicardHom_eq_of_pair_iso P
    hform hcharge models hm₁ hnef₀ hsq₀ hprim₀ (fun w ↦ (hword w).1) ρ hρ e hpic hsgn
  let x := signedClusterModularGroupMap ℂ E (End.of w)
  have hxx : x * x = 1 := op_injective (hρinj (by
    rw [op_mul, map_mul, hw, hgg, op_one, map_one]))
  refine ⟨w, hw, orderOf_eq_prime (by rwa [pow_two]) ?_⟩
  intro hx
  have hg₁ : g = 1 := by simpa only [hx, op_one, map_one] using hw.symm
  rw [hg₁, map_one] at hg
  exact (by decide : (-1 : ℤˣ) ≠ 1) hg.symm

private theorem exists_central_involution {hE : E.matrix ≠ 0}
    {F : Point Centers[r] → MarkedSurface ℂ n B XTor[r]}
    {hF : ∀ t, D[F t].IsEffectiveCartier}
    {dc : ZMod n → L} (hmark : ∀ t j, (F t).boundaryClass (hF t) j = dc j)
    (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (models : ∀ t : Point Centers[r], t.left (default : S) ∈ Path.nil.centerOpen ℂ P →
      Q.HasNodalModel t (F t))
    {c : Point Centers[r]} (href : Q.HasNodalModel c (F c))
    (hnef : (classOf(hF c)).IsNef ℂ ((F c).surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ (F c).surface classOf(hF c) classOf(hF c) = 0)
    (hprim : IsPrimitive (Additive.ofMul classOf(hF c)))
    (ρ : (Γₛ)ᵐᵒᵖ →* signedBoundaryIsometryGroup B dc) (hρinj : Function.Injective ρ)
    (hρ : ∀ (w : Word E E)
      (R : GeometricRealization F F (w.centerPartialMap ℂ P) (w.xRationalMap ℂ)),
      models[F,w.centerPartialMap ℂ P] → ρ eval[w] = R.toSignedBoundaryIsometry dc hF hmark)
    (hη : ∀ w : Word E E, sign B dc (ρ eval[w]) = (-1 : ℤˣ) ^ w.inversionCount)
    (hn : n ≤ 2) :
    ∃ z : Γₛ, ρ (op z) = centralSign B dc hn ∧ z ∈ Subgroup.center Γₛ ∧ orderOf z = 2 ∧
      ∃ e : Γ₀ × Subgroup.zpowers z ≃* Γₛ, ∀ (f : Γ₀) (u : Subgroup.zpowers z),
        e (f, u) = clusterModularGroupInclusion ℂ E f * u.val := by
  let g := centralSign B dc hn
  have hg : sign B dc g = -1 := by simp [g]
  have hgg : g * g = 1 := by
    rw [← pow_two, ← orderOf_centralSign B dc hn]
    exact pow_orderOf_eq_one _
  obtain ⟨w, hw, ho⟩ := Q.exists_word_orderOf_eq_two_of_signed_involution P hmark hform hcharge
    models href hnef hsq hprim ρ hρinj hρ hg hgg
  have hOdd := (neg_one_pow_eq_neg_one_iff_odd (by decide : (-1 : ℤˣ) ≠ 1)).mp
    ((hη w).symm.trans (by rw [hw, hg]))
  have hc : signedClusterModularGroupMap ℂ E (End.of w) ∈ Subgroup.center Γₛ := by
    rw [Subgroup.mem_center_iff]
    intro f
    apply op_injective
    apply hρinj
    simpa only [op_mul, map_mul, hw] using
      (Subgroup.mem_center_iff.mp (centralSign_mem_center B dc hn) (ρ (op f))).symm
  exact ⟨_, hw, hc, ho,
    exists_mulEquiv_prod_zpowers_of_central_odd_loop ℂ E (hB := hE) w hOdd ho hc⟩

/-- The signed Picard lift of a boundary reflection has order two and splits
the inversion-sign extension for a primitive nef square-zero anticanonical cycle.
The unsigned subgroup has index two. The induced semidirect product acts on the
unsigned subgroup by conjugation by the section. For a cycle of one or two components, the
pure sign change lifts to a central involution and multiplication identifies the
signed group with the product of the unsigned subgroup and its cyclic complement.
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
      ∃ (ρ : (Γₛ)ᵐᵒᵖ →* signedBoundaryIsometryGroup B d) (hE : E.matrix ≠ 0)
        (hs : Function.Surjective (signedInversionSign ℂ E hE))
        (s : (signedInversionSignExtension ℂ E hE hs).Splitting),
        Function.Injective ρ ∧
        (∀ (w : Word E E) {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
          [C.IsOver Centers[r].hom Centers[r].hom]
          (R : GeometricRealization F F C (w.xRationalMap ℂ)), models[F,C] →
          ρ eval[w] = R.toSignedBoundaryIsometry d
            (fun t ↦ (F t).isEffectiveCartier_boundaryIdeal) hmark) ∧
        (clusterModularGroupInclusion ℂ E).range.index = 2 ∧
        orderOf (s (-1)) = 2 ∧
        (∃ (j₀ : ZMod n) (a : L),
          let g := (toIsometry B d (ρ (op (s (-1))))).val
          B a a = -1 ∧ (∀ j, B a (d j) = if j = j₀ then 1 else 0) ∧ g a = a ∧ g δL = δL ∧
          (∀ j, g (d j) = d (2 * j₀ - j)) ∧
          ∀ x ∈ B.orthogonal (Submodule.span ℤ (Set.range d)), g x = -x + (2 * B x a) • δL) ∧
        ∀ hn : n ≤ 2, ∃ z : Γₛ,
          ρ (op z) = centralSign B d hn ∧ z ∈ Subgroup.center Γₛ ∧ orderOf z = 2 ∧
          ∃ e : Γ₀ × Subgroup.zpowers z ≃* Γₛ, ∀ (f : Γ₀) (u : Subgroup.zpowers z),
            e (f, u) = clusterModularGroupInclusion ℂ E f * u.val := by
  let : IsRationalOver (M.surface ↘ S) := href.isRationalOver
  have hcan := congrArg Inv.inv (href.canonicalClass M.isEffectiveCartier_boundaryIdeal)
  have hindex := Q.chargeIndex_ne_zero_of_anticanonical_cycle
    (M := fun _ ↦ M) href M.isEffectiveCartier_boundaryIdeal hnef hsq hcan hprim
  have hE := Q.exchangeMatrix_ne_zero_of_chargeIndex_ne_zero P hform hcharge hindex
  obtain ⟨F, hF, hFc, hfamily⟩ := Q.exists_marked_family_of_nodal_model href
    M.isEffectiveCartier_boundaryIdeal
  subst M
  have hmark (t : Point Centers[r]) (j : ZMod n) :
      (F t).boundaryClass (F t).isEffectiveCartier_boundaryIdeal j =
        (F c).boundaryClass (F c).isEffectiveCartier_boundaryIdeal j :=
    congrFun (hfamily t).2 j
  obtain ⟨ρ, ⟨hρ, _⟩, _⟩ := GeometricRealization.existsUnique_signedPicardHom_of_presentation
    P Q hform hcharge F (fun _ ↦ (hfamily _).1) href
    (fun t ↦ (F t).isEffectiveCartier_boundaryIdeal) hnef hsq hcan hprim _ hmark
  have hinj := ρ.ker_eq_bot_iff.mp
    (GeometricRealization.signedPicardHom_ker_eq_bot_of_presentation Q P hform hcharge F
      (fun t _ ↦ (hfamily t).1) (fun t ↦ (F t).isEffectiveCartier_boundaryIdeal) href
      hnef hsq hcan hprim _ hmark ρ (fun w _ _ _ ↦ (hρ w).2))
  obtain ⟨j₀, a, g, haa, ha, hg, hgg, hfix, hsum, hreflect, horth⟩ :=
    (F c).exists_marked_boundary_reversing_involution hcan hnef hsq hprim
  obtain ⟨w, hw, horder⟩ := Q.exists_word_orderOf_eq_two_of_signed_involution P hmark hform hcharge
    (fun t _ ↦ (hfamily t).1) href hnef hsq hprim ρ hinj (fun w ↦ (hρ (End.of w)).2) hg hgg
  have hη : (-1 : ℤˣ) ^ w.inversionCount = -1 :=
    (hρ (End.of w)).1.symm.trans (by rw [hw, hg])
  have hOdd := (neg_one_pow_eq_neg_one_iff_odd (by decide : (-1 : ℤˣ) ≠ 1)).mp hη
  let s := signSplittingOfOddInvolution ℂ E (hB := hE) w hOdd horder
  have hsect := signSplittingOfOddInvolution_neg_one ℂ E (hB := hE) w hOdd horder
  refine ⟨F, hmark, rfl, fun t ↦ (hfamily t).1, ρ, hE, _, s, hinj,
    fun w ↦ (hρ (End.of w)).2, index_range_clusterModularGroupInclusion ℂ E hE hOdd,
    hsect ▸ horder, ⟨j₀, a, haa, ha, ?_⟩, ?_⟩
  · simpa only [s, hsect, hw] using ⟨hfix, hsum, hreflect, horth⟩
  · intro hn
    exact Q.exists_central_involution (hE := hE) P hmark hform hcharge (fun t _ ↦ (hfamily t).1)
      href hnef hsq hprim ρ hinj (fun v ↦ (hρ (End.of v)).2)
      (fun v ↦ (hρ (End.of v)).1) hn

end CompleteToricPresentation

end QPainleve.SignedClusterModularGroup
