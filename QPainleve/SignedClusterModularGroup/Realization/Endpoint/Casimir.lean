/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.ChargeKernel.Basic
public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.SelfRealization

import QPainleve.AlgebraicGeometry.Chow.Nef.Boundary
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.Geometry.Toric.Fan.Presentation.Genus
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Orthogonal
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Boundary

/-!
# Casimir action in a marked toric presentation

The descended signed Picard action determines the Casimir action on the group of
independent X maps. The two actions are compared in integral charge
coordinates. The total boundary class detects the sign on the Casimir image.

The comparison combines `exists_realize_signed_loop` with
`chargeKernelAction_eq_signedOrthogonalRestriction`. The exchange-kernel
action evaluates on monomials by `Cluster.exchangeKernelAction_monomial`.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Centers[" r "]" => Over.mk (structureMap k₀ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme k₀ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "Cw[" w "," P "]" => Path.centerPartialMap k₀ w P
local notation "U₀[" P "]" => Path.centerOpen k₀ Path.nil P
local notation "dst[" C "," c "]" =>
  c ≫ Scheme.PartialMap.domainTarget (X := Centers[_]) (Y := Centers[_]) C
local notation "χ[" c "]" => pointsEquiv k₀ _
  (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "Loops[" E "]" => End (Prefunctor.obj (Paths.of (SkewExchangeMatrix (Fin _))) E)
local notation "eval[" w "]" => op (signedClusterModularGroupMap k₀ _ (w))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)}

variable (Q : CompleteToricPresentation k₀ i b r L γ)

local notation "orth[" H "," d "]" =>
  LinearMap.BilinForm.orthogonal H (Submodule.span ℤ (Set.range d))
local notation "TargetModels[" M "," C "]" =>
  HasToricTargetModels (b := b) (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin)
    (s := Q.rays) (ι := Q.inclusion) (T₀ := Centers[r]) (T₁ := Centers[r]) (P₁ := M)
    (fun c : Point Centers[r] ↦ χ[c]) C

private theorem sign_eq_one_of_mem_ker_signedOrthogonalRestriction
    (P : MarkedSurface k₀ n H XTor[r]) [IsRationalOver (P.surface ↘ S)]
    (hD : D[P].IsEffectiveCartier) (hnef : (classOf(hD)).IsNef k₀ (P.surface ↘ S))
    (hsq : Chow.classIntersectionNumber k₀ P.surface classOf(hD) classOf(hD) = 0)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD)))
    {d : ZMod n → L} (hd : P.boundaryClass hD = d)
    {g : signedBoundaryIsometryGroup H d} (hg : g ∈ (signedOrthogonalRestriction H d).ker) :
    sign H d g = 1 := by
  let : IsIntegral P.surface := P.integral
  let : P.surface.IsProjectiveOver k₀ := P.projective
  let : SmoothOfRelativeDimension 2 (P.surface ↘ S) := P.smooth
  let : Module.Free ℤ (Additive (LineBundleClass P.surface)) :=
    P.surface.free_picard_of_isRationalOver k₀
  let : HasUniqueDiv (Additive (LineBundleClass P.surface)) := .of_isTorsionFree ℤ _
  let : IsAddTorsionFree L := P.picardMarking.injective.isAddTorsionFree
    P.picardMarking.toAddEquiv.toAddMonoidHom
  have hδ : (∑ j, d j) ∈ orth[H,d] := by
    rw [← hd, ← P.picardMarking_mem_boundaryOrthogonal_iff hD,
      P.picardMarking_sum_boundaryClass hD]
    exact (hD.effectiveCartierClass_mem_boundaryOrthogonal_iff_of_isNef hnef).mpr hsq
  have hδ₀ : (∑ j, d j) ≠ 0 := by
    rw [← hd]
    intro hzero
    exact hprim.ne_zero (by rw [← P.picardMarking_sum_boundaryClass hD, hzero, map_zero])
  exact MonoidHom.mem_ker.mp (ker_signedOrthogonalRestriction_le_ker_sign hδ hδ₀ hg)

/-- The signed Picard homomorphism characterized by the marked pullbacks of
loop realizations gives the Casimir action on every independent X map. The
boundary orthogonal is identified with the exchange kernel by the negatives of
the total exceptional coefficients. The kernel of the Casimir action, read in
the point-map group, lies in the unsigned subgroup. -/
theorem existsUnique_exchangeKernelEquiv_of_presentation
    (P : ChargeSeed E N) (hform : P.form = b.detDualEquiv.toLinearMap)
    (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (M : Point Centers[r] → MarkedSurface k₀ n H XTor[r])
    (hD : ∀ c, D[M c].IsEffectiveCartier)
    {c₀ : Point Centers[r]} (href : Q.HasNodalModel c₀ (M c₀))
    (models : ∀ c : Point Centers[r], c.left (default : S) ∈ U₀[P] → Q.HasNodalModel c (M c))
    (hnef : (classOf(hD c₀)).IsNef k₀ ((M c₀).surface ↘ S))
    (hsq : Chow.classIntersectionNumber k₀ (M c₀).surface classOf(hD c₀) classOf(hD c₀) = 0)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD c₀)))
    (d : ZMod n → L) (hmark : ∀ c j, (M c).boundaryClass (hD c) j = d j)
    (ρ : (SignedClusterModularGroup k₀ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup H d)
    (hρ : ∀ (w : Loops[E]) {C : Centers[r].left.PartialMap Centers[r].left}
      [IsDominant C.hom] [C.IsOver Centers[r].hom Centers[r].hom],
      letI : ((End.asHom w).xRationalMap k₀).IsDominant :=
        Path.instIsDominantXRationalMap k₀ (End.asHom w)
      letI := Q.complete.nonempty_cones
      letI := Q.prestable
      letI := Q.neZero
      ∀ (R : GeometricRealization M M C ((End.asHom w).xRationalMap k₀)),
        TargetModels[M,C] → ρ eval[w] = R.toSignedBoundaryIsometry d hD hmark) :
    ∃! e : orth[H,d] ≃ₗ[ℤ] E.matrix.mulVecLin.ker,
      (∀ x, (Q.inclusion x.val).2 = -(e x : Fin r → ℤ)) ∧
      exchangeKernelAction k₀ E =
        (LinearEquiv.autCongr e).toMonoidHom.comp
          ((H.restrict orth[H,d]).isometryGroup.subtype.comp
            ((signedOrthogonalRestriction H d).comp ρ)) ∧
      (exchangeKernelAction k₀ E).ker.unop ≤ (clusterModularGroupInclusion k₀ E).range := by
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  -- A reference fiber fixes the two kernel identifications for the whole family.
  have hindex := href.chargeIndex_ne_zero (hD c₀) hnef hsq hprim
  have hker : E.matrix.mulVecLin.ker = P.charge.ker := by
    rw [← P.matrix_eq, hform, hcharge]
    exact Fan.ker_chargeExchangeMatrix_rayChargeMap b Q.rays hindex
  let : (Q.fan.finiteFanScheme k₀).IsProjectiveOver k₀ :=
    Q.fan.isProjectiveOver_finiteFanScheme_of_isComplete k₀ Q.regular Q.complete b
  let := Q.smoothOfRelativeDimension_fan
  let := Q.isPerfPair_auxiliaryPicardForm
  let e := href.chargeKernelEquiv (hD c₀) (funext (hmark c₀))
  have he := href.chargeKernelEquiv_symm_apply (hD c₀) (funext (hmark c₀))
  have hker' := hker.trans (congrArg LinearMap.ker hcharge)
  let j := (LinearEquiv.ofEq _ _ hker).trans
    (LinearEquiv.ofEq _ _ (congrArg LinearMap.ker hcharge))
  have hj : LinearEquiv.ofEq _ _ hker' = j := by
    ext x : 1
    exact Subtype.ext (by simp [j])
  let e' := href.exchangeKernelEquiv (hD c₀) (funext (hmark c₀)) hker'
  have he' : e' = e.trans j.symm := by
    simp only [e', href.exchangeKernelEquiv_def, hj, e]
  have hcoordinates (x : orth[H,d]) : (Q.inclusion x.val).2 = -(e' x : Fin r → ℤ) := by
    simp [e']
  -- Use the same geometric realization for the charge action and its sign.
  have comparison (w : Loops[E]) :
      exchangeKernelAction k₀ E eval[w] =
        LinearEquiv.autCongr e' (signedOrthogonalRestriction H d (ρ eval[w])).val ∧
      sign H d (ρ eval[w]) = (-1 : ℤˣ) ^ (End.asHom w).inversionCount := by
    let word : Word E E := End.asHom w
    obtain ⟨R, hsign, _, htargets⟩ := exists_realize_signed_loop word P Q hform hcharge M
      (fun x ↦ models _ (Path.nil.centerPoint_endpoints_mem_noncollision P hker x).2)
      href hD hnef hsq hprim d hmark
    let : IsDominant Cw[word,P].hom := inferInstance
    let : Cw[word,P].IsOver Centers[r].hom Centers[r].hom :=
      inferInstanceAs (Cw[word,P].IsOver
        (structureMap k₀ (Fin r → ℤ)) (structureMap k₀ (Fin r → ℤ)))
    have hmodels : TargetModels[M,Cw[word,P]] :=
      fun c ↦ (htargets c).nonempty_contractedToricFiber
    rw [hρ w (C := Cw[word,P]) R hmodels]
    refine ⟨?_, ?_⟩
    · have h := chargeKernelAction_eq_signedOrthogonalRestriction Q.rayOrder
        (fun k ↦ (Q.cycle.component_apply k).symm.trans (Q.component_eq k))
        (fun k ↦ (Q.positive k).1) Q.exists_cone_of_numbered_node d hD hmark word R
        (word.centerPartialMap_hom (K := k₀) P) P hcharge hker e he
        (U := {c : Point Centers[r] | c.left (default : S) ∈ U₀[P]})
        (word.centerPoint_endpoints_mem_noncollision P hker)
        (fun c hc ↦ by
          let : IsIntegral (M c).surface := (M c).integral
          let : (M c).surface.IsProjectiveOver k₀ := (M c).projective
          let : SmoothOfRelativeDimension 2 ((M c).surface ↘ S) := (M c).smooth
          let : PrestableFamily (D[M c].subscheme ↘ S) := (M c).prestable_boundaryImage
          exact (models c hc).hasToricPresentation.genus_blowupComponent_eq_zero (hD c))
        (fun c hc ↦ ⟨((Q.hasNodalModel_iff c (M c)).mp (models c hc)).choose⟩)
      have hw : (End.of word : Loops[E]) = w := End.ext rfl
      apply (LinearEquiv.autCongr j).injective
      simpa only [hw, chargeKernelAction_apply, he', j, ← LinearEquiv.autCongr_trans,
        MulEquiv.trans_apply, ← LinearEquiv.autCongr_symm, MulEquiv.apply_symm_apply] using! h
    · exact (SignedBoundaryIsometryGroup.sign_apply H d _).trans
        ((congrArg Prod.snd (coe_toSignedBoundaryIsometry R d hD hmark)).trans hsign)
  refine ⟨e', ⟨hcoordinates, ?_, ?_⟩, fun f hf ↦ ?_⟩
  · apply MonoidHom.ext
    intro g
    obtain ⟨w, hw⟩ := signedClusterModularGroupMap_surjective k₀ E g.unop
    simpa only [hw, op_unop, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.subtype_apply] using (comparison w).1
  · -- A trivial restriction fixes the total boundary class, so the loop is even.
    intro g hg
    obtain ⟨w, rfl⟩ := signedClusterModularGroupMap_surjective k₀ E g
    have hg₁ := MonoidHom.mem_ker.mp (Subgroup.mem_unop.mp hg)
    have hrestrict : ρ eval[w] ∈ (signedOrthogonalRestriction H d).ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      apply (LinearEquiv.autCongr e').injective
      simpa only [hg₁, map_one, OneMemClass.coe_one] using (comparison w).1.symm
    let : IsRationalOver ((M c₀).surface ↘ S) := href.isRationalOver
    have hsign := sign_eq_one_of_mem_ker_signedOrthogonalRestriction
      (M c₀) (hD c₀) hnef hsq hprim (funext (hmark c₀)) hrestrict
    rw [(comparison w).2, neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)] at hsign
    have hu := (mem_unsignedLoopPullbacks_iff_exists_even k₀ E _).mpr
      ⟨End.asHom w, hsign, rfl⟩
    refine ⟨op ⟨_, hu⟩, unop_injective (Subtype.ext ?_)⟩
    simp only [clusterModularGroupInclusion, MonoidHom.op_apply_apply, Function.comp_apply,
      unop_op, Subgroup.coe_inclusion, signedClusterModularGroupMap_unop_coe]
    rfl
  · exact LinearEquiv.ext fun x ↦
      Subtype.ext (neg_injective ((hf.1 x).symm.trans (hcoordinates x)))

end QPainleve.SignedClusterModularGroup.GeometricRealization
