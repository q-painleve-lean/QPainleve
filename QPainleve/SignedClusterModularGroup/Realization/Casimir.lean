/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.ChargeKernel
public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.SelfRealization

import QPainleve.AlgebraicGeometry.Chow.Nef.Boundary
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic

/-!
# Casimir action in a marked toric presentation

The descended signed Picard action determines the Casimir action on the group of
independent X maps. The two actions are compared in integral charge
coordinates. The total boundary class detects the sign on the Casimir image.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "Cw[" w "," P "]" => Path.centerPartialMap ℂ w P
local notation "U₀[" P "]" => Path.centerOpen ℂ Path.nil P
local notation "dst[" C "," c "]" =>
  c ≫ Scheme.PartialMap.domainTarget (X := Centers[_]) (Y := Centers[_]) C
local notation "χ[" c "]" => pointsEquiv ℂ _
  (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "Loops[" E "]" => End (Prefunctor.obj (Paths.of (SkewExchangeMatrix (Fin _))) E)
local notation "eval[" w "]" => op (signedClusterModularGroupMap ℂ _ (w))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)}

variable (Q : CompleteToricPresentation i b r L γ)

local notation "orth[" H "," d "]" =>
  LinearMap.BilinForm.orthogonal H (Submodule.span ℤ (Set.range d))
local notation "fiberAt[" M "," c "]" =>
  ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c] (M c)
local notation "TargetModels[" M "," C "]" =>
  HasToricTargetModels (b := b) (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin)
    (s := Q.rays) (ι := Q.inclusion) (T₀ := Centers[r]) (T₁ := Centers[r]) (P₁ := M)
    (fun c : Point Centers[r] ↦ χ[c]) C

private theorem sign_eq_one_of_mem_ker_signedOrthogonalRestriction
    (P : MarkedSurface ℂ n H XTor[r]) [IsRationalOver (P.surface ↘ S)]
    (hD : D[P].IsEffectiveCartier) (hnef : (classOf(hD)).IsNef ℂ (P.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ P.surface classOf(hD) classOf(hD) = 0)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD)))
    {d : ZMod n → L} (hd : P.boundaryClass hD = d)
    {g : signedBoundaryIsometryGroup H d} (hg : g ∈ (signedOrthogonalRestriction H d).ker) :
    sign H d g = 1 := by
  let : IsIntegral P.surface := P.integral
  let : P.surface.IsProjectiveOver ℂ := P.projective
  let : SmoothOfRelativeDimension 2 (P.surface ↘ S) := P.smooth
  let : Module.Free ℤ (Additive (LineBundleClass P.surface)) :=
    P.surface.free_picard_of_isRationalOver ℂ
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

variable [Q.fan.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S)]
  [LinearMap.IsPerfPair (letI := Q.complete.nonempty_cones
    (Chow.intersectionBilinForm ℂ Q.fan.algebraicRealization).prod
      (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ))))]

/-- The signed Picard homomorphism characterized by the marked pullbacks of
loop realizations gives the Casimir action on every independent X map. The
comparison uses the charge coordinates of the boundary orthogonal lattice. The
kernel of the Casimir action, read in the point-map group, lies in the unsigned subgroup. -/
theorem chargeKernelAction_eq_signedPicardRestriction
    (P : ChargeSeed E N) (hform : P.form = b.detDualEquiv.toLinearMap)
    (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (hker : E.matrix.mulVecLin.ker = P.charge.ker)
    (M : Point Centers[r] → MarkedSurface ℂ n H XTor[r])
    (hD : ∀ c, D[M c].IsEffectiveCartier)
    {c₀ : Point Centers[r]} (hc₀ : c₀.left (default : S) ∈ U₀[P])
    (p : letI := Q.complete.nonempty_cones
      letI := Q.prestable
      letI := Q.neZero
      ∀ (c : Point Centers[r]), c.left (default : S) ∈ U₀[P] → fiberAt[M,c])
    (hnodal : letI := Q.complete.nonempty_cones
      letI := Q.prestable
      letI := Q.neZero
      ∀ c hc, (p c hc).IsNodalContraction)
    [IsRationalOver ((M c₀).surface ↘ S)]
    (hnef : (classOf(hD c₀)).IsNef ℂ ((M c₀).surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ (M c₀).surface classOf(hD c₀) classOf(hD c₀) = 0)
    (hcan : letI : SmoothOfRelativeDimension 2 ((M c₀).surface ↘ S) := (M c₀).smooth
      classOf(hD c₀) = (LineBundleClass.mk (canonicalBundle ℂ (M c₀).surface 2))⁻¹)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD c₀)))
    (d : ZMod n → L) (hmark : ∀ c j, (M c).boundaryClass (hD c) j = d j)
    (hnodes :
      letI := Q.prestable
      letI := Q.neZero
      ∀ j, ∃ σ : Q.fan.cones, (Q.rayOrder j).toCone ≤ σ ∧
        (Q.rayOrder (j + 1)).toCone ≤ σ ∧
        (Q.fan.boundaryIdeal Q.complete.nonempty_cones).subschemeι
          ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme.dualGraphEdgeEquiv
            Q.marks (Q.cycle.edge j)).val =
          Q.fan.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (e : orth[H,d] ≃ₗ[ℤ] (Fan.rayChargeMap Q.rays).ker)
    (he : letI := Q.complete.nonempty_cones
      ∀ x, Q.inclusion (e.symm x).val =
        ((Fan.boundaryOrthogonalEquivChargeKernel Q.regular Q.rays
          ((Chow.intersectionBilinForm ℂ Q.fan.algebraicRealization).prod
            (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ))))).symm x).val)
    (ρ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup H d)
    (hρ : ∀ (w : Loops[E]) {C : Centers[r].left.PartialMap Centers[r].left}
      [IsDominant C.hom] [C.IsOver Centers[r].hom Centers[r].hom],
      letI : ((End.asHom w).xRationalMap ℂ).IsDominant :=
        Path.instIsDominantXRationalMap ℂ (End.asHom w)
      letI := Q.complete.nonempty_cones
      letI := Q.prestable
      letI := Q.neZero
      ∀ (R : GeometricRealization M M C ((End.asHom w).xRationalMap ℂ)),
        TargetModels[M,C] → ρ eval[w] = R.toSignedBoundaryIsometry d hD hmark) :
    ((LinearEquiv.autCongr (LinearEquiv.ofEq _ _ (congrArg LinearMap.ker hcharge))).toMonoidHom.comp
        (chargeKernelAction ℂ P hker) =
      (LinearEquiv.autCongr e).toMonoidHom.comp
        ((H.restrict orth[H,d]).isometryGroup.subtype.comp
          ((signedOrthogonalRestriction H d).comp ρ))) ∧
      (chargeKernelAction ℂ P hker).ker.unop ≤ (clusterModularGroupInclusion ℂ E).range := by
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  -- Use the same geometric realization for the charge action and its sign.
  have comparison (w : Loops[E]) :
      LinearEquiv.autCongr (LinearEquiv.ofEq _ _ (congrArg LinearMap.ker hcharge))
          (chargeKernelAction ℂ P hker (eval[w])) =
        LinearEquiv.autCongr e (signedOrthogonalRestriction H d (ρ eval[w])).val ∧
      sign H d (ρ eval[w]) = (-1 : ℤˣ) ^ (End.asHom w).inversionCount := by
    let word : Word E E := End.asHom w
    have hmodel (c : Point Centers[r]) (hc : c.left (default : S) ∈ U₀[P]) :
        Q.HasNodalModel c (M c) := by
      obtain ⟨l, Y, A, hA, f, hf⟩ := (hnodal c hc).exists_tower
      exact (Q.hasNodalModel_iff c (M c)).mpr ⟨p c hc, Y, l, A, f, hA, hf.symm⟩
    have htarget (v : Word E E) (x : CenterPoint (U := Centers[r]) (V := Centers[r]) Cw[v,P]) :
        (dst[Cw[v,P],x]).left (default : S) ∈ U₀[P] := by
      rw [Over.comp_left, Scheme.PartialMap.domainTarget_left, Scheme.Hom.comp_apply]
      exact v.centerPartialMap_opensRange_le_centerOpen_nil P hker
        ((Cw[v,P]).hom.mem_opensRange.mpr (Set.mem_range_self _))
    obtain ⟨R, hsign, _, htargets⟩ := exists_realize_signed_loop word P Q hform hcharge M
      (fun x ↦ hmodel _ (htarget Path.nil x)) (hmodel c₀ hc₀) hD hnef hsq hcan hprim d hmark
    let : IsDominant Cw[word,P].hom := inferInstance
    let : Cw[word,P].IsOver Centers[r].hom Centers[r].hom :=
      inferInstanceAs (Cw[word,P].IsOver
        (structureMap ℂ (Fin r → ℤ)) (structureMap ℂ (Fin r → ℤ)))
    have hmodels : TargetModels[M,Cw[word,P]] := by
      intro c
      obtain ⟨q, _⟩ := (Q.hasNodalModel_iff _ _).mp (htargets c)
      exact ⟨q⟩
    rw [hρ w (C := Cw[word,P]) R hmodels]
    refine ⟨?_, ?_⟩
    · refine chargeKernelAction_eq_signedOrthogonalRestriction Q.rayOrder
        (fun j ↦ (Q.cycle.component_apply j).symm.trans (Q.component_eq j))
        (fun j ↦ (Q.positive j).1) hnodes d hD hmark word R (word.centerPartialMap_hom (K := ℂ) P)
        P hcharge hker e he (U := {c : Point Centers[r] | c.left (default : S) ∈ U₀[P]})
        (fun c ↦ ⟨?_, htarget word c⟩)
        (fun c hc ↦ (hnodal c hc).genus_zero) (fun c hc ↦ ⟨p c hc⟩)
      rw [Set.mem_ofPred_eq, Over.comp_left, Scheme.PartialMap.domainSource_left,
        Scheme.Hom.comp_apply]
      exact word.centerOpen_le_centerOpen_nil ℂ P
        ((word.centerPartialMap_domain (K := ℂ) P) ▸ (c.left (default : S)).property)
    · exact (SignedBoundaryIsometryGroup.sign_apply H d _).trans
        ((congrArg Prod.snd (coe_toSignedBoundaryIsometry R d hD hmark)).trans hsign)
  refine ⟨?_, ?_⟩
  · apply MonoidHom.ext
    intro g
    obtain ⟨w, hw⟩ := signedClusterModularGroupMap_surjective ℂ E g.unop
    simpa only [hw, op_unop, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.subtype_apply] using (comparison w).1
  · -- A trivial restriction fixes the total boundary class, so the loop is even.
    intro g hg
    obtain ⟨w, rfl⟩ := signedClusterModularGroupMap_surjective ℂ E g
    have hg₁ := MonoidHom.mem_ker.mp (Subgroup.mem_unop.mp hg)
    have hrestrict : ρ eval[w] ∈ (signedOrthogonalRestriction H d).ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      apply (LinearEquiv.autCongr e).injective
      simpa only [hg₁, map_one, OneMemClass.coe_one] using (comparison w).1.symm
    have hsign := sign_eq_one_of_mem_ker_signedOrthogonalRestriction
      (M c₀) (hD c₀) hnef hsq hprim (funext (hmark c₀)) hrestrict
    rw [(comparison w).2, neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)] at hsign
    have hu := (mem_unsignedLoopPullbacks_iff_exists_even ℂ E _).mpr
      ⟨End.asHom w, hsign, rfl⟩
    refine ⟨op ⟨_, hu⟩, unop_injective (Subtype.ext ?_)⟩
    simp only [clusterModularGroupInclusion, MonoidHom.op_apply_apply, Function.comp_apply,
      unop_op, Subgroup.coe_inclusion, signedClusterModularGroupMap_unop_coe]
    rfl

end QPainleve.SignedClusterModularGroup.GeometricRealization
