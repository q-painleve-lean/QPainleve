/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.ConnectingWord

import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber

/-!
# Prescribed actions of words between marked toric presentations

At a source center in a word's noncollision open, its fixed-center X evaluation
determines its marked Picard pullback and action on ordered boundary branches.
The word can reach a different target center from the one in the prescribed
isomorphism. The comparison uses
`FiberRealization.marked_actions_eq_of_compOfDefined`, with both target models
supplied by the target presentation.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Module Quiver
open QPainleve.CharacterTorus QPainleve.Cluster TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

open MarkedSurface (surfaceIso boundaryIso)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "boundaryClassOf[" M "]" =>
  (LineBundleClass.mk
    (IsEffectiveCartier.toInvertibleSheaf (MarkedSurface.isEffectiveCartier_boundaryIdeal M)))⁻¹
local notation "Cw[" w "," P "]" => Path.centerPartialMap ℂ w P
local notation "Cnil[" P "]" => Path.centerPartialMap ℂ Path.nil P
local notation "src(" C "," c ")" =>
  c ≫ Scheme.PartialMap.domainSource (X := Centers[_]) (Y := Centers[_]) C
local notation "dst(" C "," c ")" =>
  c ≫ Scheme.PartialMap.domainTarget (X := Centers[_]) (Y := Centers[_]) C

variable {N₀ V₀ N₁ V₁ : Type} [AddCommGroup N₀] [AddCommGroup V₀] [Module ℝ V₀]
  [AddCommGroup N₁] [AddCommGroup V₁] [Module ℝ V₁]
  {i₀ : N₀ →+ V₀} {i₁ : N₁ →+ V₁} {b₀ : Basis (Fin 2) ℤ N₀} {b₁ : Basis (Fin 2) ℤ N₁}
  {r n : ℕ} [NeZero n] {L₀ L₁ γ₀ γ₁ : Type} [AddCommGroup L₀] [AddCommGroup L₁]
  {H₀ : LinearMap.BilinForm ℤ L₀} {H₁ : LinearMap.BilinForm ℤ L₁}
  {B E : SkewExchangeMatrix (Fin r)}
  {M₀ : Point Centers[r] → MarkedSurface ℂ n H₀ XTor[r]}
  {M₁ : Point Centers[r] → MarkedSurface ℂ n H₁ XTor[r]}

/-- A word with the same fixed-center X evaluation as a specified isomorphism
of fibers of two marked toric presentations realizes the isomorphism's full
Picard pullback and ordered boundary action. The source center must lie in
the word's noncollision open. The actual branch sign of the specified
isomorphism is the inversion parity, including for cycles of length one or two. -/
theorem exists_realize_signed_word_with_pair_iso_action
    (w : Word B E) (P₀ : ChargeSeed B N₀) (P₁ : ChargeSeed E N₁)
    (Q₀ : CompleteToricPresentation i₀ b₀ r L₀ γ₀)
    (Q₁ : CompleteToricPresentation i₁ b₁ r L₁ γ₁)
    (hform₀ : P₀.form = b₀.detDualEquiv.toLinearMap)
    (hcharge₀ : P₀.charge = Fan.rayChargeMap Q₀.rays)
    (hform₁ : P₁.form = b₁.detDualEquiv.toLinearMap)
    (hcharge₁ : P₁.charge = Fan.rayChargeMap Q₁.rays)
    (models₀ : ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P₀],
      Q₀.HasNodalModel (dst(Cnil[P₀],c)) (M₀ (dst(Cnil[P₀],c))))
    (models₁ : ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P₁],
      Q₁.HasNodalModel (dst(Cnil[P₁],c)) (M₁ (dst(Cnil[P₁],c))))
    {c₀ c₁ : Point Centers[r]} (hm₁ : Q₁.HasNodalModel c₁ (M₁ c₁))
    (hnef₀ : boundaryClassOf[M₀ c₀].IsNef ℂ ((M₀ c₀).surface ↘ S))
    (hsq₀ : Chow.classIntersectionNumber ℂ (M₀ c₀).surface
      boundaryClassOf[M₀ c₀] boundaryClassOf[M₀ c₀] = 0)
    (hprim₀ : IsPrimitive (Additive.ofMul boundaryClassOf[M₀ c₀]))
    (d₀ : ZMod n → L₀) (d₁ : ZMod n → L₁)
    (hmark₀ : ∀ c j, (M₀ c).boundaryClass (M₀ c).isEffectiveCartier_boundaryIdeal j = d₀ j)
    (hmark₁ : ∀ c j, (M₁ c).boundaryClass (M₁ c).isEffectiveCartier_boundaryIdeal j = d₁ j)
    (hcenter : c₀.left (default : S) ∈ w.centerOpen ℂ P₀)
    (e : (M₀ c₀).pair ≅ (M₁ c₁).pair)
    (heval : letI : IsIntegral (M₀ c₀).surface := (M₀ c₀).integral
      ∃ h, (M₀ c₀).evaluation.compOfDefined (w.xRationalMap ℂ) h =
        (surfaceIso e).hom.toRationalMap.comp (M₁ c₁).evaluation) :
    ∃ R : GeometricRealization M₀ M₁ Cw[w,P₀] (w.xRationalMap ℂ),
      (∀ a, (M₀ c₀).picardMarking (R.picard a) =
        Additive.ofMul
          (LineBundleClass.pullback (surfaceIso e).hom ((M₁ c₁).picardMarking a).toMul)) ∧
      (letI : PrestableFamily ((M₀ c₀).boundary ↘ S) := (M₀ c₀).prestable
       letI : PrestableFamily ((M₁ c₁).boundary ↘ S) := (M₁ c₁).prestable
       let act := (boundaryIso e).boundaryCycleAction (M₀ c₀).cycle (M₁ c₁).cycle
       act = R.boundaryAction ∧ cycleOrientationSign act = (-1 : ℤˣ) ^ w.inversionCount) ∧
      ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cw[w,P₀],
        Q₁.HasNodalModel (dst(Cw[w,P₀],c)) (M₁ (dst(Cw[w,P₀],c))) := by
  obtain ⟨hD₁, hnef₁, hsq₁⟩ := MarkedSurface.exists_nef_square_zero_boundary_of_pairIso
    e (M₀ c₀).isEffectiveCartier_boundaryIdeal hnef₀ hsq₀
  have hpull := MarkedSurface.pullback_boundaryLineBundleClass e.symm
  have hprim₁ : IsPrimitive (Additive.ofMul boundaryClassOf[M₁ c₁]) := by
    let f : Additive (LineBundleClass (M₀ c₀).surface) ≃ₗ[ℤ]
        Additive (LineBundleClass (M₁ c₁).surface) :=
      (LineBundleClass.pullbackEquiv (surfaceIso e.symm)).toAdditive.toIntLinearEquiv
    have hf : f (Additive.ofMul boundaryClassOf[M₀ c₀]) =
        Additive.ofMul boundaryClassOf[M₁ c₁] := by
      simpa only [f, AddEquiv.coe_toIntLinearEquiv, MulEquiv.toAdditive_apply_apply,
        LineBundleClass.pullbackEquiv_apply, toMul_ofMul] using congrArg Additive.ofMul hpull
    rw [← hf]
    exact f.isPrimitive_iff.mpr hprim₀
  obtain ⟨R, hsign, -, hmodels⟩ := exists_realize_signed_word_to_presentation w P₀ P₁ Q₀ Q₁
    hform₀ hcharge₀ hform₁ hcharge₁ M₀ M₁ models₀ models₁ hm₁
    (fun c ↦ (M₀ c).isEffectiveCartier_boundaryIdeal)
    (fun c ↦ (M₁ c).isEffectiveCartier_boundaryIdeal)
    hnef₀ hnef₁ hsq₀ hsq₁ hprim₀ hprim₁ d₀ d₁ hmark₀ hmark₁
  have hmem : c₀.left (default : S) ∈ Cw[w,P₀].domain := by
    rwa [Path.centerPartialMap_domain]
  obtain ⟨c, hc⟩ := (Cw[w,P₀].exists_section_comp_domainSource_eq_iff
    (Y := Centers[r]) c₀ (default : S)).mpr hmem
  have hindex := hm₁.chargeIndex_ne_zero hD₁ hnef₁ hsq₁ hprim₁
  let := Q₁.complete.nonempty_cones
  let := Q₁.prestable
  let := Q₁.neZero
  obtain ⟨p⟩ := (hmodels c).nonempty_contractedToricFiber
  obtain ⟨q⟩ := hm₁.nonempty_contractedToricFiber
  subst c₀
  let : IsIntegral (M₀ (src(Cw[w,P₀],c))).surface := (M₀ (src(Cw[w,P₀],c))).integral
  obtain ⟨hpic, hb⟩ := (R.fiber c).marked_actions_eq_of_compOfDefined
    p q e Q₁.complete (Q₁.inclusion_injective hm₁) hindex heval
  have hsign' := (congrArg cycleOrientationSign hb).trans (R.orientation_def.symm.trans hsign)
  exact ⟨R, hpic, ⟨hb, hsign'⟩, hmodels⟩

end QPainleve.SignedClusterModularGroup.GeometricRealization
