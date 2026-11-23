/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
public import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Pivot

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.Geometry.Toric.Fan.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Mutation.Valuation
import QPainleve.Geometry.Toric.Fan.Picard.StrictTransform
import QPainleve.Geometry.Toric.Fan.Smooth
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Geometric Picard pullback for toric mutation

The pivot blowup isomorphism carries each strict ray divisor to the divisor of the
sheared ray. The comparison uses the generic points on the pivot-fiber complement.
Together with the exceptional pullback, this gives the geometric Picard action of the
elementary transformation in Gross, Hacking and Keel, [*Birational geometry of
cluster algebras*, §3.1 and the proof of Theorem 5.6](https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone Scheme
open Scheme.IdealSheafData TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass
open QPainleve.BlowupTower

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : ℂˣ)
  (hΦ : Φ.IsRegular)

local notation "v" => Ray.primitiveGenerator ρ
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hOpp) hΦ
local notation "r" => Φ.mutationFanRayEquiv b hv hp hOpp
local notation "I₀" => Ray.mutationSourceCenterIdeal b ρ c
local notation "I₁" => Ray.mutationTargetCenterIdeal b ρ hOpp c
local notation "G" => Ray.mutationBlowupIso b ρ hOpp c
local notation "h₀" => Φ.detCharacter_nonneg_or_nonpos b hv hp hOpp
local notation "h₁" => Φ.mutationDetCharacter_nonneg_or_nonpos b hv hp hOpp
local notation "U₀" => Φ.mutationComplement b h₀ (c : ℂ)
local notation "U₁" => mutationComplement Ψ b h₁ (c : ℂ)
local notation "eC" => Φ.mutationComplementIso b (c : ℂ) hv hp hOpp
local notation "P(" I ")" => QPainleve.BlowupTower.snoc QPainleve.BlowupTower.nil I

/-- The strict transform of each ray divisor pulls back to the strict transform of
the corresponding original ray divisor under the global pivot blowup isomorphism. -/
theorem Ray.comap_strictRayBoundary_mutationBlowupIso (u : Φ.Ray) :
    ((I₁).blowupMap ((Ψ).rayBoundaryIdeal (hΨ) ((r) u)).subschemeι).ker.comap (G).hom =
      ((I₀).blowupMap (Φ.rayBoundaryIdeal hΦ u).subschemeι).ker := by
  let x : (U₀).toScheme :=
    ⟨(Φ.rayBoundaryPoint hΦ u).val,
      Φ.rayBoundaryPoint_mem_mutationComplement b c hv h₀ hΦ u⟩
  let y := (eC).hom x
  let hI₀ := ρ.mutationSourceCenterIdeal_comap_complement b hOpp c
  let hI₁ := ρ.mutationTargetCenterIdeal_comap_complement b hOpp c
  let l₀ := (I₀).blowupLift (U₀).ι (hI₀.symm ▸ isEffectiveCartier_top _)
  let l₁ := (I₁).blowupLift (U₁).ι (hI₁.symm ▸ isEffectiveCartier_top _)
  have outsideExceptional {X U : Scheme} (I : X.IdealSheafData) (j : U ⟶ X)
      (h : I.comap j = ⊤) (z : U) :
      I.blowupLift j (h.symm ▸ isEffectiveCartier_top _) z ∉
        ((I.comap I.blowupToBase).support : Set I.blowup) := by
    have he := (I.comap I.blowupToBase).comap_eq_top_iff
      (I.blowupLift j (h.symm ▸ isEffectiveCartier_top _))
    rw [comap_blowupLift_exceptional] at he
    exact (Scheme.Hom.mem_preimage _).mp (by rw [he.mp h]; trivial)
  have hx : (I₀).blowupToBase (l₀ x) = (Φ.rayBoundaryPoint hΦ u).val := by
    rw [← Scheme.Hom.comp_apply, blowupLift_blowupToBase, Scheme.Opens.ι_apply]
  have hy : (I₁).blowupToBase (l₁ y) = ((Ψ).rayBoundaryPoint (hΨ) ((r) u)).val := by
    rw [← Scheme.Hom.comp_apply, blowupLift_blowupToBase]
    exact Φ.mutationComplementIso_hom_rayBoundaryPoint b c hv hp hOpp hΦ u
  have hl : (G).hom (l₀ x) = l₁ y := by
    rw [← Scheme.Hom.comp_apply, ρ.mutationComplementBlowupι_comp_mutationBlowupIso_hom,
      Scheme.Hom.comp_apply]
  rw [rayBoundaryIdeal_def, rayBoundaryIdeal_def, ← hx, ← hy,
    ker_blowupMap_vanishingIdeal_closure_singleton _ _ (outsideExceptional _ _ hI₀ x),
    ker_blowupMap_vanishingIdeal_closure_singleton _ _ (outsideExceptional _ _ hI₁ y),
    ← hl, comap_vanishingIdeal_closure_singleton_apply]

private theorem exists_strictRayClass_blowup_binomialCenter [Nonempty Φ.cones]
    [DecidableEq Φ.Ray] (u : Φ.Ray) (I : Φ.algebraicRealization.IdealSheafData)
    (hI : I = ρ.mutationSourceCenterIdeal b c) :
    ∃ h : (I.blowupMap (Φ.rayBoundaryIdeal hΦ u).subschemeι).ker.IsEffectiveCartier,
      (LineBundleClass.mk h.toInvertibleSheaf)⁻¹ =
        ((P(I)).picardHom (markedBoundaryMap hΦ (fun _ : Fin 1 ↦ ρ) (Pi.single u 1))).toMul := by
  let d := Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
  let J : Fin 1 → _ := fun _ ↦ ρ.internalCenter b c
  let m : Fin 1 → N →+ ℤ := fun _ ↦ (b.detDualEquiv v).toAddMonoidHom
  let T := alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι J
  let hT := isClosedPointTower_alongBoundary_binomialCenters d (fun _ ↦ ρ) m
    (fun _ ↦ b.detDualEquiv_self v) (fun _ ↦ ρ.surjective_detCharacter b)
    (fun _ ↦ c) J (fun _ ↦ ρ.internalCenter_val b c)
  have hdim : SmoothOfRelativeDimension 2 Φ.algebraicRealizationStructureMap :=
    d ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  have hS := hT.isEffectiveCartier_strictTransform Φ.algebraicRealizationStructureMap
    (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ u)
  have hmark := picardHom_markedBoundaryMap_single hΦ d (fun _ ↦ ρ) m
    (fun _ ↦ b.detDualEquiv_self v) (fun _ ↦ ρ.surjective_detCharacter b)
    (fun _ ↦ c) J (fun _ ↦ ρ.internalCenter_val b c) hT u
  rw [strictRayBoundaryClass_eq hΦ d T.2.toTower hT u hS] at hmark
  let D := (Φ.boundaryIdeal inferInstance).subschemeι
  let a := markedBoundaryMap hΦ (fun _ : Fin 1 ↦ ρ) (Pi.single u 1)
  let statement (A : Σ Y, WithBoundary D 1 Y) :=
    ∃ h : (A.2.toTower.strictTransform (Φ.rayBoundaryIdeal hΦ u)).IsEffectiveCartier,
      (LineBundleClass.mk h.toInvertibleSheaf)⁻¹ = (A.2.toTower.picardHom a).toMul
  let extend (A : Σ Y, WithBoundary D 0 Y) : Σ Y, WithBoundary D 1 Y :=
    ⟨_, A.2.snoc (J 0).val (J 0).property⟩
  have hT' : T = extend ⟨_, WithBoundary.nil D⟩ :=
    (alongBoundary_succ D J).trans (congrArg extend (alongBoundary_zero D _))
  have hclass : statement T := ⟨hS, congrArg Additive.toMul hmark.symm⟩
  obtain ⟨hS', hclass'⟩ := (congrArg statement hT').mp hclass
  let K := (J 0).val.map (WithBoundary.nil D).boundaryι
  have hmap : K = I := by
    dsimp only [K]
    rw [WithBoundary.boundaryι_nil, hI, Ray.mutationSourceCenterIdeal_eq]
    exact ρ.map_internalCenter_subschemeι b c
  clear hI
  subst I
  have hTower : (extend ⟨_, WithBoundary.nil D⟩).2.toTower = P(K) := by
    simp only [extend, WithBoundary.toTower_snoc, WithBoundary.toTower_nil, K]
  have hStrict : (extend ⟨_, WithBoundary.nil D⟩).2.toTower.strictTransform
      (Φ.rayBoundaryIdeal hΦ u) = (K.blowupMap (Φ.rayBoundaryIdeal hΦ u).subschemeι).ker := by
    rw [hTower, strictTransform_snoc, strictTransform_nil]
  refine ⟨hStrict ▸ hS', ?_⟩
  rw [← LineBundleClass.mk_toInvertibleSheaf_congr hS' _ hStrict, hclass', hTower]

section Marking

local notation "s" => fun _ : Fin 1 ↦ ρ
local notation "t" => Φ.mutationFanCenterRays b s 0 hOpp
local notation "M" => mutationPicardEquiv b s 0 hOpp hΦ
local notation "hΦ₀" => Nonempty.intro (Ray.toCone Φ ρ)
local notation "hΨ₀" => Nonempty.intro (Ray.toCone Ψ ((r) ρ))
local notation "P₀" => P(I₀)
local notation "P₁" => P(I₁)

private theorem pullback_mutationBlowupIso_markedBoundaryMap [DecidableEq Φ.Ray]
    [DecidableEq (Ψ).Ray] (u : Φ.Ray) :
    letI : Nonempty Φ.cones := hΦ₀
    letI : Nonempty (Ψ).cones := hΨ₀
    pullback (G).hom ((P₁).picardHom (markedBoundaryMap (hΨ) (t)
        (Pi.single ((r) u) 1))).toMul =
      ((P₀).picardHom (markedBoundaryMap hΦ s (Pi.single u 1))).toMul := by
  let : Nonempty Φ.cones := hΦ₀
  let : Nonempty (Ψ).cones := hΨ₀
  have hI₁ : (I₁) = ((t) 0).mutationSourceCenterIdeal b c⁻¹ := by
    rw [Ray.mutationTargetCenterIdeal_eq, Ray.mutationSourceCenterIdeal_eq,
      mutationFanCenterRays_self, mutationFanCenterRays_self]
  obtain ⟨hS, hclassS⟩ := exists_strictRayClass_blowup_binomialCenter b ρ c hΦ u (I₀) rfl
  obtain ⟨hT, hclassT⟩ := exists_strictRayClass_blowup_binomialCenter b ((t) 0) c⁻¹
    (hΨ) ((r) u) (I₁) hI₁
  have hsingle : (fun _ : Fin 1 ↦ (t) 0) = t := by
    funext j
    rw [Subsingleton.elim j 0]
  rw [hsingle] at hclassT
  have hRay := ρ.comap_strictRayBoundary_mutationBlowupIso b hOpp c hΦ u
  let hPull := hRay.symm ▸ hS
  rw [← hclassT, pullback_inv, hT.pullback_mk_toInvertibleSheaf hPull,
    LineBundleClass.mk_toInvertibleSheaf_congr hPull hS hRay, hclassS]

private theorem pullback_mutationBlowupIso_picardHom_pivot :
    pullback (G).hom ((P₁).picardHom (0, Pi.single (0 : Fin 1) 1)).toMul =
      ((P₀).picardHom ((M) (0, Pi.single (0 : Fin 1) 1))).toMul := by
  rw [mutationPicardEquiv_exceptional_pivot, picardHom_apply_single]
  have hE : (P₁).exceptionalClass 0 = (I₁).blowupExceptionalClass := by
    rw [← Fin.last_zero, exceptionalClass_snoc_last, blowupExceptionalClass_def]
  rw [hE, zpow_one, picardHom_snoc_apply_toMul, picardHom_nil, Fin.last_zero,
    Pi.neg_apply, Pi.single_eq_same, zpow_neg_one, ← div_eq_mul_inv]
  simpa only [blowupExceptionalClass_def] using
    ρ.pullback_blowupExceptionalClass_mutationBlowupIso b hOpp c hΦ

/-- In the Picard markings of the two global pivot blowups, geometric pullback is the
marked mutation equivalence on the entire Picard group. -/
theorem Ray.pullback_mutationBlowupIso_picardHom
    (a : Additive (LineBundleClass (Ψ).algebraicRealization) × (Fin 1 → ℤ)) :
    pullback (G).hom ((P₁).picardHom a).toMul = ((P₀).picardHom ((M) a)).toMul := by
  classical
  let : Nonempty Φ.cones := hΦ₀
  let : Nonempty (Ψ).cones := hΨ₀
  let f := (pullbackHom (G).hom).toAdditive.toIntLinearMap.comp ((P₁).picardHom)
  let g := ((P₀).picardHom).comp (M).toLinearMap
  have hD : f.comp (markedBoundaryMap (hΨ) (t)) = g.comp (markedBoundaryMap (hΨ) (t)) := by
    apply (Pi.basisFun ℤ (Ψ).Ray).ext
    intro u
    obtain ⟨u, rfl⟩ := (r).surjective u
    apply Additive.toMul.injective
    simp only [Pi.basisFun_apply, f, g, LinearMap.comp_apply, LinearEquiv.coe_coe,
      AddMonoidHom.coe_toIntLinearMap, MonoidHom.toAdditive_apply_apply, pullbackHom_apply,
      toMul_ofMul, mutationPicardEquiv_markedBoundaryMap, Pi.single_comp_equiv,
      Equiv.symm_apply_apply]
    exact pullback_mutationBlowupIso_markedBoundaryMap b ρ hOpp c hΦ u
  have hE : f.comp (LinearMap.inr ℤ _ _) = g.comp (LinearMap.inr ℤ _ _) := by
    apply (Pi.basisFun ℤ (Fin 1)).ext
    intro j
    rw [Subsingleton.elim j 0]
    apply Additive.toMul.injective
    simpa only [Pi.basisFun_apply, f, g, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.inr_apply, AddMonoidHom.coe_toIntLinearMap, MonoidHom.toAdditive_apply_apply,
      pullbackHom_apply, toMul_ofMul] using
      pullback_mutationBlowupIso_picardHom_pivot b ρ hOpp c hΦ
  -- Replace each total ray class by its strict class plus its exceptional contribution.
  obtain ⟨A, hA⟩ := (Ψ).rayDivisorToPicard_surjective (hΨ) a.1
  let z j := A ((t) j) + a.2 j
  have ha : markedBoundaryMap (hΨ) (t) A + (0, z) = a := by
    refine Prod.ext (by simpa only [markedBoundaryMap_apply, Prod.fst_add, add_zero] using hA) ?_
    funext j
    simp only [markedBoundaryMap_apply, Prod.snd_add, Pi.add_apply, z]
    exact neg_add_cancel_left (A ((t) j)) (a.2 j)
  have hfg : f a = g a := by
    rw [← ha, map_add, map_add]
    exact congrArg₂ (· + ·) (LinearMap.congr_fun hD A) (LinearMap.congr_fun hE z)
  simpa only [f, g, LinearMap.comp_apply, LinearEquiv.coe_coe, AddMonoidHom.coe_toIntLinearMap,
    MonoidHom.toAdditive_apply_apply, pullbackHom_apply, toMul_ofMul] using
    congrArg Additive.toMul hfg

end Marking

section Ordered

variable {n : ℕ} (s : Fin (1 + n) → Φ.Ray)

local notation "k" => Fin.castAdd n (0 : Fin 1)
local notation "p" => s (k)

local notation "oppositeMem" => hull ℝ {i (-Ray.primitiveGenerator (p))} ∈ Φ.cones
local notation "Ψₙ(" h ")" => Φ.mutationFan b (Ray.primitiveGenerator_ne_zero (p))
  (Ray.hull_primitiveGenerator_mem (p)) h
local notation "hΨₙ(" h ")" => Iff.mpr (Φ.isRegular_mutationFan_iff b
  (Ray.primitiveGenerator_ne_zero (p)) (Ray.hull_primitiveGenerator_mem (p)) h) hΦ
local notation "I₀ₙ" => Ray.mutationSourceCenterIdeal b (p) c
local notation "I₁ₙ(" h ")" => Ray.mutationTargetCenterIdeal b (p) h c
local notation "Gₙ(" h ")" => Ray.mutationBlowupIso b (p) h c
local notation "Mₙ(" h ")" => mutationPicardEquiv b s (k) h hΦ
local notation "M₁(" h ")" => mutationPicardEquiv b (fun _ : Fin 1 ↦ p) 0 h hΦ
local notation "P₀" => P(I₀ₙ)
local notation "P₁(" h ")" => P(I₁ₙ(h))

private theorem mutationPicardEquiv_pivot_split (hOppₙ : oppositeMem)
    (a : Additive (LineBundleClass (Ψₙ(hOppₙ)).algebraicRealization) × (Fin (1 + n) → ℤ)) :
    (((Mₙ(hOppₙ)) a).1, fun j : Fin 1 ↦ ((Mₙ(hOppₙ)) a).2 (j.castAdd n)) =
      (M₁(hOppₙ)) (a.1, fun j : Fin 1 ↦ a.2 (j.castAdd n)) ∧
    (fun j : Fin n ↦ ((Mₙ(hOppₙ)) a).2 (j.natAdd 1)) = fun j ↦ a.2 (j.natAdd 1) := by
  classical
  let : Nonempty (Ψₙ(hOppₙ)).cones := ⟨(Φ.mutationFanConeEquiv b (p).primitiveGenerator_ne_zero
    (p).hull_primitiveGenerator_mem hOppₙ (p).toCone)⟩
  obtain ⟨A, hA⟩ := (Ψₙ(hOppₙ)).rayDivisorToPicard_surjective (hΨₙ(hOppₙ)) a.1
  obtain ⟨_, z⟩ := a
  dsimp only at hA ⊢
  rw [← hA, mutationPicardEquiv_apply_rayDivisor, mutationPicardEquiv_apply_rayDivisor]
  constructor
  · refine Prod.ext rfl ?_
    funext j
    rw [Subsingleton.elim j 0]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same]
  · funext j
    have hj : j.natAdd 1 ≠ k := by
      intro he
      have hv' := congrArg Fin.val he
      simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_zero] at hv'
      omega
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero, sub_zero]

/-- The Picard change of marking for one toric mutation also describes every lift
through matching ordered towers after the pivot. Coordinates are ordered with
the selected center first in both models. -/
theorem pullback_mutationBlowupIso_lift_picardHom (hOppₙ : oppositeMem) {X Y : Scheme}
    {T : QPainleve.BlowupTower (I₀ₙ).blowup n X}
    {S : QPainleve.BlowupTower (I₁ₙ(hOppₙ)).blowup n Y}
    {e : X ≅ Y} (he : IsLift (Gₙ(hOppₙ)) T S e)
    (a : Additive (LineBundleClass (Ψₙ(hOppₙ)).algebraicRealization) × (Fin (1 + n) → ℤ)) :
    pullback e.hom (((P₁(hOppₙ)).append S).picardHom a).toMul =
      (((P₀).append T).picardHom ((Mₙ(hOppₙ)) a)).toMul := by
  have hsplit := mutationPicardEquiv_pivot_split b hΦ s hOppₙ a
  rw [picardHom_append, he.pullback_picardHom,
    Ray.pullback_mutationBlowupIso_picardHom b (p) hOppₙ c hΦ, ofMul_toMul]
  rw [picardHom_append]
  exact congrArg (fun z ↦ (T.picardHom z).toMul)
    (Prod.ext (congrArg (P₀).picardHom hsplit.1.symm) hsplit.2.symm)

end Ordered

end TauCeti.Toric.Fan
