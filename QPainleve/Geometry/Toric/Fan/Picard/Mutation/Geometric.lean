/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
public import QPainleve.Geometry.Toric.Fan.Mutation.Boundary
public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Pivot

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.Geometry.Toric.Fan.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Ruling
import QPainleve.Geometry.Toric.Fan.Picard.StrictTransform
import QPainleve.Geometry.Toric.BaseChange.Fan
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

variable (K : Type) [Field K] [PerfectField K]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : Kˣ)
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
local notation "P(" I ")" => QPainleve.BlowupTower.snoc QPainleve.BlowupTower.nil I

private theorem exists_strictRayClass_blowup_binomialCenter [Nonempty Φ.cones]
    [DecidableEq Φ.Ray] (u : Φ.Ray) (I : (Φ.finiteFanScheme K).IdealSheafData)
    (hI : I = ρ.mutationSourceCenterIdeal b c) :
    ∃ h : (I.blowupMap (Φ.rayDivisorIdeal K hΦ u).subschemeι).ker.IsEffectiveCartier,
      (LineBundleClass.mk h.toInvertibleSheaf)⁻¹ =
        ((P(I)).picardHom (markedBoundaryMap K hΦ (fun _ : Fin 1 ↦ ρ) (Pi.single u 1))).toMul := by
  let d := Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
  let J : Fin 1 → _ := fun _ ↦ ρ.internalCenter K b c
  let m : Fin 1 → N →+ ℤ := fun _ ↦ (b.detDualEquiv v).toAddMonoidHom
  let T := alongBoundary (Φ.toricBoundaryIdeal K inferInstance).subschemeι J
  let hT := isClosedPointTower_alongBoundary_binomialCenters K d (fun _ ↦ ρ) m
    (fun _ ↦ b.detDualEquiv_self v) (fun _ ↦ ρ.surjective_detCharacter b)
    (fun _ ↦ c) J (fun _ ↦ ρ.internalCenter_val K b c)
  have hdim : SmoothOfRelativeDimension 2 (Φ.finiteFanSchemeToSpec K) :=
    d ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ
  have hS := hT.isEffectiveCartier_strictTransform (Φ.finiteFanSchemeToSpec K)
    (Φ.isEffectiveCartier_rayDivisorIdeal K hΦ u)
  have hmark := picardHom_markedBoundaryMap_single K hΦ d (fun _ ↦ ρ) m
    (fun _ ↦ b.detDualEquiv_self v) (fun _ ↦ ρ.surjective_detCharacter b)
    (fun _ ↦ c) J (fun _ ↦ ρ.internalCenter_val K b c) hT u
  rw [strictRayBoundaryClass_eq K hΦ d T.2.toTower hT u hS] at hmark
  let D := (Φ.toricBoundaryIdeal K inferInstance).subschemeι
  let a := markedBoundaryMap K hΦ (fun _ : Fin 1 ↦ ρ) (Pi.single u 1)
  let statement (A : Σ Y, WithBoundary D 1 Y) :=
    ∃ h : (A.2.toTower.strictTransform (Φ.rayDivisorIdeal K hΦ u)).IsEffectiveCartier,
      (LineBundleClass.mk h.toInvertibleSheaf)⁻¹ = (A.2.toTower.picardHom a).toMul
  let extend (A : Σ Y, WithBoundary D 0 Y) : Σ Y, WithBoundary D 1 Y :=
    ⟨_, A.2.snoc (J 0).val (J 0).property⟩
  have hT' : T = extend ⟨_, WithBoundary.nil D⟩ :=
    (alongBoundary_succ D J).trans (congrArg extend (alongBoundary_zero D _))
  have hclass : statement T := ⟨hS, congrArg Additive.toMul hmark.symm⟩
  obtain ⟨hS', hclass'⟩ := (congrArg statement hT').mp hclass
  let center := (J 0).val.map (WithBoundary.nil D).boundaryι
  have hmap : center = I := by
    dsimp only [center]
    rw [WithBoundary.boundaryι_nil, hI, Ray.mutationSourceCenterIdeal_eq]
    exact ρ.map_internalCenter_subschemeι K b c
  clear hI
  subst I
  have hTower : (extend ⟨_, WithBoundary.nil D⟩).2.toTower = P(center) := by
    simp only [extend, WithBoundary.toTower_snoc, WithBoundary.toTower_nil, center]
  have hStrict : (extend ⟨_, WithBoundary.nil D⟩).2.toTower.strictTransform
      (Φ.rayDivisorIdeal K hΦ u) =
        (center.blowupMap (Φ.rayDivisorIdeal K hΦ u).subschemeι).ker := by
    rw [hTower, strictTransform_snoc, strictTransform_nil]
  refine ⟨hStrict ▸ hS', ?_⟩
  rw [← LineBundleClass.mk_toInvertibleSheaf_congr hS' _ hStrict, hclass', hTower]

section Marking

local notation "s" => fun _ : Fin 1 ↦ ρ
local notation "t" => Φ.mutationFanCenterRays b s 0 hOpp
local notation "M" => mutationPicardEquiv K b s 0 hOpp hΦ
local notation "hΦ₀" => Nonempty.intro (Ray.toCone Φ ρ)
local notation "hΨ₀" => Nonempty.intro (Ray.toCone Ψ ((r) ρ))
local notation "P₀" => P(I₀)
local notation "P₁" => P(I₁)

private theorem pullback_mutationBlowupIso_markedBoundaryMap [DecidableEq Φ.Ray]
    [DecidableEq (Ψ).Ray] (u : Φ.Ray) :
    letI : Nonempty Φ.cones := hΦ₀
    letI : Nonempty (Ψ).cones := hΨ₀
    pullback (G).hom ((P₁).picardHom (markedBoundaryMap K (hΨ) (t)
        (Pi.single ((r) u) 1))).toMul =
      ((P₀).picardHom (markedBoundaryMap K hΦ s (Pi.single u 1))).toMul := by
  let : Nonempty Φ.cones := hΦ₀
  let : Nonempty (Ψ).cones := hΨ₀
  have hI₁ : (I₁) = ((t) 0).mutationSourceCenterIdeal b c⁻¹ := by
    rw [Ray.mutationTargetCenterIdeal_eq, Ray.mutationSourceCenterIdeal_eq,
      mutationFanCenterRays_self, mutationFanCenterRays_self]
  obtain ⟨hS, hclassS⟩ := exists_strictRayClass_blowup_binomialCenter K b ρ c hΦ u (I₀) rfl
  obtain ⟨hT, hclassT⟩ := exists_strictRayClass_blowup_binomialCenter K b ((t) 0) c⁻¹
    (hΨ) ((r) u) (I₁) hI₁
  have hsingle : (fun _ : Fin 1 ↦ (t) 0) = t := by
    funext j
    rw [Subsingleton.elim j 0]
  rw [hsingle] at hclassT
  have hRay := ρ.comap_strictRayBoundary_mutationBlowupIso b hOpp c hΦ u
  let hPull := hRay.symm ▸ hS
  rw [← hclassT, pullback_inv, hT.pullback_mk_toInvertibleSheaf hPull,
    LineBundleClass.mk_toInvertibleSheaf_congr hPull hS hRay, hclassS]

omit [PerfectField K] in
private theorem pullback_mutationBlowupIso_picardHom_pivot :
    pullback (G).hom ((P₁).picardHom (0, Pi.single (0 : Fin 1) 1)).toMul =
      ((P₀).picardHom ((M) (0, Pi.single (0 : Fin 1) 1))).toMul := by
  rw [mutationPicardEquiv_exceptional_pivot, picardHom_apply_single]
  have hE : (P₁).exceptionalClass 0 = (I₁).blowupExceptionalClass := by
    rw [← Fin.last_zero, exceptionalClass_snoc_last, blowupExceptionalClass_def]
  rw [hE, zpow_one, picardHom_snoc_apply_toMul, picardHom_nil, Fin.last_zero,
    Pi.neg_apply, Pi.single_eq_same, zpow_neg_one, ← div_eq_mul_inv]
  simpa only [blowupExceptionalClass_def] using
    ρ.pullback_blowupExceptionalClass_mutationBlowupIso K b hOpp c hΦ

/-- In the Picard markings of the two global pivot blowups, geometric pullback is the
marked mutation equivalence on the entire Picard group. -/
theorem Ray.pullback_mutationBlowupIso_picardHom
    (a : Additive (LineBundleClass ((Ψ).finiteFanScheme K)) × (Fin 1 → ℤ)) :
    pullback (G).hom ((P₁).picardHom a).toMul = ((P₀).picardHom ((M) a)).toMul := by
  classical
  let : Nonempty Φ.cones := hΦ₀
  let : Nonempty (Ψ).cones := hΨ₀
  let f := (pullbackHom (G).hom).toAdditive.toIntLinearMap.comp ((P₁).picardHom)
  let g := ((P₀).picardHom).comp (M).toLinearMap
  have hD : f.comp (markedBoundaryMap K (hΨ) (t)) = g.comp (markedBoundaryMap K (hΨ) (t)) := by
    apply (Pi.basisFun ℤ (Ψ).Ray).ext
    intro u
    obtain ⟨u, rfl⟩ := (r).surjective u
    apply Additive.toMul.injective
    simp only [Pi.basisFun_apply, f, g, LinearMap.comp_apply, LinearEquiv.coe_coe,
      AddMonoidHom.coe_toIntLinearMap, MonoidHom.toAdditive_apply_apply, pullbackHom_apply,
      toMul_ofMul, mutationPicardEquiv_markedBoundaryMap, Pi.single_comp_equiv,
      Equiv.symm_apply_apply]
    exact pullback_mutationBlowupIso_markedBoundaryMap K b ρ hOpp c hΦ u
  have hE : f.comp (LinearMap.inr ℤ _ _) = g.comp (LinearMap.inr ℤ _ _) := by
    apply (Pi.basisFun ℤ (Fin 1)).ext
    intro j
    rw [Subsingleton.elim j 0]
    apply Additive.toMul.injective
    simpa only [Pi.basisFun_apply, f, g, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.inr_apply, AddMonoidHom.coe_toIntLinearMap, MonoidHom.toAdditive_apply_apply,
      pullbackHom_apply, toMul_ofMul] using
      pullback_mutationBlowupIso_picardHom_pivot K b ρ hOpp c hΦ
  -- Replace each total ray class by its strict class plus its exceptional contribution.
  obtain ⟨A, hA⟩ := (Ψ).rayChartDivisorToPicard_surjective K (hΨ) a.1
  let z j := A ((t) j) + a.2 j
  have ha : markedBoundaryMap K (hΨ) (t) A + (0, z) = a := by
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
local notation "I₀ₙ" => Ray.mutationSourceCenterIdeal b (p) c
local notation "I₁ₙ(" h ")" => Ray.mutationTargetCenterIdeal b (p) h c
local notation "Gₙ(" h ")" => Ray.mutationBlowupIso b (p) h c
local notation "Mₙ(" h ")" => mutationPicardEquiv K b s (k) h hΦ
local notation "P₀" => P(I₀ₙ)
local notation "P₁(" h ")" => P(I₁ₙ(h))

/-- The Picard change of marking for one toric mutation also describes every lift
through matching ordered towers after the pivot. Coordinates are ordered with
the selected center first in both models. -/
theorem pullback_mutationBlowupIso_lift_picardHom (hOppₙ : oppositeMem) {X Y : Scheme}
    {T : QPainleve.BlowupTower (I₀ₙ).blowup n X}
    {S : QPainleve.BlowupTower (I₁ₙ(hOppₙ)).blowup n Y}
    {e : X ≅ Y} (he : IsLift (Gₙ(hOppₙ)) T S e)
    (a : Additive (LineBundleClass ((Ψₙ(hOppₙ)).finiteFanScheme K)) × (Fin (1 + n) → ℤ)) :
    pullback e.hom (((P₁(hOppₙ)).append S).picardHom a).toMul =
      (((P₀).append T).picardHom ((Mₙ(hOppₙ)) a)).toMul := by
  obtain ⟨hpivot, hrest⟩ := mutationPicardEquiv_pivot_split K b s (k) hOppₙ hΦ a
  have hfirst (j : Fin 1) : j.castAdd n = k := by rw [Subsingleton.elim j 0]
  have hnext (j : Fin n) : j.natAdd 1 ≠ k := by
    simp [Fin.ext_iff]
  rw [picardHom_append, he.pullback_picardHom,
    Ray.pullback_mutationBlowupIso_picardHom K b (p) hOppₙ c hΦ, ofMul_toMul]
  rw [picardHom_append]
  exact congrArg (fun z ↦ (T.picardHom z).toMul)
    (Prod.ext (congrArg (P₀).picardHom (by simpa only [hfirst] using hpivot.symm))
      (funext fun j ↦ (hrest _ (hnext j)).symm))

end Ordered

section Ruling

open QPainleve

local notation "X" => (Φ.finiteFanScheme K)
local notation "X'" => Fan.finiteFanScheme K Ψ
local notation "q" => Ray.ofPrimitiveGenerator ρ.isPrimitiveGenerator.isPrimitive.neg hOpp
local notation "F" => mutationFiberClass K b ρ hΦ
local notation "F'" => mutationFiberClass K b (r ρ) hΨ

variable {n : ℕ} {Y : Scheme.{0}}
  (T : BlowupTower ((ρ.mutationSourceCenterIdeal b (c : Kˣ)).blowup) n Y)

local notation "k" => Fin.castAdd n (0 : Fin 1)
local notation "s" => (fun _ : Fin (1 + n) ↦ ρ)
local notation "R₁" => BlowupTower.transport T G
local notation "U₁" => BlowupTower.append (P(I₁)) (BlowupTower.Transport.tower (R₁))
local notation "A" => BlowupTower.append (P(I₀)) T

/-- The mutation lift transports a line class with ruling coordinates `(a, d)`
and ordered exceptional coefficients `x`. Use the pivot ray as section when
`onSection = true` and the opposite ray otherwise. The new ruling coordinates
are `(a + x k + if onSection then d else 0, d)`, where `k` is the first stage.
The new first exceptional coefficient is `-d - x k`, and the tail stays fixed. -/
theorem picardHom_transport_mutation (onSection : Bool) (a d : ℤ)
    (x : Fin (1 + n) → ℤ) :
    let : Nonempty Φ.cones := ⟨ρ.toCone⟩
    let : Nonempty (Ψ).cones := ⟨(r ρ).toCone⟩
    let : ∀ x : X, UniqueFactorizationMonoid ((X).presheaf.stalk x) :=
      Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := K) hΦ
    let : ∀ x : X', UniqueFactorizationMonoid ((X').presheaf.stalk x) :=
      (Ψ).uniqueFactorizationMonoid_stalk_finiteFanScheme (R := K) hΨ
    let τ := if onSection then ρ else q
    let S := Additive.ofMul (primeDivisorClass (Φ.rayBoundaryChartPoint (R := K) hΦ τ))
    let S' := Additive.ofMul (primeDivisorClass ((Ψ).rayBoundaryChartPoint (R := K) hΨ (r τ)))
    pullback (R₁).iso.inv ((A).picardHom (a • F + d • S, x)).toMul =
      ((U₁).picardHom ((a + x k + (if onSection then d else 0)) • F' + d • S',
        Function.update x k (-d - x k))).toMul := by
  intro h₀ h₁ huf₀ huf₁ τ S S'
  let := h₀
  let := h₁
  let := huf₀
  let := huf₁
  let w := ((a + x k + (if onSection then d else 0)) • F' + d • S',
        Function.update x k (-d - x k))
  have hw : (mutationPicardEquiv K b s k hOpp hΦ).symm (a • F + d • S, x) = w :=
    mutationPicardEquiv_symm_apply_ruling K b s k hOpp hΦ onSection a d x
  have h := pullback_mutationBlowupIso_lift_picardHom K b c hΦ s hOpp (T := T)
    (S := (R₁).tower) (e := (R₁).iso) (R₁).isLift w
  rw [← hw, LinearEquiv.apply_symm_apply, hw] at h
  rw [← h, pullback_comp, Iso.inv_hom_id, pullback_id]

end Ruling

end TauCeti.Toric.Fan
