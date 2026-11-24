/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform
public import QPainleve.Geometry.Toric.Fan.Boundary.Component
public import QPainleve.Geometry.Toric.Fan.Boundary.Prime
public import QPainleve.Geometry.Toric.Fan.Picard.BoundaryQuotient
public import QPainleve.Geometry.Toric.Fan.Smooth

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Boundary.StrictTransform
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Picard classes of the strict boundary in an internal toric blowup tower

The strict transform of a ray component has its original toric divisor class and an
exceptional coefficient of `-1` for each center on that ray. This identifies the
Picard quotient by the actual strict-transform boundary classes with the cokernel of
the dual charge map. The centers are ordered and may repeat, in which case the
associated blowups use the successive strict transforms of the boundary.

The boundary marking is the calculation used in the proof of Gross, Hacking and Keel,
*Birational geometry of cluster algebras*, Theorem 5.5. The comparison uses
`boundaryQuotientEquivDualChargeCokernel` for charges of arbitrary rank.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]

local notation "D" => Φ.boundaryIdeal inferInstance

section Marking

variable {n : ℕ} (hΦ : Φ.IsRegular) (hdim : Module.finrank ℤ N = 2)
  (s : Fin n → Φ.Ray) (m : Fin n → N →+ ℤ)
  (hm : ∀ j, m j (s j).primitiveGenerator = 0) (hprim : ∀ j, Function.Surjective (m j))
  (c : Fin n → ℂˣ)

local notation "b" => subschemeι D
local notation "f" => Φ.algebraicRealizationStructureMap
local notation "Pic" Y => Additive (LineBundleClass Y)
local notation "C" j:arg => Ray.binomialCenterOnBoundary (s j) hdim (hm j) (hprim j) (c j)
local notation "p" j:arg => (C j) (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ))

omit [Nonempty Φ.cones] in
include hΦ hdim in
private theorem smoothOfRelativeDimension_two : SmoothOfRelativeDimension 2 f :=
  hdim ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ

/-- The Picard class of the actual scheme-theoretic strict transform of a ray boundary divisor
in a closed-point tower over the regular toric surface. -/
def strictRayBoundaryClass {Y : Scheme} (T : BlowupTower Φ.algebraicRealization n Y)
    (hT : IsClosedPointTower Φ.algebraicRealization T) (ρ : Φ.Ray) : Pic Y :=
  let := smoothOfRelativeDimension_two hΦ hdim
  Additive.ofMul (LineBundleClass.mk (hT.isEffectiveCartier_strictTransform f
    (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ)).toInvertibleSheaf)⁻¹

/-- The strict boundary class is the inverse of the class of its Cartier ideal. -/
theorem strictRayBoundaryClass_eq {Y : Scheme} (T : BlowupTower Φ.algebraicRealization n Y)
    (hT : IsClosedPointTower Φ.algebraicRealization T) (ρ : Φ.Ray)
    (hD : (T.strictTransform (Φ.rayBoundaryIdeal hΦ ρ)).IsEffectiveCartier) :
    strictRayBoundaryClass hΦ hdim T hT ρ =
      Additive.ofMul (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ := (rfl)

variable (J : Fin n → {I : (Φ.boundaryIdeal inferInstance).subscheme.IdealSheafData //
  I.IsEffectiveCartier})
  (hJ : ∀ j, (J j).val = ((s j).binomialCenterOnBoundary hdim (hm j) (hprim j) (c j)).ker)

local notation "tower" => alongBoundary b J
local notation "T" => WithBoundary.toTower (Sigma.snd tower)

variable (hT : IsClosedPointTower Φ.algebraicRealization
  (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι J).2.toTower)

include hJ in
private theorem strictTransformCoefficients_rayBoundaryIdeal [DecidableEq Φ.Ray] (ρ : Φ.Ray) :
    (hT).strictTransformCoefficients (Φ.rayBoundaryIdeal hΦ ρ) =
      fun j ↦ if s j = ρ then -1 else 0 := by
  let : ∀ j : Fin n, Decidable (p j ∈ Set.range (ρ.boundaryComponentι hΦ)) :=
    fun _ ↦ Classical.propDecidable _
  let := smoothOfRelativeDimension_two hΦ hdim
  obtain h := strictTransformCoefficients_alongBoundary b (ρ.boundaryComponentι hΦ) f
    J (fun j ↦ p j)
    (fun j ↦ by
      have hsingle : Set.range (C j) = {p j} :=
        Set.range_eq_singleton fun q ↦ congrArg (C j) (Subsingleton.elim q _)
      rw [← hsingle]
      exact (C j).isClosedEmbedding.isClosed_range)
    (fun j ↦ (hJ j).trans (C j).ker_eq_ker_fromSpecResidueField)
    (fun j ↦ by
      rw [hJ j]
      exact (s j).isEffectiveCartier_comap_ker_binomialCenterOnBoundary hΦ hdim
        (hm j) (hprim j) (c j) ρ)
    (fun j ↦ (s j).isRegularLocalRing_stalk_of_boundaryComponentι_eq_binomialCenter hΦ hdim
      (hm j) (hprim j) (c j) ρ)
    (by simpa only [Ray.boundaryComponentι_subschemeι, ker_subschemeι] using
      Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ)
    (hT)
  simp only [Ray.boundaryComponentι_subschemeι, ker_subschemeι] at h
  refine h.trans ?_
  funext j
  have hmem := (s j).binomialCenterOnBoundary_mem_range_boundaryComponentι_iff hΦ hdim
    (hm j) (hprim j) (c j) ρ
  by_cases hs : s j = ρ
  · simp only [ite_eq_left hs,
      ite_eq_left (hmem.mpr hs)]
  · simp only [ite_eq_right hs,
      ite_eq_right (hmem.not.mpr hs)]

include hJ in
/-- The coordinate vector of a marked boundary generator maps to the strict transform of its
ray component, even if several centers on that ray coincide on the initial toric surface. -/
theorem picardHom_markedBoundaryMap_single [DecidableEq Φ.Ray] (ρ : Φ.Ray) :
    (T).picardHom (markedBoundaryMap hΦ s (Pi.single ρ 1)) =
      strictRayBoundaryClass hΦ hdim (T) (hT) ρ := by
  let := smoothOfRelativeDimension_two hΦ hdim
  have := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have h := (hT).picardMarking_strictTransform f (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ)
  rw [strictTransformCoefficients_rayBoundaryIdeal hΦ hdim s m hm hprim c J hJ hT ρ] at h
  have hbase : LineBundleClass.primeDivisorClass (Φ.rayBoundaryPoint hΦ ρ) =
      (LineBundleClass.mk (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ).toInvertibleSheaf)⁻¹ := by
    rw [LineBundleClass.primeDivisorClass_def, LineBundleClass.mk_toInvertibleSheaf_congr _ _
      (Φ.rayBoundaryIdeal_def hΦ ρ).symm]
  rw [strictRayBoundaryClass_eq hΦ hdim (T) (hT) ρ
    ((hT).isEffectiveCartier_strictTransform f (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ))]
  simpa only [picardMarking_apply, markedBoundaryMap_apply,
    rayDivisorToPicard_single, one_zsmul, Pi.single_apply, apply_ite, neg_zero, hbase]
    using h

include hJ in
/-- The ordered Picard marking sends the marked boundary span to the span of the actual
strict-transform ray classes. -/
theorem map_range_markedBoundaryMap_picardHom :
    (markedBoundaryMap hΦ s).range.map (T).picardHom =
      Submodule.span ℤ (Set.range (strictRayBoundaryClass hΦ hdim (T) (hT))) := by
  classical
  rw [range_markedBoundaryMap_eq_span, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext ρ
  simpa only [Function.comp_apply, markedBoundaryMap_apply, Pi.single_apply, apply_ite,
    neg_zero] using picardHom_markedBoundaryMap_single hΦ hdim s m hm hprim c J hJ hT ρ

include hJ in
/-- In the surface obtained by blowing up the ordered binomial centers, the Picard group
modulo the strict-transform ray classes is the cokernel of the dual of the charge map.
The charges may have any rank. -/
def binomialBoundaryQuotientEquivDualChargeCokernel :
    ((Pic (Sigma.fst tower)) ⧸ Submodule.span ℤ
      (Set.range (strictRayBoundaryClass hΦ hdim (T) (hT)))) ≃ₗ[ℤ]
      (Module.Dual ℤ (Fin n → ℤ) ⧸ (rayChargeMap s).dualMap.range) := by
  letI := smoothOfRelativeDimension_two hΦ hdim
  let e := (T).picardMarking (hT) f
  have he : e.toLinearMap = (T).picardHom :=
    LinearMap.ext fun a ↦ picardMarking_apply (T) (hT) f a
  have hspan := map_range_markedBoundaryMap_picardHom hΦ hdim s m hm hprim c J hJ hT
  exact (Submodule.Quotient.equiv _ _ e (he.symm ▸ hspan)).symm.trans
    (boundaryQuotientEquivDualChargeCokernel hΦ s)

/-- The inverse cokernel comparison sends a dual functional to the corresponding class
supported in the total exceptional coordinates. -/
@[simp]
theorem binomialBoundaryQuotientEquivDualChargeCokernel_symm_apply_mk
    (φ : Module.Dual ℤ (Fin n → ℤ)) :
    (binomialBoundaryQuotientEquivDualChargeCokernel hΦ hdim s m hm hprim c J hJ hT).symm
      (Submodule.Quotient.mk φ) =
      Submodule.Quotient.mk ((T).picardHom (0, fun j ↦ φ (Pi.single j 1))) := by
  simp only [binomialBoundaryQuotientEquivDualChargeCokernel, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, boundaryQuotientEquivDualChargeCokernel_symm_apply_mk,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe, picardMarking_apply]

end Marking

section OrderedModel

variable {n : ℕ} (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

open TopologicalSpace LineBundleClass

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Z" => Φ.algebraicRealization
local notation "d₂" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "m" => (fun j ↦ LinearMap.toAddMonoidHom
  (b.detDualEquiv (Ray.primitiveGenerator (s j))))
local notation "hm" => (fun j ↦ b.detDualEquiv_self (Ray.primitiveGenerator (s j)))
local notation "hprim" => (fun j ↦ Ray.surjective_detCharacter (s j) b)
local notation "Model" => (Σ Y, WithBoundary (subschemeι (Φ.boundaryIdeal inferInstance)) n Y)
local notation "model" c => internalBlowupTower b s c
local notation "U" c => WithBoundary.toTower (Sigma.snd (model c))
local notation "hU" c => isClosedPointTower_internalBlowupTower b s c
local notation "fZ" => (Φ.algebraicRealization ↘ S)
local notation "prime(" x ")" => (Subtype.mk (Subtype.val x)
  (And.right (mem_boundaryPrimes.mp (Subtype.property x))) : CodimensionOnePoint _)
local notation "cl" ρ:arg => markedBoundaryMap hΦ s (Pi.single ρ 1)

/-- In the ordered Picard marking the actual boundary prime over a ray has the
fixed strict ray class. -/
theorem picardHom_markedBoundaryMap_single_eq_primeDivisorClass [DecidableEq Φ.Ray]
    (c : Fin n → ℂˣ) (ρ : Φ.Ray) :
    let : IsIntegral (model c).1 := isIntegral_internalBlowupTower b s c hΦ
    let : IsNoetherian (model c).1 := (U c).isNoetherian
    let : SmoothOfRelativeDimension 2 fZ :=
      d₂ ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : SmoothOfRelativeDimension 2 ((U c).toBase ≫ fZ) :=
      (hU c).smoothOfRelativeDimension fZ
    let := ((U c).toBase ≫ fZ).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (U c).picardHom (cl ρ) =
      Additive.ofMul (primeDivisorClass (prime(internalBlowupBoundaryPrimeEquiv hΦ b s c ρ))) := by
  intro _ _ _ _ _
  let j := ρ.boundaryComponentι hΦ ≫ (model c).2.boundaryι
  have : IsIntegral (Φ.rayBoundaryIdeal hΦ ρ).subscheme := by
    rw [rayBoundaryIdeal_def]
    exact isIntegral_subscheme_vanishingIdeal isIrreducible_singleton.closure
  have hI := ker_boundaryComponentι_internalBlowupTower b s c hΦ ρ
  have hs := range_rayComponent_internalBlowupBoundaryPrimeEquiv hΦ b s c ρ
  let x := (internalBlowupBoundaryPrimeEquiv hΦ b s c ρ).val
  have hker : j.ker = vanishingIdeal ⟨closure {x}, isClosed_closure⟩ := by
    rw [j.ker_eq_vanishingIdeal_support]
    congr 1
    exact SetLike.coe_injective ((j.support_ker.trans
      j.isClosedEmbedding.isClosed_range.closure_eq).trans hs)
  have heff := (hU c).isEffectiveCartier_strictTransform fZ
    (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ)
  let Marked (M : Model) := ∀ hM : IsClosedPointTower Z M.2.toTower,
    M.2.toTower.picardHom (cl ρ) = strictRayBoundaryClass hΦ d₂ _ hM ρ
  have hmark : Marked (model c) := by
    rw [internalBlowupTower_eq_alongBoundary]
    intro hM
    exact picardHom_markedBoundaryMap_single hΦ d₂ s m hm hprim c _
      (fun j ↦ (s j).internalCenter_val b (c j)) hM ρ
  rw [hmark (hU c),
    strictRayBoundaryClass_eq _ _ _ _ _ heff, primeDivisorClass_def,
    mk_toInvertibleSheaf_congr _ _ (hI.symm.trans hker)]

end OrderedModel

end TauCeti.Toric.Fan
