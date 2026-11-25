/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.StrictTransform

import QPainleve.AlgebraicGeometry.CartierDivisor.WeightedClass
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial

/-!
# Weighted boundary classes on ordered internal blowups

An effective Cartier divisor on the strict toric boundary has toric Picard coordinates
given by its ray multiplicities. Its total exceptional coefficient at each labeled center
is the negative of the multiplicity of that center's ray. This describes the marking
for nonreduced divisors such as total transforms of nodal boundaries.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {r : ℕ}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin r → Φ.Ray) (c : Fin r → ℂˣ)

local notation "Y" => Sigma.fst (internalBlowupTower b s c)
local notation "U" => WithBoundary.toTower (Sigma.snd (internalBlowupTower b s c))
local notation "D" =>
  Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd (internalBlowupTower b s c)))
local notation "f" => QPainleve.BlowupTower.toBase U ≫ Fan.algebraicRealizationStructureMap Φ

local instance : IsNoetherian Y := (U).isNoetherian

/-- The multiplicity of a Cartier divisor at the strict boundary prime indexed by a ray. -/
def internalBlowupRayMultiplicity {I : Scheme.IdealSheafData Y} (hI : I.IsEffectiveCartier)
    (ρ : Φ.Ray) : ℤ :=
  letI := isIntegral_internalBlowupTower b s c hΦ
  WeilDivisor.coeff hI.toCartierDivisor.toWeilDivisor
    ((D).boundaryPrimeEmbedding (internalBlowupBoundaryPrimeEquiv hΦ b s c ρ))

/-- The ray multiplicity is the Weil coefficient at the corresponding strict prime. -/
theorem internalBlowupRayMultiplicity_eq_coeff {I : Scheme.IdealSheafData Y}
    (hI : I.IsEffectiveCartier) (ρ : Φ.Ray) :
    letI := isIntegral_internalBlowupTower b s c hΦ
    internalBlowupRayMultiplicity hΦ b s c hI ρ =
      WeilDivisor.coeff hI.toCartierDivisor.toWeilDivisor
        ((D).boundaryPrimeEmbedding (internalBlowupBoundaryPrimeEquiv hΦ b s c ρ)) := (rfl)

/-- The ray multiplicity is positive exactly on the support of the divisor. -/
@[simp]
theorem internalBlowupRayMultiplicity_pos_iff {I : Scheme.IdealSheafData Y}
    (hI : I.IsEffectiveCartier) (ρ : Φ.Ray) :
    0 < internalBlowupRayMultiplicity hΦ b s c hI ρ ↔
      (internalBlowupBoundaryPrimeEquiv hΦ b s c ρ).val ∈ I.support := by
  let := isIntegral_internalBlowupTower b s c hΦ
  let : SmoothOfRelativeDimension 2 f := smoothOfRelativeDimension_internalBlowupTower b s c hΦ
  let := (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let : IsNormalScheme Y := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let p := (D).boundaryPrimeEmbedding (internalBlowupBoundaryPrimeEquiv hΦ b s c ρ)
  have hn : 0 ≤ WeilDivisor.coeff hI.toCartierDivisor.toWeilDivisor p :=
    (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
      hI.isEffective_toCartierDivisor p
  rw [internalBlowupRayMultiplicity_eq_coeff, lt_iff_le_and_ne, and_iff_right hn, ne_comm]
  simpa only [p, not_not, coe_boundaryPrimeEmbedding] using
    not_congr (hI.coeff_toWeilDivisor_eq_zero_iff p)

/-- The Picard marking of an effective Cartier divisor supported on the strict toric
boundary is the marked boundary map applied to its ray multiplicities. -/
theorem internalBlowupPicardMarking_symm_ofMul_inv_toInvertibleSheaf
    {I : Scheme.IdealSheafData Y} (hI : I.IsEffectiveCartier) (hs : I.support ≤ (D).support) :
    (internalBlowupPicardMarking b s c hΦ).symm
      (Additive.ofMul (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹) =
      markedBoundaryMap hΦ s (internalBlowupRayMultiplicity hΦ b s c hI) := by
  classical
  let := isIntegral_internalBlowupTower b s c hΦ
  let : SmoothOfRelativeDimension 2 f := smoothOfRelativeDimension_internalBlowupTower b s c hΦ
  let := (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := Fintype.ofFinite Φ.Ray
  let e := internalBlowupBoundaryPrimeEquiv hΦ b s c
  let p := e.toEmbedding.trans (D).boundaryPrimeEmbedding
  have hp (x : CodimensionOnePoint Y) (hx : x.val ∈ I.support) : x ∈ Set.range p := by
    rw [Function.Embedding.coe_trans, Equiv.coe_toEmbedding, e.surjective.range_comp,
      (D).range_boundaryPrimeEmbedding]
    exact hs hx
  let w := internalBlowupRayMultiplicity hΦ b s c hI
  have hw : ∑ ρ, w ρ • Pi.single ρ 1 = internalBlowupRayMultiplicity hΦ b s c hI := by
    simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using
      (Pi.basisFun ℤ Φ.Ray).sum_repr w
  have hclass (ρ : Φ.Ray) :
      (U).picardHom (markedBoundaryMap hΦ s (Pi.single ρ 1)) =
        Additive.ofMul (primeDivisorClass (p ρ)) := by
    rw [picardHom_markedBoundaryMap_single_eq_primeDivisorClass hΦ b s c]
    congr 2
    exact Subtype.ext (coe_boundaryPrimeEmbedding _ _).symm
  apply (internalBlowupPicardMarking b s c hΦ).injective
  rw [LinearEquiv.apply_symm_apply, internalBlowupPicardMarking_apply, ← hw, map_sum, map_sum,
    hI.ofMul_inv_toInvertibleSheaf_eq_sum_coeff_zsmul_primeDivisorClass p hp]
  simp only [map_zsmul, hclass, w, internalBlowupRayMultiplicity, p, e,
    Function.Embedding.trans_apply, Equiv.toEmbedding_apply]

end TauCeti.Toric.Fan
