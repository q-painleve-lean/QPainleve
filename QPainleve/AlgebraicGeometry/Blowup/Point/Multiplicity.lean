/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.Support
public import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Multiplicity
import QPainleve.AlgebraicGeometry.CartierDivisor.Multiplicity
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Blowup.Restriction

/-!
# Weil coefficients of total transforms of point blowups

The Weil coefficient at the exceptional prime of a point blowup is the
order of the original effective Cartier divisor at the center. On each strict transform,
the coefficient agrees with the coefficient of its image prime.
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  {D : X.IdealSheafData} {p : X} [IsRegularLocalRing (X.presheaf.stalk p)]

variable {I : X.IdealSheafData}
local notation "π" => blowupToBase I
local notation "E" => Scheme.IdealSheafData.comap I π

/-- At the exceptional prime over a regular closed point of dimension two, the total
transform has Weil coefficient equal to the order of the original Cartier ideal. -/
theorem coeff_toWeilDivisor_comap_pointBlowup_of_over_center
    (hD : D.IsEffectiveCartier) (hp : IsClosed ({p} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (hI : I = (X.fromSpecResidueField p).ker)
    [IsIntegral I.blowup] [IsNoetherian I.blowup]
    (hT : (D.comap π).IsEffectiveCartier)
    (q : CodimensionOnePoint I.blowup) [IsDiscreteValuationRing (I.blowup.presheaf.stalk
      (q : I.blowup))] (hq : π q = p) :
    WeilDivisor.coeff hT.toCartierDivisor.toWeilDivisor q = (D.stalkOrder p).toNat := by
  have hE : (E).IsExceptionalCurveOfFirstKind := hI ▸
    isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hdim
  have : IsIntegral (E).subscheme := hE.isIntegral_subscheme
  have hqE : (q : I.blowup) ∈ (E).support := by
    rw [support_comap, ← SetLike.mem_coe, Closeds.coe_preimage, Set.mem_preimage, hq, hI,
      Scheme.support_ker_fromSpecResidueField_of_isClosed hp]
    exact Set.mem_singleton p
  have hV := hI.trans (X.ker_fromSpecResidueField_eq_vanishingIdeal p)
  clear hI
  subst I
  obtain ⟨hS, hsum, hoff⟩ := hD.exists_strictTransform_cartierDivisor hp hdim hT
  have hzero := (hS.coeff_toWeilDivisor_eq_zero_iff q).mpr (hoff q hqE)
  have hone := hE.isEffectiveCartier.coeff_toWeilDivisor_eq_one_of_isReduced q hqE
  rw [hsum, ← Scheme.CartierDivisor.toWeilDivisorHom_apply, map_add, map_nsmul,
    Scheme.CartierDivisor.toWeilDivisorHom_apply, Scheme.CartierDivisor.toWeilDivisorHom_apply,
    WeilDivisor.coeff_add, WeilDivisor.coeff_nsmul, hzero, hone, zero_add, mul_one]

/-- A strict-transform prime in a point blowup has the same Weil coefficient
as its image prime. -/
theorem coeff_toWeilDivisor_comap_pointBlowup_of_strict
    {Z : Scheme.{u}} [IsIntegral Z] [IsNoetherian Z] [IsNormalScheme Z]
    {P : Z.IdealSheafData} (hP : P.IsEffectiveCartier)
    {x : Z} (hx : IsClosed ({x} : Set Z)) (hx₁ : Order.coheight x ≠ 1)
    {I : Z.IdealSheafData} (hI : I = (Z.fromSpecResidueField x).ker)
    [IsIntegral I.blowup] [IsNoetherian I.blowup] [IsNormalScheme I.blowup]
    (hQ : (P.comap I.blowupToBase).IsEffectiveCartier)
    (q : CodimensionOnePoint I.blowup) (r : CodimensionOnePoint Z)
    (hr : I.blowupToBase q = r) :
    WeilDivisor.coeff hQ.toCartierDivisor.toWeilDivisor q =
      WeilDivisor.coeff hP.toCartierDivisor.toWeilDivisor r := by
  have hne : (r : Z) ≠ x := fun h ↦ hx₁ (h ▸ r.property)
  have hr' : (r : Z) ∈ I.support.compl := by
    rw [← SetLike.mem_coe, Closeds.coe_compl, hI,
      Scheme.support_ker_fromSpecResidueField_of_isClosed hx, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    exact hne
  have hIso := I.blowupToBase.le_isoLocus_iff.mpr
    I.isIso_blowupToBase_restrict_compl_support hr'
  have hIso' : I.blowupToBase q ∈ I.blowupToBase.isoLocus := hr.symm ▸ hIso
  rw [hP.coeff_toWeilDivisor_comap_of_mem_isoLocus _ hQ q hIso']
  exact congrArg (WeilDivisor.coeff hP.toCartierDivisor.toWeilDivisor) (Subtype.ext hr)

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
