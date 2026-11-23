/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Order
public import TauCeti.AlgebraicGeometry.IdealSheaf.Colon
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Removing the exact exceptional multiplicity

Dividing the total transform by the exceptional power of its exact stalk order
removes the exceptional component. The result applies to any ideal sheaf of
finite stalk order, including the ideals of divisors and of moving linear systems.
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} (p : X)

local notation "P" => Scheme.Hom.ker (Scheme.fromSpecResidueField X p)
local notation "π" => blowupToBase P
local notation "E" => comap P π
local notation "hE" => isEffectiveCartier_comap_blowupToBase P

/-- The total transform factors as the residual ideal and the exceptional power of
the natural-number value of the stalk order at the center. -/
theorem comap_blowupToBase_eq_colon_mul_exceptional_pow
    (hp : IsClosed ({p} : Set X)) (J : X.IdealSheafData) :
    J.comap π = (J.comap π).colon (E ^ (J.stalkOrder p).toNat) * E ^ (J.stalkOrder p).toNat := by
  apply eq_colon_mul _ _ (TauCeti.isEffectiveCartier_pow hE _).locallyPrincipal
  rw [← comap_pow]
  exact comap_mono π ((natCast_le_stalkOrder_iff_le_pow_ker_fromSpecResidueField p J hp _).mp
    (ENat.natCast_toNat_le_self _))

variable [IsIntegral X] [IsLocallyNoetherian X] [IsRegularLocalRing (X.presheaf.stalk p)]
  (hp : IsClosed ({p} : Set X)) (hdim : ringKrullDim (X.presheaf.stalk p) = 2)

include hp hdim

/-- After dividing a total-transform ideal by the exceptional power of its exact stalk order,
the generic point of the exceptional divisor lies outside the residual support. -/
theorem notMem_support_colon_exceptional_of_mem_exceptional (J : X.IdealSheafData)
    (m : ℕ) (hm : J.stalkOrder p = m) (x : CodimensionOnePoint (P).blowup)
    (hx : (x : (P).blowup) ∈ (E).support) :
    (x : (P).blowup) ∉ (((J.comap π).colon (E ^ m)).support) := by
  have : IsLocallyNoetherian (P).blowup := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsIntegral (E).subscheme :=
    (isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hdim).isIntegral_subscheme
  have hxη := ((hE).mem_support_iff_eq_subschemeι_genericPoint x.property).mp hx
  let R := (J.comap π).colon (E ^ m)
  intro hxR
  have hsub : ((E).support : Set (P).blowup) ⊆ (R.support : Set (P).blowup) := by
    rw [(E).support_eq_closure_subschemeι_genericPoint, ← hxη]
    exact R.support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hxR)
  have hRE : R ≤ E := by
    have hclosed : (E).support ≤ R.support := fun _ hx ↦ hsub hx
    have hs := le_support_iff_le_vanishingIdeal.mp hclosed
    rw [vanishingIdeal_support, ((E).isReduced_subscheme_iff_radical_eq).mp inferInstance] at hs
    exact hs
  have hle' : J.comap π ≤ E ^ (m + 1) := calc
    J.comap π = R * E ^ m := by
      simpa only [R, hm, ENat.toNat_natCast] using comap_blowupToBase_eq_colon_mul_exceptional_pow
        p hp J
    _ ≤ E * E ^ m := fun U ↦ by
      simpa only [ideal_mul, Pi.mul_apply] using Ideal.mul_mono (hRE U) le_rfl
    _ = E ^ (m + 1) := (pow_succ' _ _).symm
  have h := (comap_blowupToBase_le_exceptional_pow_iff p hp hdim J (m + 1)).mp hle'
  rw [hm, ENat.natCast_le_natCast] at h
  omega

end AlgebraicGeometry.Scheme.IdealSheafData
