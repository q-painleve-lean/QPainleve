/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
public import QPainleve.AlgebraicGeometry.Blowup.Order
public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Multiplicity
public import TauCeti.AlgebraicGeometry.IdealSheaf.Colon
import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Integral
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
import TauCeti.AlgebraicGeometry.Morphisms.Dominant

/-!
# Residual and strict transforms of Cartier divisors

On the blowup of a regular closed point of local dimension two, subtracting an exceptional
power bounded by the original stalk order gives an effective Cartier divisor. Its Picard
class is the total transform minus that multiple of the exceptional class. Removing the
exceptional power at the exact stalk order gives the scheme-theoretic strict transform.
-/

public section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

section Residual

variable (p : X)

local notation "P" => Scheme.Hom.ker (Scheme.fromSpecResidueField X p)
local notation "π" => blowupToBase P
local notation "E" => comap P π
local notation "hE" => isEffectiveCartier_comap_blowupToBase P

variable [IsIntegral X] [IsNoetherian X] [IsRegularLocalRing (X.presheaf.stalk p)]
  (hp : IsClosed ({p} : Set X)) (hdim : ringKrullDim (X.presheaf.stalk p) = 2)

include hp hdim

private theorem isEffectiveCartier_comap_pointBlowup {D : X.IdealSheafData}
    (hD : D.IsEffectiveCartier) : (D.comap π).IsEffectiveCartier := by
  have : IsIntegral (P).blowup := X.isIntegral_pointBlowup p (by
    intro h
    have hg : coheight (genericPoint X) = 0 :=
      coheight_eq_zero.mpr TauCeti.AlgebraicGeometry.Scheme.isMax_genericPoint
    rw [ringKrullDim_stalk_eq_coheight, h, hg] at hdim
    norm_num at hdim)
  have : Surjective π := by
    rw [X.ker_fromSpecResidueField_eq_vanishingIdeal]
    exact surjective_blowupToBase_point hp hdim
  refine hD.comap_of_isIntegral π ?_
  rw [(π).genericPoint_eq_of_isDominant]
  exact hD.genericPoint_notMem_support

/-- Removing an exceptional power up to the order of an effective Cartier divisor gives an
effective Cartier divisor on the point blowup. -/
theorem IsEffectiveCartier.comap_blowupToBase_colon_exceptional_pow {D : X.IdealSheafData}
    (hD : D.IsEffectiveCartier) (n : ℕ) (hn : (n : ℕ∞) ≤ D.stalkOrder p) :
    ((D.comap π).colon (E ^ n)).IsEffectiveCartier :=
  (isEffectiveCartier_comap_pointBlowup p hp hdim hD).colon
    (TauCeti.isEffectiveCartier_pow hE n).locallyPrincipal
    ((comap_blowupToBase_le_exceptional_pow_iff p hp hdim _ n).mpr hn)

/-- The residual divisor has class `π*D - nE` in the Picard group. -/
theorem IsEffectiveCartier.toLineBundleClass_comap_blowupToBase_colon_exceptional_pow
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    (n : ℕ) (hn : (n : ℕ∞) ≤ D.stalkOrder p) :
    let hR := IsEffectiveCartier.comap_blowupToBase_colon_exceptional_pow p hp hdim hD n hn
    (LineBundleClass.mk hR.toInvertibleSheaf)⁻¹ =
      LineBundleClass.pullback π (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ *
        (LineBundleClass.mk (hE).toInvertibleSheaf) ^ n := by
  dsimp only
  let hF := TauCeti.isEffectiveCartier_pow hE n
  let hT := isEffectiveCartier_comap_pointBlowup p hp hdim hD
  let hR := IsEffectiveCartier.comap_blowupToBase_colon_exceptional_pow p hp hdim hD n hn
  have heq := eq_colon_mul (D.comap π) (E ^ n) hF.locallyPrincipal
    ((comap_blowupToBase_le_exceptional_pow_iff p hp hdim _ n).mpr hn)
  have hprod := LineBundleClass.mk_toInvertibleSheaf_congr hT
    (TauCeti.isEffectiveCartier_mul hR hF) heq
  rw [LineBundleClass.pullback_inv, hD.pullback_mk_toInvertibleSheaf hT, hprod,
    LineBundleClass.mk_toInvertibleSheaf_mul hR hF, LineBundleClass.mk_toInvertibleSheaf_pow hE n]
  rw [mul_inv_rev, mul_comm _ (LineBundleClass.mk hR.toInvertibleSheaf)⁻¹,
    mul_assoc, inv_mul_cancel, mul_one]

end Residual

section StrictTransform

variable {p : X} {D : X.IdealSheafData}

local notation "Iₚ" => vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)
local notation "π" => blowupToBase Iₚ
local notation "E" => comap Iₚ π
local notation "S" => Scheme.Hom.ker (blowupMap Iₚ D.subschemeι)
local notation "m" => ENat.toNat (D.stalkOrder p)

variable [IsIntegral X] [IsNoetherian X] [IsRegularLocalRing (X.presheaf.stalk p)]

/-- Removing the exceptional power of the exact multiplicity from the total transform
gives the ideal of the scheme-theoretic strict transform. -/
theorem IsEffectiveCartier.comap_blowupToBase_colon_eq_strictTransform
    (hD : D.IsEffectiveCartier) (hp : IsClosed ({p} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) :
    (D.comap π).colon (E ^ m) = S := by
  have h : D.comap π = S * E ^ m :=
    hD.totalTransform_eq_strictTransform_mul_pow_closedPoint hp hdim
  rw [h, (TauCeti.isEffectiveCartier_pow
    (Iₚ).isEffectiveCartier_comap_blowupToBase m).mul_colon_cancel_right]

/-- The scheme-theoretic strict transform of an effective Cartier divisor under a
regular closed point blowup of local dimension two is effective Cartier. -/
theorem IsEffectiveCartier.strictTransform_pointBlowup
    (hD : D.IsEffectiveCartier) (hp : IsClosed ({p} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) : (S).IsEffectiveCartier := by
  have hP : (Iₚ) = (X.fromSpecResidueField p).ker :=
    (X.ker_fromSpecResidueField_eq_vanishingIdeal p).symm
  rw [← hD.comap_blowupToBase_colon_eq_strictTransform hp hdim, hP]
  exact IsEffectiveCartier.comap_blowupToBase_colon_exceptional_pow p hp hdim hD m
    (ENat.natCast_toNat_le_self _)

/-- The class of the strict transform is `π*D - mE`, where `m` is the stalk
order of `D` at the center. -/
theorem IsEffectiveCartier.toLineBundleClass_strictTransform_pointBlowup
    (hD : D.IsEffectiveCartier) (hp : IsClosed ({p} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) :
    let hS := hD.strictTransform_pointBlowup hp hdim
    (LineBundleClass.mk hS.toInvertibleSheaf)⁻¹ =
      LineBundleClass.pullback π (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ *
        (Iₚ).blowupExceptionalClass⁻¹ ^ m := by
  intro hS
  have hP : (Iₚ) = (X.fromSpecResidueField p).ker :=
    (X.ker_fromSpecResidueField_eq_vanishingIdeal p).symm
  rw [blowupExceptionalClass_def, inv_inv]
  suffices ∃ hR : ((D.comap π).colon (E ^ m)).IsEffectiveCartier,
      (LineBundleClass.mk hR.toInvertibleSheaf)⁻¹ =
        LineBundleClass.pullback π (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ *
          (LineBundleClass.mk (Iₚ).isEffectiveCartier_comap_blowupToBase.toInvertibleSheaf) ^ m by
    obtain ⟨hR, hclass⟩ := this
    rw [← LineBundleClass.mk_toInvertibleSheaf_congr hR hS
      (hD.comap_blowupToBase_colon_eq_strictTransform hp hdim)]
    exact hclass
  rw [hP]
  let hn := ENat.natCast_toNat_le_self (D.stalkOrder p)
  exact ⟨IsEffectiveCartier.comap_blowupToBase_colon_exceptional_pow p hp hdim hD m hn,
    IsEffectiveCartier.toLineBundleClass_comap_blowupToBase_colon_exceptional_pow
      p hp hdim hD m hn⟩

end StrictTransform

end AlgebraicGeometry.Scheme.IdealSheafData
