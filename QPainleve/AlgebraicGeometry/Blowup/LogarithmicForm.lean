/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Integral
public import QPainleve.AlgebraicGeometry.Blowup.Smooth
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Divisor
public import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
public import TauCeti.AlgebraicGeometry.Blowup.Pullback
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Cartier.Inverse
import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Multiplicity
import QPainleve.AlgebraicGeometry.Blowup.Ramification
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Multiplicity
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction
import TauCeti.Topology.KrullDimension.Basic

/-!
# Logarithmic top forms on point blowups

For a top form whose divisor is `-D`, the pullback to a point blowup has
divisor `-Dˢᵗʳ + (1 - m)E`, where `m` is the stalk order of the effective
Cartier divisor `D` at the center. This computes the order along the
exceptional curve for centers away from the poles, at smooth points of the poles,
and at nodes. The computation uses the actual cotangent pullback and the
scheme-theoretic strict transform.

See [Hacking, *583C Lecture notes*, Proposition 7.2][Hacking] for the
local Jacobian calculation.

[Hacking]: https://paulhacking.github.io/surfaces.pdf#page=36
-/

public section

open CategoryTheory Order TopologicalSpace TauCeti TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme (CartierDivisor)

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

universe u

variable {X : Scheme.{u}} {p : X} [IsIntegral X] {D : X.IdealSheafData}

local notation "Iₚ" => vanishingIdeal (Closeds.mk (closure (singleton p)) isClosed_closure)
local notation "B" => blowup Iₚ
local notation "π" => blowupToBase Iₚ
local notation "E" => Scheme.IdealSheafData.comap Iₚ π
local notation "hE" => isEffectiveCartier_comap_blowupToBase Iₚ

private theorem exists_strictTransform_cartierDivisor [IsLocallyNoetherian X]
    [IsIntegral B] [IsRegularLocalRing (X.presheaf.stalk p)]
    (hD : D.IsEffectiveCartier) (hp : IsClosed ({p} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (hT : (D.comap π).IsEffectiveCartier) :
    ∃ hS : ((Iₚ).blowupMap D.subschemeι).ker.IsEffectiveCartier,
      hT.toCartierDivisor = hS.toCartierDivisor + (D.stalkOrder p).toNat • (hE).toCartierDivisor ∧
        ∀ x : CodimensionOnePoint B, (x : B) ∈ (E).support →
          (x : B) ∉ ((Iₚ).blowupMap D.subschemeι).ker.support := by
  let m := (D.stalkOrder p).toNat
  let hF := TauCeti.isEffectiveCartier_pow hE m
  have hsplit : D.comap π = ((Iₚ).blowupMap D.subschemeι).ker * E ^ m :=
    hD.totalTransform_eq_strictTransform_mul_pow_closedPoint hp hdim
  have hle : D.comap π ≤ E ^ m := by
    rw [hsplit]
    exact fun U ↦ by
      simpa only [ideal_mul, Pi.mul_apply] using Ideal.mul_le_right
  have hres : (D.comap π).colon (E ^ m) = ((Iₚ).blowupMap D.subschemeι).ker := by
    rw [hsplit, hF.mul_colon_cancel_right]
  let hS : ((Iₚ).blowupMap D.subschemeι).ker.IsEffectiveCartier :=
    Eq.mp (congrArg Scheme.IdealSheafData.IsEffectiveCartier hres)
      (hT.colon hF.locallyPrincipal hle)
  refine ⟨hS, ?_, ?_⟩
  · calc
      _ = (TauCeti.isEffectiveCartier_mul hS hF).toCartierDivisor :=
        (hT.toCartierDivisor_eq_iff _).mpr hsplit
      _ = _ := by rw [toCartierDivisor_mul hS hF, toCartierDivisor_pow]
  · have hm : (m : ℕ∞) = D.stalkOrder p := by
      refine ENat.natCast_toNat ?_
      rw [D.stalkOrder_def, ne_eq, Ideal.localOrder_eq_top_iff_eq_bot]
      exact hD.stalkIdeal_ne_bot p
    rw [← hres, ← X.ker_fromSpecResidueField_eq_vanishingIdeal]
    exact fun x hx ↦ notMem_support_colon_exceptional_of_mem_exceptional p hp hdim D m hm.symm x hx

variable (k : Type u) [Field k] [PerfectField k] [X.Over (Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

/-- For a top form with divisor `-D`, pullback to the blowup of a smooth surface at a
closed point has divisor `-Dˢᵗʳ + (1 - m)E`, where `m` is the stalk order of `D`.
In particular its order at the generic point of the exceptional divisor is `1 - m`. -/
theorem pullbackTopFormDivisor_pointBlowup (hD : D.IsEffectiveCartier)
    (e : hD.toInvertibleSheaf ≅ QPainleve.canonicalBundle k X 2)
    (hp : IsClosed ({p} : Set X)) :
    let : (B).Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    letI : (π).IsOver (Spec (.of k)) := ⟨rfl⟩
    letI : SmoothOfRelativeDimension 2 (B ↘ Spec (.of k)) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
    letI : Smooth (B ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
    letI : IsIntegral B := isIntegral_blowup_closed_point (X ↘ Spec (.of k)) hp
    letI : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian (B ↘ Spec (.of k))
    ∃ (hT : (D.comap π).IsEffectiveCartier)
      (hRam : (ramificationIdealSheaf k π).IsEffectiveCartier)
      (hS : ((Iₚ).blowupMap D.subschemeι).ker.IsEffectiveCartier),
      let C := QPainleve.pullbackTopFormDivisor k π 2 hD e hT hRam
      let a := 1 - ((D.stalkOrder p).toNat : ℤ)
      C = a • (hE).toCartierDivisor - hS.toCartierDivisor ∧
        ∀ x : CodimensionOnePoint B, (x : B) ∈ (E).support → C.orderAt x = a := by
  let : (B).Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
  have : (π).IsOver (Spec (.of k)) := ⟨rfl⟩
  have : SmoothOfRelativeDimension 2 (B ↘ Spec (.of k)) :=
    smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
  have : Smooth (B ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral B := isIntegral_blowup_closed_point (X ↘ Spec (.of k)) hp
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  have : IsNoetherian B := isNoetherian_of_finiteType π
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  have hdim : ringKrullDim (X.presheaf.stalk p) = 2 :=
    ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (X ↘ Spec (.of k)) 2).mp
      inferInstance).2 p hp
  have : Surjective π := surjective_blowupToBase_point hp hdim
  let hT := hD.comap_of_isIntegral π (by
    rw [(π).genericPoint_eq_of_isDominant]
    exact hD.genericPoint_notMem_support)
  have hRamEq := ramificationIdealSheaf_blowup_of_smoothSurface k hp
  let hRam : (ramificationIdealSheaf k π).IsEffectiveCartier := hRamEq.symm ▸ hE
  have hRamDiv := (hRam.toCartierDivisor_eq_iff hE).mpr hRamEq
  obtain ⟨hS, hsplit, hSnot⟩ := exists_strictTransform_cartierDivisor hD hp hdim hT
  have hdiv : QPainleve.pullbackTopFormDivisor k π 2 hD e hT hRam =
      (1 - ((D.stalkOrder p).toNat : ℤ)) • (hE).toCartierDivisor - hS.toCartierDivisor := by
    rw [QPainleve.pullbackTopFormDivisor_eq_ramification_sub, hRamDiv, hsplit, sub_smul, one_smul]
    simp only [natCast_zsmul]
    abel
  refine ⟨hT, hRam, hS, hdiv, fun x hx ↦ ?_⟩
  have : IsRegular B := IsRegular.of_smooth (B ↘ Spec (.of k))
  have hdimB := topologicalKrullDim_eq_of_smoothOfRelativeDimension (B ↘ Spec (.of k)) (n := 2)
  have (y : B) : UniqueFactorizationMonoid ((B).presheaf.stalk y) :=
    IsRegular.uniqueFactorizationMonoid_stalk y
      (WithBot.coe_le_coe.mp ((coheight_le_topologicalKrullDim y).trans hdimB.le))
  have : IsIntegral (E).subscheme := by
    rw [← X.ker_fromSpecResidueField_eq_vanishingIdeal]
    exact (isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hdim)
      |>.isIntegral_subscheme
  have hx' := ((hE).mem_support_iff_eq_subschemeι_genericPoint x.property).mp hx
  have hvan : vanishingIdeal ⟨closure {(x : B)}, isClosed_closure⟩ = E := by
    rw [hx', (E).vanishingIdeal_closure_subschemeι_genericPoint]
  have hOne : (hE).toCartierDivisor.toWeilDivisor = WeilDivisor.ofPoint x := by
    have hP := isEffectiveCartier_vanishingIdeal_closure_singleton x.property
    rw [((hE).toCartierDivisor_eq_iff hP).mpr hvan.symm]
    exact toWeilDivisor_toCartierDivisor_vanishingIdeal_closure_singleton x
  have hZero := (hS.coeff_toWeilDivisor_eq_zero_iff x).mpr (hSnot x hx)
  rw [← CartierDivisor.coeff_toWeilDivisor, hdiv, ← CartierDivisor.toWeilDivisorHom_apply]
  simp only [map_sub, map_zsmul, CartierDivisor.toWeilDivisorHom_apply, hOne, WeilDivisor.coeff_sub,
    WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_self, hZero, mul_one, sub_zero]

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
