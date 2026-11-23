/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Canonical
public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Residual
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Canonical and boundary classes under point blowups

The scheme-theoretic strict transform of a Cartier divisor is the residual divisor
obtained by removing the exceptional power at the exact multiplicity. Consequently
the logarithmic canonical class changes by `(1 - multiplicity) E`. At a center on an
anticanonical divisor, adjoining `(multiplicity - 1) E` to the strict transform gives
an effective anticanonical divisor.

The computation uses the point-blowup canonical class and strict-transform formulas
(Hacking, *583C Lecture notes*, Propositions 7.2 and 7.3).
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {p : X} {D : X.IdealSheafData}

local notation "P" => vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)
local notation "π" => blowupToBase P
local notation "E" => comap P π
local notation "S" => Scheme.Hom.ker (blowupMap P D.subschemeι)
local notation "m" => ENat.toNat (D.stalkOrder p)

variable (k : Type u) [Field k] [PerfectField k] [IsIntegral X] [IsNoetherian X]
  [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "K(" Y ")" => LineBundleClass.mk (QPainleve.canonicalBundle k Y 2)

/-- The logarithmic canonical class of a smooth surface with Cartier divisor changes
under a point blowup by `(1 - m)E` when the new boundary is the strict transform.
The formula includes centers away from the divisor, where `m = 0`. -/
theorem IsEffectiveCartier.logCanonicalClass_strictTransform_pointBlowup
    (hD : D.IsEffectiveCartier) (hp : IsClosed ({p} : Set X)) :
    letI : (P).blowup.Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    letI : SmoothOfRelativeDimension 2 ((P).blowup ↘ Spec (.of k)) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
    ∃ hS : (S).IsEffectiveCartier,
      K((P).blowup) * (LineBundleClass.mk hS.toInvertibleSheaf)⁻¹ =
        LineBundleClass.pullback π (K(X) * (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹) *
          (P).blowupExceptionalClass ^ (1 - (m : ℤ)) := by
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
    (X ↘ Spec (.of k)) 2).mp inferInstance).2 p hp
  refine ⟨hD.strictTransform_pointBlowup hp hdim, ?_⟩
  rw [mk_canonicalBundle_pointBlowup k hp, hD.toLineBundleClass_strictTransform_pointBlowup hp hdim,
    LineBundleClass.pullback_mul, zpow_sub,
    zpow_one, zpow_natCast, inv_pow]
  ac_rfl

/-- For an anticanonical effective Cartier divisor and a closed point on its support,
the inverse image minus one exceptional divisor is effective anticanonical. Its
actual ideal is the product of the strict-transform ideal and the exceptional ideal
to the power `m - 1`. -/
theorem IsEffectiveCartier.exists_anticanonical_strictTransform_mul_exceptional_pow
    (hD : D.IsEffectiveCartier) (hp : IsClosed ({p} : Set X)) (hpD : p ∈ D.support)
    (hanti : LineBundleClass.mk hD.toInvertibleSheaf = K(X)) :
    letI : (P).blowup.Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    letI : SmoothOfRelativeDimension 2 ((P).blowup ↘ Spec (.of k)) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
    let D' := S * E ^ (m - 1)
    ∃ hD' : D'.IsEffectiveCartier,
      LineBundleClass.mk hD'.toInvertibleSheaf = K((P).blowup) ∧ D' * E = D.comap π := by
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
    (X ↘ Spec (.of k)) 2).mp inferInstance).2 p hp
  have hmt : D.stalkOrder p ≠ ⊤ := by
    rw [D.stalkOrder_def, ne_eq, Ideal.localOrder_eq_top_iff_eq_bot]
    exact hD.stalkIdeal_ne_bot p
  have hm : 1 ≤ m :=
    ENat.toNat_le_toNat ((D.one_le_stalkOrder_iff p).mpr hpD) hmt
  obtain ⟨hS, hlog⟩ := hD.logCanonicalClass_strictTransform_pointBlowup k hp
  let hE := (P).isEffectiveCartier_comap_blowupToBase
  refine ⟨TauCeti.isEffectiveCartier_mul hS (TauCeti.isEffectiveCartier_pow hE (m - 1)), ?_, ?_⟩
  · rw [LineBundleClass.mk_toInvertibleSheaf_mul hS
      (TauCeti.isEffectiveCartier_pow hE (m - 1)),
      LineBundleClass.mk_toInvertibleSheaf_pow hE]
    rw [← hanti, mul_inv_cancel, LineBundleClass.pullback_one, one_mul] at hlog
    have hs : (1 : ℤ) - (m : ℤ) = -((m - 1 : ℕ) : ℤ) := by omega
    rw [hs, zpow_neg, zpow_natCast, blowupExceptionalClass_def, inv_pow, inv_inv] at hlog
    exact (mul_comm _ _).trans (mul_inv_eq_iff_eq_mul.mp hlog).symm
  · have ht : D.comap π = S * E ^ m :=
      hD.totalTransform_eq_strictTransform_mul_pow_closedPoint hp hdim
    rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hm, ht]

/-- Blowing up a closed point where an anticanonical divisor is regular leaves its strict
transform anticanonical, with the exceptional divisor appearing once in the total transform. -/
theorem IsEffectiveCartier.exists_anticanonical_strictTransform_of_isRegularLocalRing
    (hD : D.IsEffectiveCartier) (hp : IsClosed ({p} : Set X))
    (q : D.subscheme) (hq : D.subschemeι q = p)
    [IsRegularLocalRing (D.subscheme.presheaf.stalk q)]
    (hanti : LineBundleClass.mk hD.toInvertibleSheaf = K(X)) :
    letI : (P).blowup.Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    letI : SmoothOfRelativeDimension 2 ((P).blowup ↘ Spec (.of k)) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
    ∃ hS : (S).IsEffectiveCartier,
      LineBundleClass.mk hS.toInvertibleSheaf = K((P).blowup) ∧ S * E = D.comap π := by
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  have hqD : D.subschemeι q ∈ (D.support : Set X) := D.range_subschemeι ▸ Set.mem_range_self q
  have hm : D.stalkOrder p = 1 :=
    hq ▸ (hD.stalkOrder_eq_one_iff_isRegularLocalRing q).mpr inferInstance
  simpa only [hm, ENat.toNat_one, Nat.sub_self, pow_zero, mul_one] using
    hD.exists_anticanonical_strictTransform_mul_exceptional_pow k hp (hq ▸ hqD) hanti

end AlgebraicGeometry.Scheme.IdealSheafData
