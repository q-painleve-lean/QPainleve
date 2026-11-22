/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.Support

/-!
# Ideal sheaves of effective Weil divisors

On a locally factorial Noetherian integral scheme, an effective Weil divisor defines
the ideal sheaf of its effective Cartier representative.
-/

public section

open AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.SchemeWeilDivisor

noncomputable section

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

attribute [local instance] IsNormalScheme.of_uniqueFactorizationMonoid_stalk

/-- The ideal sheaf of an effective Weil divisor, with its Cartier scheme structure. -/
def idealSheaf (D : SchemeWeilDivisor X) (hD : 0 ≤ D) : X.IdealSheafData :=
  ((isEffective_equivCartierDivisorOfUniqueFactorizationMonoid_iff D).mpr hD).idealSheaf

/-- An effective Weil divisor defines an effective Cartier ideal. -/
theorem isEffectiveCartier_idealSheaf (D : SchemeWeilDivisor X) (hD : 0 ≤ D) :
    (D.idealSheaf hD).IsEffectiveCartier :=
  let h := (isEffective_equivCartierDivisorOfUniqueFactorizationMonoid_iff D).mpr hD
  h.isEffectiveCartier_idealSheaf

/-- The Cartier divisor of the ideal of an effective Weil divisor is its Cartier representative. -/
@[simp]
theorem toCartierDivisor_idealSheaf (D : SchemeWeilDivisor X) (hD : 0 ≤ D) :
    (D.isEffectiveCartier_idealSheaf hD).toCartierDivisor =
      equivCartierDivisorOfUniqueFactorizationMonoid D :=
  Scheme.CartierDivisor.IsEffective.toCartierDivisor_idealSheaf _

/-- Addition of effective Weil divisors corresponds to multiplication of their ideal sheaves. -/
@[simp]
theorem idealSheaf_add (D E : SchemeWeilDivisor X) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    (D + E).idealSheaf (add_nonneg hD hE) = D.idealSheaf hD * E.idealSheaf hE := by
  let hI := D.isEffectiveCartier_idealSheaf hD
  let hJ := E.isEffectiveCartier_idealSheaf hE
  apply ((isEffectiveCartier_idealSheaf (D + E) _).toCartierDivisor_eq_iff
    (TauCeti.isEffectiveCartier_mul hI hJ)).mp
  calc
    _ = equivCartierDivisorOfUniqueFactorizationMonoid (D + E) :=
      toCartierDivisor_idealSheaf _ _
    _ = equivCartierDivisorOfUniqueFactorizationMonoid D +
        equivCartierDivisorOfUniqueFactorizationMonoid E :=
      map_add equivCartierDivisorOfUniqueFactorizationMonoid _ _
    _ = hI.toCartierDivisor + hJ.toCartierDivisor :=
      congrArg₂ (· + ·) (toCartierDivisor_idealSheaf D hD).symm
        (toCartierDivisor_idealSheaf E hE).symm
    _ = _ := (hI.toCartierDivisor_mul hJ).symm

/-- At a prime divisor, zero coefficient means its generic point lies outside the support. -/
theorem coeff_eq_zero_iff_notMem_support (D : SchemeWeilDivisor X) (hD : 0 ≤ D)
    (x : CodimensionOnePoint X) :
    WeilDivisor.coeff D x = 0 ↔ (x : X) ∉ (D.idealSheaf hD).support := by
  have h := (D.isEffectiveCartier_idealSheaf hD).coeff_toWeilDivisor_eq_zero_iff x
  rwa [toCartierDivisor_idealSheaf,
    toWeilDivisor_equivCartierDivisorOfUniqueFactorizationMonoid] at h

/-- The ideal of the Weil divisor of an effective Cartier divisor recovers the Cartier ideal. -/
@[simp]
theorem idealSheaf_toWeilDivisor {D : Scheme.CartierDivisor X} (hD : D.IsEffective) :
    idealSheaf D.toWeilDivisor
      ((Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg D).mp hD) = hD.idealSheaf := by
  have he : equivCartierDivisorOfUniqueFactorizationMonoid D.toWeilDivisor = D :=
    equivCartierDivisorOfUniqueFactorizationMonoid_toWeilDivisor D
  have hE := (isEffective_equivCartierDivisorOfUniqueFactorizationMonoid_iff D.toWeilDivisor).mpr
    ((Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg D).mp hD)
  have hsub : (⟨_, hE⟩ : {C : Scheme.CartierDivisor X // C.IsEffective}) = ⟨D, hD⟩ :=
    Subtype.ext he
  exact congrArg (fun E : {C : Scheme.CartierDivisor X // C.IsEffective} ↦ E.property.idealSheaf)
    hsub

/-- The zero Weil divisor cuts out the empty subscheme. -/
@[simp]
theorem idealSheaf_zero : idealSheaf (0 : SchemeWeilDivisor X) le_rfl = ⊤ := by
  apply ((isEffectiveCartier_idealSheaf _ _).toCartierDivisor_eq_iff
    (Scheme.IdealSheafData.isEffectiveCartier_top X)).mp
  rw [toCartierDivisor_idealSheaf, map_zero,
    Scheme.IdealSheafData.IsEffectiveCartier.toCartierDivisor_top]

end

end TauCeti.AlgebraicGeometry.SchemeWeilDivisor
