/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange

/-!
# Global sections of twists under graded projective maps

Homogeneous forms give global sections of twists. This construction respects
graded projective maps and is linear over the coefficient ring. The coefficient
calculation generalizes Tau Ceti's `SymmetricAlgebra.toTwistingSheaf_top_smul`.
-/

public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Proj

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The twisting-sheaf comparison carries the pullback of a global homogeneous
form to the global section of its image under the graded map. -/
theorem pullbackTwistingSheafMap_app_top_toTwistingSheaf
    (F : 𝒜 →+*ᵍ ℬ)
    (hF : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map F)
    {n : ℤ} {j : ℕ} (hj : (j : ℤ) = n) (r : 𝒜 j) :
    (pullbackTwistingSheafMap F hF n).app ⊤
        ((map F hF).pullbackSectionsLE _ ⊤ ⊤ (map F hF).preimage_top.ge
          (toTwistingSheaf 𝒜 hj ⊤ r)) =
      toTwistingSheaf ℬ hj ⊤ ⟨F r, F.map_mem r.property⟩ := by
  let p := map F hF
  let φ := pullbackTwistingSheafMap F hF n
  let u := homOfLE p.preimage_top.ge
  let t := toTwistingSheaf 𝒜 hj ⊤ r
  have h := φ.mapPresheaf.naturality_apply u.op (p.pullbackSections _ ⊤ t)
  have ht : φ.app (p ⁻¹ᵁ ⊤) (p.pullbackSections _ ⊤ t) =
      toTwistingSheaf ℬ hj (p ⁻¹ᵁ ⊤) ⟨F r, F.map_mem r.property⟩ :=
    (pullbackTwistingSheafMap_app_pullbackSections F hF n ⊤ t).trans
      (comap_toTwistingSheaf F hF Set.Subset.rfl hj r)
  simpa only [Scheme.Modules.mapPresheaf_app, unop_op, ht, res_toTwistingSheaf,
    Scheme.Hom.pullbackSectionsLE_apply, u] using h

/-- A degree-one element gives the standard generator of `𝒪(1)` on every open
contained in its standard chart. -/
theorem toTwistingSheaf_one_eq_chartGenerator (r : 𝒜 1) (V : (Proj 𝒜).Opens)
    (hV : V ≤ basicOpen 𝒜 (r : A)) :
    toTwistingSheaf 𝒜 rfl V r = twistingSheaf.chartGenerator 1 r.val r.property V hV := by
  apply twistingSheaf.ext
  intro x
  -- Both sides are fractions in the same homogeneous localization at the point.
  erw [toTwistingSheaf_apply_apply, twistingSheaf.chartGenerator_apply]
  simp only [Int.toNat_one, Int.reduceNeg, Int.toNat_of_nonpos (by decide : (-1 : ℤ) ≤ 0),
    pow_one, pow_zero]
  rfl

section Coefficients

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The section of a twist defined by a homogeneous form is linear over the
coefficient ring, acting through the projective structure morphism. -/
theorem toTwistingSheaf_top_smul_toSpecCoeff {n : ℤ} {j : ℕ} (hj : (j : ℤ) = n)
    (r : R) (p : 𝒜 j) :
    toTwistingSheaf 𝒜 hj ⊤ (r • p) =
      (toSpecCoeff 𝒜).appTop ((Scheme.ΓSpecIso (.of R)).inv r) •
        toTwistingSheaf 𝒜 hj ⊤ p := by
  -- This is the same localization computation as for a symmetric algebra.
  refine twistingSheaf.ext fun x ↦ ?_
  rw [twistingSheaf.smul_apply, val_toSpecCoeff_appTop_apply, toTwistingSheaf_apply_apply,
    toTwistingSheaf_apply_apply, Localization.mk_mul, one_mul, Submodule.coe_smul,
    Algebra.smul_def]

end Coefficients

end AlgebraicGeometry.Proj
