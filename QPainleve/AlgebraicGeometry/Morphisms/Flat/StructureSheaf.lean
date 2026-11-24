/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Restricting a comparison of regular functions

An isomorphism on sections over one affine open restricts to an isomorphism over
any smaller affine open. The argument uses the flat base-change isomorphism
`isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` for sections.
-/

public section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- For a quasi-compact, quasi-separated morphism, an isomorphism on sections over
an affine open induces an isomorphism on sections over any affine open it contains. -/
theorem isIso_app_of_isIso_app_of_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] {U V : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hVU : V ≤ U) [IsIso (f.app U)] : IsIso (f.app V) := by
  have : IsAffine V := hV
  have hpre : (⊤ : Opens V) ≤ V.ι ⁻¹ᵁ U := fun x _ ↦ hVU x.property
  have hpre' : (f ⁻¹ᵁ V).ι ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊤ :=
    top_unique (fun x _ ↦ f.preimage_mono hVU x.property)
  let H := (isPullback_morphismRestrict f V).flip
  have hUY : (⊤ : Opens (f ⁻¹ᵁ V)) =
      (f ⁻¹ᵁ V).ι ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ (f ∣_ V) ⁻¹ᵁ (⊤ : Opens V) := by
    simp [hpre']
  have hc := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H hpre le_rfl hUY
    hU (isAffineOpen_top _) (f.isCompact_preimage hU.isCompact)
    (f.isQuasiSeparated_preimage hU.isQuasiSeparated)
  have hb : IsIso (f.appLE U (f ⁻¹ᵁ U) le_rfl) := by rwa [appLE_eq_app]
  have hd := ((isIso_pushoutSection_iff H hpre le_rfl hUY).mp hc).isIso_inr_of_isIso
  have ht : IsIso ((f ∣_ V).appTop) := by
    rw [appTop, app_eq_appLE]
    exact ((f ∣_ V).appLE_congr (by simp) rfl ((f ∣_ V).preimage_top).symm
      (fun {_ _} a ↦ IsIso a)).mp hd
  rw [← resLE_eq_morphismRestrict, appTop, resLE_app_top, ← app_eq_appLE] at ht
  exact (isIso_comp_right_iff _ _).mp ((isIso_comp_left_iff _ _).mp ht)

end AlgebraicGeometry.Scheme.Hom
