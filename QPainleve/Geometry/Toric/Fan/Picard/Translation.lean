/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Presentation
public import QPainleve.Geometry.Toric.Fan.TorusAction.Translation

import QPainleve.Geometry.Toric.Fan.Boundary.Automorphism

/-!
# Torus translations on the Picard group

On a regular fan scheme, torus translations preserve the ray divisors. These divisors
generate the Picard group, so translation pullback fixes every line bundle class.
-/

public noncomputable section

open Multiplicative
open TauCeti.AlgebraicGeometry (LineBundleClass)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]

local notation "Chars" => (Multiplicative (N →+ ℤ) →* ℂˣ)

/-- Torus translations act trivially on the Picard group of a regular fan scheme. -/
theorem pullback_torusTranslation_eq (hΦ : Φ.IsRegular) (χ : Chars)
    (a : LineBundleClass Φ.algebraicRealization) :
    LineBundleClass.pullback (Φ.torusTranslation χ).hom a = a := by
  classical
  let := Fintype.ofFinite Φ.Ray
  have := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  let f := LineBundleClass.pullbackHom (Φ.torusTranslation χ).hom
  have hsingle (ρ : Φ.Ray) :
      f (LineBundleClass.primeDivisorClass (Φ.rayBoundaryPoint hΦ ρ)) =
        LineBundleClass.primeDivisorClass (Φ.rayBoundaryPoint hΦ ρ) := by
    let D := Φ.rayBoundaryIdeal hΦ ρ
    have hD : D.IsEffectiveCartier := Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ
    have heq : D.comap (Φ.torusTranslation χ).hom = D :=
      Φ.comap_rayBoundaryIdeal_torusTranslation_hom hΦ χ ρ
    let toClass := fun J : {I : Φ.algebraicRealization.IdealSheafData // I.IsEffectiveCartier} ↦
      LineBundleClass.mk J.property.toInvertibleSheaf
    have hline := congrArg toClass (Subtype.ext heq :
      (⟨_, hD.comap (Φ.torusTranslation χ).hom⟩ :
        {I : Φ.algebraicRealization.IdealSheafData // I.IsEffectiveCartier}) = ⟨D, hD⟩)
    simp only [f, LineBundleClass.pullbackHom_apply,
      LineBundleClass.primeDivisorClass_def, ← Φ.rayBoundaryIdeal_def, LineBundleClass.pullback_inv]
    rw [hD.pullback_mk_toInvertibleSheaf (hD.comap (Φ.torusTranslation χ).hom)]
    exact congrArg Inv.inv hline
  obtain ⟨u, hu⟩ := Φ.rayDivisorToPicard_surjective hΦ (Additive.ofMul a)
  rw [← LineBundleClass.pullbackHom_apply]
  suffices f a = a from this
  have hu' : ((Φ.rayDivisorToPicard hΦ) u).toMul = a := congrArg Additive.toMul hu
  rw [← hu', Φ.rayDivisorToPicard_apply]
  simp only [toMul_sum, toMul_zsmul, toMul_ofMul, map_prod, map_zpow, hsingle]

end TauCeti.Toric.Fan
