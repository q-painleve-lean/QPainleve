/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.TorusAction.Translation
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

import QPainleve.Geometry.Toric.Fan.Boundary.Automorphism
import QPainleve.Geometry.Toric.Fan.Picard.Presentation

/-!
# Torus translations on the toric Picard group

Torus translations preserve the reduced ray divisors. The generation theorem
`Fan.rayDivisorToPicard_surjective` then identifies their action on the whole
Picard group.
-/

public section

open AlgebraicGeometry Multiplicative
open TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]

/-- Pullback by a torus translation fixes the Picard group of the regular fan scheme. -/
theorem pullback_torusTranslation_hom (hΦ : Φ.IsRegular) (χ : Multiplicative (N →+ ℤ) →* ℂˣ)
    (a : LineBundleClass Φ.algebraicRealization) :
    pullback (Φ.torusTranslation χ).hom a = a := by
  classical
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  let := Fintype.ofFinite Φ.Ray
  let t := (Φ.torusTranslation χ).hom
  obtain ⟨d, hd⟩ := Φ.rayDivisorToPicard_surjective hΦ (Additive.ofMul a)
  have hρ (ρ : Φ.Ray) :
      pullback (Φ.torusTranslation χ).hom (primeDivisorClass (Φ.rayBoundaryPoint hΦ ρ)) =
        primeDivisorClass (Φ.rayBoundaryPoint hΦ ρ) := by
    let hD := Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ
    have hfix := Φ.comap_rayBoundaryIdeal_torusTranslation_hom hΦ χ ρ
    have hbase : primeDivisorClass (Φ.rayBoundaryPoint hΦ ρ) =
        (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ := by
      rw [primeDivisorClass_def, mk_toInvertibleSheaf_congr _ hD
        (Φ.rayBoundaryIdeal_def hΦ ρ).symm]
    rw [hbase, pullback_inv, hD.pullback_mk_toInvertibleSheaf (hD.comap t),
      mk_toInvertibleSheaf_congr _ hD hfix]
  have hd' := congrArg Additive.toMul hd
  rw [toMul_ofMul, Φ.rayDivisorToPicard_apply] at hd'
  rw [← hd', toMul_sum, ← pullbackHom_apply (f := (Φ.torusTranslation χ).hom), map_prod]
  simp only [toMul_zsmul, toMul_ofMul, map_zpow, pullbackHom_apply, hρ]

end TauCeti.Toric.Fan
