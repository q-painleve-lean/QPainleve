/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.BaseChange.Translation
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

import QPainleve.Geometry.Toric.Fan.Boundary.Automorphism
import QPainleve.Geometry.Toric.Fan.Picard.FiniteFanScheme

/-!
# Torus translations on the toric Picard group

Torus translations preserve the reduced ray divisors. The generation theorem
`Fan.rayChartDivisorToPicard_surjective` then identifies their action on the whole
Picard group.
-/

public section

open AlgebraicGeometry Multiplicative
open TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan

universe u

variable (K : Type u) [CommRing K] [IsDomain K] [IsNoetherianRing K] [UniqueFactorizationMonoid K]
  {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]

/-- Pullback by a torus translation fixes the Picard group of the regular fan scheme. -/
theorem pullback_torusTranslation_hom (hΦ : Φ.IsRegular) (χ : Multiplicative (N →+ ℤ) →* Kˣ)
    (a : LineBundleClass (Φ.finiteFanScheme K)) :
    pullback (Φ.torusTranslationIso K χ).hom a = a := by
  classical
  let := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := K) hΦ
  let := Fintype.ofFinite Φ.Ray
  let t := (Φ.torusTranslationIso K χ).hom
  obtain ⟨d, hd⟩ := Φ.rayChartDivisorToPicard_surjective K hΦ (Additive.ofMul a)
  have hρ (ρ : Φ.Ray) :
      pullback t (primeDivisorClass (Φ.rayBoundaryChartPoint (R := K) hΦ ρ)) =
        primeDivisorClass (Φ.rayBoundaryChartPoint (R := K) hΦ ρ) := by
    let hD := Φ.isEffectiveCartier_rayDivisorIdeal K hΦ ρ
    have hfix := Φ.comap_rayBoundaryIdeal_torusTranslation_hom K hΦ χ ρ
    have hbase : primeDivisorClass (Φ.rayBoundaryChartPoint (R := K) hΦ ρ) =
        (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ := by
      rw [primeDivisorClass_def, mk_toInvertibleSheaf_congr _ hD
        (Φ.rayDivisorIdeal_def K hΦ ρ).symm]
    rw [hbase, pullback_inv, hD.pullback_mk_toInvertibleSheaf (hD.comap t),
      mk_toInvertibleSheaf_congr _ hD hfix]
  have hd' := congrArg Additive.toMul hd
  rw [toMul_ofMul, Φ.rayChartDivisorToPicard_apply K] at hd'
  change pullback t a = a
  rw [← hd', toMul_sum, ← pullbackHom_apply (f := t), map_prod]
  simp only [toMul_zsmul, toMul_ofMul, map_zpow, pullbackHom_apply, hρ]

end TauCeti.Toric.Fan
