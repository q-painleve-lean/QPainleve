/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.Support

/-!
# Picard classes from Weil coefficients

The class of an effective Cartier divisor on a locally factorial scheme is computed
by summing the classes of the prime divisors with their actual multiplicities.
-/

public section

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {X : Scheme.{u}} [IsIntegral X] {I : X.IdealSheafData}

open TauCeti.AlgebraicGeometry LineBundleClass in
/-- The class of an effective Cartier divisor supported on the listed primes is the sum of
their classes weighted by its Weil coefficients. -/
theorem ofMul_inv_toInvertibleSheaf_eq_sum_coeff_zsmul_primeDivisorClass [IsNoetherian X]
    [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    (hI : I.IsEffectiveCartier) {ι : Type*} [Fintype ι] (p : ι ↪ CodimensionOnePoint X)
    (hp : ∀ x : CodimensionOnePoint X, (x : X) ∈ I.support → x ∈ Set.range p) :
    Additive.ofMul (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ =
      ∑ i, WeilDivisor.coeff hI.toCartierDivisor.toWeilDivisor (p i) •
        Additive.ofMul (primeDivisorClass (p i)) := by
  let W := hI.toCartierDivisor.toWeilDivisor
  let f := Finsupp.comapDomain p W p.injective.injOn
  have hW : hI.toCartierDivisor.toWeilDivisor = Finsupp.mapDomain p f := by
    symm
    apply Finsupp.mapDomain_comapDomain p p.injective
    intro x hx
    apply hp x
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hx) ((hI.coeff_toWeilDivisor_eq_zero_iff x).mpr hn)
  rw [← hI.toLineBundleClass_toCartierDivisor,
    ← Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor]
  conv_lhs => rw [hW, Finsupp.mapDomain,
    Finsupp.sum_fintype _ _ (fun _ ↦ Finsupp.single_zero _), map_sum]
  simp only [Scheme.CartierDivisor.weilToLineBundleClassHom_single,
    ← LineBundleClass.primeDivisorClass_def, f, Finsupp.comapDomain_apply, W, WeilDivisor.coeff]

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
