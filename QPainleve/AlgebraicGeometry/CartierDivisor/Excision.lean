/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Excision
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The Picard quotient in open excision

Restriction to an open subscheme of a locally factorial, integral Noetherian scheme
identifies its Picard group with the quotient by the prime divisors in the complement.
This bundles Tau Ceti's `pullback_surjective_of_isOpenImmersion` and
`pullback_eq_one_iff_mem_closure_of_isOpenImmersion` into an equivalence, with
the restriction formula on representatives.
-/

public noncomputable section

open TauCeti.AlgebraicGeometry LineBundleClass

namespace AlgebraicGeometry.Scheme.Opens

universe u

variable {X : Scheme.{u}}

section Span

variable [IsLocallyNoetherian X] [∀ x : X, IsDomain (X.presheaf.stalk x)]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

/-- The span in the additive Picard group of the prime divisor classes whose generic
points lie outside the open. -/
def primeDivisorSpanCompl (U : X.Opens) : Submodule ℤ (Additive (LineBundleClass X)) :=
  Submodule.span ℤ (Additive.toMul ⁻¹'
    {primeDivisorClass x | (x : CodimensionOnePoint X) (_ : (x : X) ∉ U)})

/-- Each prime divisor in the complement contributes its class to the span. -/
theorem primeDivisorClass_mem_primeDivisorSpanCompl (U : X.Opens) (η : CodimensionOnePoint X)
    (hη : (η : X) ∉ U) : Additive.ofMul (primeDivisorClass η) ∈ U.primeDivisorSpanCompl :=
  Submodule.subset_span ⟨η, hη, rfl⟩

end Span

variable [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

/-- A Picard class lies in the span of the complementary prime divisors exactly when its
restriction to the open is trivial. -/
theorem mem_primeDivisorSpanCompl_iff (U : X.Opens) (a : LineBundleClass X) :
    Additive.ofMul a ∈ U.primeDivisorSpanCompl ↔ pullback U.ι a = 1 := by
  rw [← Submodule.mem_toAddSubgroup, primeDivisorSpanCompl,
    Submodule.span_int_eq_addSubgroupClosure, ← Subgroup.toAddSubgroup_closure,
    Additive.mem_toAddSubgroup, toMul_ofMul]
  simpa only [Scheme.Opens.range_ι, SetLike.mem_coe] using
    (pullback_eq_one_iff_mem_closure_of_isOpenImmersion U.ι (a := a)).symm

private theorem ker_pullback_opens_ι (U : X.Opens) :
    LinearMap.ker (pullbackHom U.ι).toAdditive.toIntLinearMap = U.primeDivisorSpanCompl := by
  ext a
  rw [LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap, MonoidHom.toAdditive_apply_apply,
    pullbackHom_apply, ← toMul_eq_one, toMul_ofMul]
  exact (U.mem_primeDivisorSpanCompl_iff a.toMul).symm

/-- Restriction identifies the Picard group modulo the prime divisor classes outside an open
with the Picard group of the open. -/
def quotientPrimeDivisorSpanComplEquiv (U : X.Opens) :
    (Additive (LineBundleClass X) ⧸ primeDivisorSpanCompl U) ≃ₗ[ℤ]
      Additive (LineBundleClass U) :=
  (Submodule.quotEquivOfEq _ _ (ker_pullback_opens_ι U).symm).trans
    ((pullbackHom U.ι).toAdditive.toIntLinearMap.quotKerEquivOfSurjective
      (fun a ↦ by
        obtain ⟨b, hb⟩ := pullback_surjective_of_isOpenImmersion U.ι a.toMul
        exact ⟨Additive.ofMul b, by
          simpa only [AddMonoidHom.coe_toIntLinearMap, MonoidHom.toAdditive_apply_apply,
            pullbackHom_apply, toMul_ofMul, ofMul_toMul] using congrArg Additive.ofMul hb⟩))

/-- The open excision equivalence restricts a line bundle representative to the open. -/
@[simp]
theorem quotientPrimeDivisorSpanComplEquiv_mk (U : X.Opens) (a : LineBundleClass X) :
    quotientPrimeDivisorSpanComplEquiv U (Submodule.Quotient.mk (Additive.ofMul a)) =
      Additive.ofMul (pullback U.ι a) := by
  rw [quotientPrimeDivisorSpanComplEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  exact (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _).trans (by
    simp only [AddMonoidHom.coe_toIntLinearMap, MonoidHom.toAdditive_apply_apply,
      pullbackHom_apply, toMul_ofMul])

end AlgebraicGeometry.Scheme.Opens

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory

variable {X Y : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
  [IsIntegral Y] [IsNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]

/-- If a morphism is an isomorphism over an open, its pullback identifies the Picard
quotients by the complementary prime divisors. -/
def quotientPrimeDivisorSpanComplEquiv (f : Y ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] :
    (Additive (LineBundleClass X) ⧸ U.primeDivisorSpanCompl) ≃ₗ[ℤ]
      (Additive (LineBundleClass Y) ⧸ (f ⁻¹ᵁ U).primeDivisorSpanCompl) :=
  U.quotientPrimeDivisorSpanComplEquiv.trans
    (((pullbackEquiv (asIso (f ∣_ U))).toAdditive.toIntLinearEquiv).trans
      (f ⁻¹ᵁ U).quotientPrimeDivisorSpanComplEquiv.symm)

/-- On representatives the equivalence is induced by pullback along the given morphism. -/
@[simp]
theorem quotientPrimeDivisorSpanComplEquiv_mk (f : Y ⟶ X) (U : X.Opens)
    [IsIso (f ∣_ U)] (a : LineBundleClass X) :
    f.quotientPrimeDivisorSpanComplEquiv U (Submodule.Quotient.mk (Additive.ofMul a)) =
      Submodule.Quotient.mk (Additive.ofMul (pullback f a)) := by
  apply (f ⁻¹ᵁ U).quotientPrimeDivisorSpanComplEquiv.injective
  simp [quotientPrimeDivisorSpanComplEquiv, pullback_comp, morphismRestrict_ι]

end AlgebraicGeometry.Scheme.Hom
