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

open TauCeti.AlgebraicGeometry LineBundleClass TopologicalSpace

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

/-- A family enumerating the codimension-one points outside an open generates its
complementary prime-divisor span. -/
theorem primeDivisorSpanCompl_eq_span_of_mem_iff {ι : Type*} (U : X.Opens)
    (η : ι → CodimensionOnePoint X)
    (h : ∀ x : CodimensionOnePoint X, (x : X) ∉ U ↔ x ∈ Set.range η) :
    U.primeDivisorSpanCompl =
      Submodule.span ℤ (Set.range fun j ↦ Additive.ofMul (primeDivisorClass (η j))) := by
  rw [primeDivisorSpanCompl]
  apply congrArg (Submodule.span ℤ)
  apply Set.ext
  intro a
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨j, rfl⟩ := (h x).mp hx
    exact Set.mem_range_self j
  · rintro ⟨j, rfl⟩
    exact ⟨η j, (h _).mpr (Set.mem_range_self j), rfl⟩

/-- If the complement is the union of the closures of a family of codimension-one points,
the classes of that family generate its boundary span. -/
theorem primeDivisorSpanCompl_eq_span_of_iUnion_closure {ι : Type*} (U : X.Opens)
    (η : ι → CodimensionOnePoint X) (h : (U : Set X)ᶜ = ⋃ j, closure {(η j : X)}) :
    U.primeDivisorSpanCompl =
      Submodule.span ℤ (Set.range fun j ↦ Additive.ofMul (primeDivisorClass (η j))) := by
  apply U.primeDivisorSpanCompl_eq_span_of_mem_iff η
  intro x
  constructor
  · intro hx
    have hx' : (x : X) ∈ (U : Set X)ᶜ := hx
    rw [h, Set.mem_iUnion] at hx'
    obtain ⟨j, hj⟩ := hx'
    have he := CodimensionOnePoint.eq_of_specializes (specializes_iff_mem_closure.mpr hj)
    exact ⟨j, he⟩
  · rintro ⟨j, rfl⟩
    have hj : (η j : X) ∈ (U : Set X)ᶜ :=
      h ▸ Set.mem_iUnion.mpr ⟨j, subset_closure (Set.mem_singleton _)⟩
    exact hj

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

/-- Over an open where `f` is an isomorphism, the pullback of a prime divisor class
and the class of its strict transform have the same restriction. -/
theorem pullback_primeDivisorClass_sub_mem_primeDivisorSpanCompl
    (f : Y ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)]
    (x : CodimensionOnePoint X) (y : CodimensionOnePoint Y)
    (hy : f y = x) (hxU : (x : X) ∈ U) :
    Additive.ofMul (pullback f (primeDivisorClass x)) - Additive.ofMul (primeDivisorClass y) ∈
      (f ⁻¹ᵁ U).primeDivisorSpanCompl := by
  let V := f ⁻¹ᵁ U
  obtain ⟨p, hp⟩ := (CodimensionOnePoint.mem_range_mapOfIsOpenImmersion V.ι).mpr
    ⟨⟨y, f.mem_preimage.mpr (hy.symm ▸ hxU)⟩, rfl⟩
  have hpy : V.ι p.val = y.val := by
    simpa only [CodimensionOnePoint.coe_mapOfIsOpenImmersion] using congrArg Subtype.val hp
  have hq : CodimensionOnePoint.mapOfIsOpenImmersion U.ι
      (CodimensionOnePoint.mapOfIsOpenImmersion (f ∣_ U) p) = x := by
    apply Subtype.ext
    rw [← CodimensionOnePoint.mapOfIsOpenImmersion_comp,
      CodimensionOnePoint.coe_mapOfIsOpenImmersion, morphismRestrict_ι,
      Scheme.Hom.comp_apply, hpy, hy]
  rw [← ofMul_div, V.mem_primeDivisorSpanCompl_iff, ← pullbackHom_apply, map_div, div_eq_one]
  simp only [pullbackHom_apply]
  let := U.ι.isDomain_stalk_of_isOpenImmersion
  let := U.ι.uniqueFactorizationMonoid_stalk_of_isOpenImmersion
  rw [pullback_comp, ← morphismRestrict_ι, ← pullback_comp, ← hq,
    pullback_primeDivisorClass_mapOfIsOpenImmersion U.ι,
    pullback_primeDivisorClass_mapOfIsOpenImmersion (f ∣_ U), ← hp,
    pullback_primeDivisorClass_mapOfIsOpenImmersion V.ι]

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
