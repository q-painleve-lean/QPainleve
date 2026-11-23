/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Pullback of Cartier divisors along isomorphisms near the support

A morphism that is an isomorphism over the support of an effective Cartier divisor
pulls it back to an effective Cartier divisor. This is the local form of Cartier
pullback used when comparing blowups under modifications away from their centers.
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

/-- Pullback preserves an effective Cartier divisor when the morphism is an isomorphism
over its support. -/
theorem IsEffectiveCartier.comap_of_support_subset_isoLocus {X Y : Scheme.{u}}
    {I : Y.IdealSheafData} (hI : I.IsEffectiveCartier) (f : X ⟶ Y)
    (h : (I.support : Set Y) ⊆ f.isoLocus) :
    (I.comap f).IsEffectiveCartier := by
  apply isEffectiveCartier_of_forall_exists_isOpenImmersion
  intro x
  by_cases hx : f x ∈ I.support
  · let U := f.isoLocus
    let V := f ⁻¹ᵁ U
    have : IsIso (f ∣_ U) := inferInstanceAs (IsIso (f ∣_ f.isoLocus))
    refine ⟨_, V.ι, inferInstance, ⟨⟨x, h hx⟩, rfl⟩, ?_⟩
    rw [← comap_comp, ← morphismRestrict_ι, comap_comp]
    exact (hI.comap U.ι).comap (f ∣_ U)
  · let V := f ⁻¹ᵁ I.support.compl
    refine ⟨_, V.ι, inferInstance, ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    rw [← comap_comp, (I.comap_eq_top_iff _).mpr ?_]
    · exact isEffectiveCartier_top _
    · rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]

/-- The ideal class of an effective Cartier divisor pulls back to the trivial class
along a morphism whose image avoids its support. -/
theorem IsEffectiveCartier.pullback_mk_toInvertibleSheaf_eq_one_of_comap_eq_top
    {X Y : Scheme.{u}} {I : Y.IdealSheafData} (hI : I.IsEffectiveCartier) {f : X ⟶ Y}
    (hf : I.comap f = ⊤) :
    LineBundleClass.pullback f (LineBundleClass.mk hI.toInvertibleSheaf) = 1 := by
  rw [hI.pullback_mk_toInvertibleSheaf (hf.symm ▸ isEffectiveCartier_top X),
    LineBundleClass.mk_toInvertibleSheaf_congr _ (isEffectiveCartier_top X) hf,
    LineBundleClass.mk_toInvertibleSheaf_top]

/-- The divisor class of an effective Cartier divisor restricts to the trivial class on
the closed subscheme defined by an ideal with disjoint support. -/
theorem IsEffectiveCartier.pullback_effectiveCartierClass_eq_one_of_disjoint
    {X : Scheme.{u}} {I J : X.IdealSheafData} (hI : I.IsEffectiveCartier)
    (h : Disjoint (J.support : Set X) (I.support : Set X)) :
    LineBundleClass.pullback J.subschemeι (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ = 1 := by
  have hcomap : I.comap J.subschemeι = ⊤ := by
    apply (I.comap_eq_top_iff _).mpr
    ext x
    simpa using Set.disjoint_left.mp h (J.range_subschemeι.le (Set.mem_range_self x))
  rw [LineBundleClass.pullback_inv, hI.pullback_mk_toInvertibleSheaf_eq_one_of_comap_eq_top hcomap,
    inv_one]

end AlgebraicGeometry.Scheme.IdealSheafData
