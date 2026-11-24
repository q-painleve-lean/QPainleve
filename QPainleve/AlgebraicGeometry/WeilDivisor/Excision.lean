/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.WeilDivisor.IdealSheaf

import Mathlib.Data.Finsupp.Order
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Excision for effective Cartier divisors

On a locally factorial Noetherian integral scheme, an effective divisor on an open
subscheme extends by taking the closures of its prime components. A reduced
divisor is recovered by schematic closure once the open contains the generic points
of its components. Together these give the divisor comparison across a point blowup.
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

universe u

/-- An effective Cartier divisor on an open subscheme extends to an
effective Cartier divisor on the locally factorial Noetherian ambient integral scheme. -/
theorem exists_comap_eq_of_isOpenImmersion {U X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    (j : U ⟶ X) [IsOpenImmersion j]
    {D : U.IdealSheafData} (hD : D.IsEffectiveCartier) :
    ∃ E : X.IdealSheafData, E.IsEffectiveCartier ∧ E.comap j = D := by
  classical
  rcases isEmpty_or_nonempty U with hU | hU
  · have : IsEmpty D.subscheme := Function.isEmpty D.subschemeι
    have hDtop : D = ⊤ :=
      D.ker_subschemeι.symm.trans (D.subschemeι.ker_eq_top_iff_isEmpty.mpr inferInstance)
    exact ⟨⊤, isEffectiveCartier_top X, (comap_top j).trans hDtop.symm⟩
  let : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  have : IsIntegral U := isIntegral_of_isOpenImmersion j
  have : IsNoetherian U := isNoetherian_of_isOpenImmersion j
  have : IsNormalScheme U := IsNormalScheme.of_isOpenImmersion j
  let e : CodimensionOnePoint U ↪ CodimensionOnePoint X :=
    ⟨CodimensionOnePoint.mapOfIsOpenImmersion j,
      CodimensionOnePoint.mapOfIsOpenImmersion_injective j⟩
  let W := hD.toCartierDivisor.toWeilDivisor
  let V : SchemeWeilDivisor X := W.embDomain e
  have hW : 0 ≤ W := (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
    hD.isEffective_toCartierDivisor
  have hV : 0 ≤ V := by simpa only [Finsupp.embDomain_zero] using Finsupp.embDomain_mono e hW
  let E := V.idealSheaf hV
  have hE := V.isEffectiveCartier_idealSheaf hV
  have hEU := hE.comap j
  refine ⟨E, hE, (hEU.toCartierDivisor_eq_iff hD).mp ?_⟩
  apply Scheme.CartierDivisor.toWeilDivisorHom_injective
  ext y
  rw [Scheme.CartierDivisor.toWeilDivisorHom_apply,
    Scheme.CartierDivisor.toWeilDivisorHom_apply, WeilDivisor.coeff, WeilDivisor.coeff,
    hE.coeff_toWeilDivisor_comap_of_isOpenImmersion j hEU,
    V.toCartierDivisor_idealSheaf,
    SchemeWeilDivisor.toWeilDivisor_equivCartierDivisorOfUniqueFactorizationMonoid]
  exact Finsupp.embDomain_apply_self e W y

/-- A reduced effective Cartier divisor is the schematic closure of its restriction
to any open containing the generic points of all its components. -/
theorem map_comap_eq_of_codimensionOne_mem_range {U X : Scheme.{u}} [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    [IsReduced D.subscheme]
    (hj : ∀ x : CodimensionOnePoint X, (x : X) ∈ D.support → (x : X) ∈ Set.range j) :
    (D.comap j).map j = D := by
  have hred : vanishingIdeal D.support = D :=
    vanishingIdeal_support.trans ((D.isReduced_subscheme_iff_radical_eq).mp inferInstance)
  have heq : D.comap j = vanishingIdeal (D.support.preimage j.continuous) := by
    have h := comap_vanishingIdeal_of_isOpenImmersion j D.support
    rw [hred] at h
    refine h.trans (congrArg vanishingIdeal ?_)
    exact Closeds.ext rfl
  rw [heq, map_vanishingIdeal]
  suffices h : closure (j '' (j ⁻¹' (D.support : Set X))) = D.support by
    exact (congrArg vanishingIdeal (Closeds.ext h)).trans hred
  refine (closure_minimal (Set.image_preimage_subset _ _) D.support.isClosed).antisymm ?_
  intro x hx
  obtain ⟨p, hp, hpx⟩ := hD.mem_support_iff_exists_codimensionOnePoint.mp hx
  obtain ⟨y, hy⟩ := hj p hp
  have hyn : p.val ∈ j '' (j ⁻¹' (D.support : Set X)) :=
    ⟨y, Set.mem_preimage.mpr (hy.symm ▸ hp), hy⟩
  exact closure_mono (Set.singleton_subset_iff.mpr hyn) (specializes_iff_mem_closure.mp hpx)

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
