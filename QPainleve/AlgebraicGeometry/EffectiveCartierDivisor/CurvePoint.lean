/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.PureRelativeDimension

import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Factorial
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.Restrict

/-!
# Closed points in the smooth locus of a curve

The reduced ideal of a closed point in the smooth locus of a curve is effective
Cartier on the whole curve. Its blowup is therefore an isomorphism, which gives
the strict-transform comparison for a smooth boundary center on a surface.
-/

public section

open CategoryTheory TopologicalSpace TauCeti TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A closed point in the smooth part of a pure one-dimensional scheme over a field
is an effective Cartier divisor, even when the scheme has singular points elsewhere. -/
theorem isEffectiveCartier_ker_fromSpecResidueField_of_mem_smoothLocus
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [LocallyOfFinitePresentation f] [PureRelativeDimension 1 f] {p : C}
    (hp : IsClosed ({p} : Set C)) (hs : p ∈ f.smoothLocus) :
    (C.fromSpecResidueField p).ker.IsEffectiveCartier := by
  let J := (C.fromSpecResidueField p).ker
  let U := f.smoothLocus
  let q : U.toScheme := ⟨p, hs⟩
  let g := U.ι ≫ f
  have : Nonempty U.toScheme := ⟨q⟩
  have : SmoothOfRelativeDimension 1 g := inferInstanceAs
    (SmoothOfRelativeDimension 1 (f.smoothLocus.ι ≫ f))
  have : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  have : IsRegular U.toScheme := IsRegular.of_smooth g
  have hclosed : IsClosed ({q} : Set U.toScheme) := by
    have hpre : U.ι ⁻¹' {U.ι q} = {q} := by
      rw [← Set.image_singleton, U.ι.injective.preimage_image]
    exact hpre ▸ hp.preimage U.ι.continuous
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension g (n := 1)
  have hq := coheight_eq_of_isClosed_of_smoothOfRelativeDimension g (n := 1) hclosed
  have hU : U ≤ U.ι.isoLocus :=
    U.ι.le_isoLocus_iff.mpr (U.ι.isIso_morphismRestrict_of_le_opensRange U.opensRange_ι.ge)
  have hqι : U.ι q = p := rfl
  have hcomap := U.ι.comap_ker_fromSpecResidueField_of_mem_isoLocus (q := q)
    (by simpa only [hqι] using hp) (hqι.symm ▸ hU hs)
  have hcart : (J.comap U.ι).IsEffectiveCartier := by
    rw [hqι] at hcomap
    dsimp only [J]
    rw [hcomap, Scheme.ker_fromSpecResidueField_eq_vanishingIdeal]
    exact isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular
      (fun x ↦ (WithBot.coe_le_coe.mp ((coheight_le_topologicalKrullDim x).trans_eq hdim)).trans
        (by decide)) hq
  apply J.isEffectiveCartier_of_forall_exists_isOpenImmersion
  intro x
  by_cases hx : x = p
  · exact ⟨U.toScheme, U.ι, inferInstance, ⟨q, hx.symm⟩, hcart⟩
  · let V : C.Opens := J.support.compl
    have hx' : x ∈ V := by
      simpa only [V, J, ← SetLike.mem_coe, Closeds.coe_compl,
        Scheme.support_ker_fromSpecResidueField_of_isClosed hp, Set.mem_compl_iff,
        Set.mem_singleton_iff] using hx
    refine ⟨V.toScheme, V.ι, inferInstance, ⟨⟨x, hx'⟩, rfl⟩, ?_⟩
    rw [(J.comap_eq_top_iff V.ι).mpr V.ι_preimage_self]
    exact isEffectiveCartier_top _

end AlgebraicGeometry.Scheme.Hom
