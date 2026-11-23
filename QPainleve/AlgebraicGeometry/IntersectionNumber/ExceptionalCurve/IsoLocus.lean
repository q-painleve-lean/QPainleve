/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Comparison
public import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus

import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import TauCeti.AlgebraicGeometry.Birational.Irreducible
import TauCeti.AlgebraicGeometry.Morphisms.Dominant

/-!
# Isomorphism loci along matched exceptional curves

If a proper birational morphism identifies two exceptional curves of the first kind,
its isomorphism locus contains the whole target curve. The generic point of the
target curve has codimension one. The corresponding isomorphism of ambient local
rings identifies the two generic stalk ideals with their maximal ideals.

## References

* [The Stacks Project, Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R).
-/

public section

open CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

/-- If a modification with reduced source and locally Noetherian normal integral target
identifies two exceptional curves of the first kind, its isomorphism locus contains the
target curve. -/
theorem support_subset_isoLocus {X Y : Scheme} [IsReduced X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormalScheme Y] {E : X.IdealSheafData} {F : Y.IdealSheafData}
    (hE : E.IsExceptionalCurveOfFirstKind) (hF : F.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) [IsModification f] (e : E.subscheme ≅ F.subscheme)
    (he : E.subschemeι ≫ f = e.hom ≫ F.subschemeι) :
    (F.support : Set Y) ⊆ f.isoLocus := by
  let := hE.isIntegral_subscheme
  let := hF.isIntegral_subscheme
  let z := genericPoint E.subscheme
  let x := E.subschemeι z
  have hpoint (w : E.subscheme) : f (E.subschemeι w) = F.subschemeι (e.hom w) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun a : E.subscheme ⟶ Y ↦ a w) he
  have hη : f x = F.subschemeι (genericPoint F.subscheme) :=
    (hpoint z).trans (congrArg F.subschemeι e.hom.genericPoint_eq_of_isDominant)
  have hx : f x ∈ f.isoLocus := by
    rw [hη]
    exact f.mem_isoLocus_of_coheight_eq_one hF.isEffectiveCartier.coheight_subschemeι_genericPoint
  let x' : (f ⁻¹ᵁ f.isoLocus).toScheme := ⟨x, f.mem_preimage.mpr hx⟩
  have hstalk : IsIso (f.stalkMap x) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (morphismRestrictStalkMap f f.isoLocus x')).mp inferInstance
  have hmax : F.stalkIdeal (f x) = IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)) := by
    rw [hη, F.stalkIdeal_subschemeι_genericPoint]
  have hstalkIdeal : (F.comap f).stalkIdeal x = E.stalkIdeal x := by
    rw [F.stalkIdeal_comap, hmax, E.stalkIdeal_subschemeι_genericPoint]
    exact IsLocalRing.map_maximalIdeal_of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
  have : IrreducibleSpace X := (IsModification.birational f).irreducibleSpace
  have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  have hCartier := hF.isEffectiveCartier.comap_of_isDominant f
  rw [← F.range_subschemeι]
  rintro _ ⟨w, rfl⟩
  have hw := f.mem_isoLocus_of_quasiFiniteAt
    (hE.quasiFiniteAt_of_exceptional_curve_isomorphism hF f hCartier e he z hstalkIdeal (e.inv w))
  simpa only [SetLike.mem_coe, hpoint, Scheme.inv_hom_apply] using hw

end AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
