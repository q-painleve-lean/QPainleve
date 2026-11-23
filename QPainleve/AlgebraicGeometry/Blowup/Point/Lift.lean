/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Factorization
public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.IsoLocus

/-!
# The center below matched exceptional curves

In a commuting square of point blowups, a lift that identifies the two exceptional
curves of the first kind forces the original modification to be an isomorphism over
the target center. This excludes such a lift at a center where the original morphism
fails to be an isomorphism.

## References

* [The Stacks Project, Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R).
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

open IdealSheafData

universe u

variable {X Y : Scheme.{u}} {p : X} {q : Y}

local notation "Iₚ" => vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)
local notation "I_q" => vanishingIdeal (Closeds.mk (closure (Set.singleton q)) isClosed_closure)
local notation "πₚ" => blowupToBase Iₚ
local notation "π_q" => blowupToBase I_q
local notation "Eₚ" => IdealSheafData.comap Iₚ πₚ
local notation "E_q" => IdealSheafData.comap I_q π_q

/-- If a lift of a modification between closed point blowups identifies their exceptional
curves of the first kind, the original modification is an isomorphism near the target
center. Both comparisons take place on the native blowups and retain the given maps. -/
theorem mem_isoLocus_of_exceptional_curve_isomorphism [IsReduced X] [IsIntegral Y]
    [IsNormalScheme Y] (f : X ⟶ Y) [IsModification f]
    (hp : IsClosed ({p} : Set X)) (hq : IsClosed ({q} : Set Y))
    [Surjective πₚ] [IsReduced (Iₚ).blowup] [IsIntegral (I_q).blowup]
    [IsLocallyNoetherian (I_q).blowup] [IsNormalScheme (I_q).blowup]
    (g : (Iₚ).blowup ⟶ (I_q).blowup) [IsModification g] (hg : g ≫ π_q = πₚ ≫ f)
    (hE : (Eₚ).IsExceptionalCurveOfFirstKind) (hF : (E_q).IsExceptionalCurveOfFirstKind)
    (e : (Eₚ).subscheme ≅ (E_q).subscheme)
    (he : (Eₚ).subschemeι ≫ g = e.hom ≫ (E_q).subschemeι) :
    q ∈ f.isoLocus := by
  have hU := hE.support_subset_isoLocus hF g e he
  have hfiber := f.preimage_singleton_eq_of_exceptionalCurve_isoLocus hp hq g hg e.hom he hU
  exact f.mem_isoLocus_of_finite_preimage_singleton q (hfiber.symm ▸ Set.finite_singleton p)

end AlgebraicGeometry.Scheme.Hom
