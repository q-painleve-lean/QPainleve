/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Morphisms.Pullback.IsoLocus
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Fibers below matched exceptional curves

When a lift between point blowups identifies the exceptional subschemes and is an isomorphism
over the target exceptional subscheme, the entire fiber downstairs consists of the source
center. In point-blowup factorization this provides the finite fiber used to exclude the
case where the terminal source exceptional curve dominates the target exceptional curve.

## References

* [The Stacks Project, Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R).
-/

public section

open CategoryTheory TopologicalSpace

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

/-- In a commuting square of closed point blowups, suppose the source projection is
surjective and the top morphism identifies the exceptional subschemes. If the target
exceptional subscheme lies in the top morphism's isomorphism locus, the fiber of the
bottom morphism over the target center consists exactly of the source center. -/
theorem preimage_singleton_eq_of_exceptionalCurve_isoLocus
    (f : X ⟶ Y) (hp : IsClosed ({p} : Set X)) (hq : IsClosed ({q} : Set Y))
    [Surjective πₚ]
    (g : (Iₚ).blowup ⟶ (I_q).blowup) (hg : g ≫ π_q = πₚ ≫ f)
    (e : (Eₚ).subscheme ⟶ (E_q).subscheme) [IsIso e]
    (he : (Eₚ).subschemeι ≫ g = e ≫ (E_q).subschemeι)
    (hU : ((E_q).support : Set (I_q).blowup) ⊆ g.isoLocus) :
    f ⁻¹' {q} = {p} := by
  have hpb := g.isPullback_of_isIso_of_range_subset_isoLocus
    (Eₚ).subschemeι e (E_q).subschemeι he ((E_q).range_subschemeι.symm ▸ hU)
  have hE : (E_q).comap g = Eₚ := by
    simpa only [ker_subschemeι] using (ker_eq_comap_of_isPullback _ hpb).symm
  have hpre : g ⁻¹' (π_q ⁻¹' {q}) = πₚ ⁻¹' {p} := by
    have hs := congrArg (fun I : (Iₚ).blowup.IdealSheafData ↦ (I.support : Set (Iₚ).blowup)) hE
    rw [support_comap, Closeds.coe_preimage] at hs
    rwa [← range_subschemeι_comap_pointBlowup hq, ← range_subschemeι_comap_pointBlowup hp,
      range_subschemeι, range_subschemeι]
  apply (πₚ).surjective.preimage_injective
  calc
    πₚ ⁻¹' (f ⁻¹' {q}) = g ⁻¹' (π_q ⁻¹' {q}) := by
      rw [← Set.preimage_comp, ← Set.preimage_comp, ← TopCat.coe_comp, ← TopCat.coe_comp,
        ← Scheme.Hom.comp_base, ← Scheme.Hom.comp_base, hg]
    _ = πₚ ⁻¹' {p} := hpre

end AlgebraicGeometry.Scheme.Hom
