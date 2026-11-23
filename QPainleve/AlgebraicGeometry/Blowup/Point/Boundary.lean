/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import QPainleve.AlgebraicGeometry.Blowup.Isomorphism
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint

import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Smooth
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Boundary components under a point blowup lift

Over the center, the lift fixes the unique generic point of the exceptional divisor.
Away from the center, the blowup projection identifies the codimension-one points on
the two surfaces.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace QPainleve

variable {X : Scheme.{u}}

private theorem eq_of_same_exceptional_prime {I : X.IdealSheafData}
    (hN : IsLocallyNoetherian I.blowup) (hE : (I.comap I.blowupToBase).IsEffectiveCartier)
    [IsIntegral (I.comap I.blowupToBase).subscheme] {p : X} (hI : (I.support : Set X) = {p})
    (g : I.blowup ≅ I.blowup) (y : CodimensionOnePoint I.blowup)
    (hy : I.blowupToBase y = p) (hgy : I.blowupToBase (g.hom y) = I.blowupToBase y) :
    g.hom y = y := by
  have hmem {z : I.blowup} (hz : I.blowupToBase z = p) :
      z ∈ (I.comap I.blowupToBase).support := by
    simpa only [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, hI,
      Set.mem_preimage, Set.mem_singleton_iff] using hz
  have hiso : g.hom y ∈ g.hom.isoLocus := by
    rw [(g.hom.isoLocus_eq_top_iff).mpr inferInstance]
    exact Opens.mem_top _
  have hheight := (g.hom.coheight_eq_of_apply_mem_isoLocus hiso).trans y.property
  exact ((hE.mem_support_iff_eq_subschemeι_genericPoint hheight).mp (hmem (hgy.trans hy))).trans
    ((hE.mem_support_iff_eq_subschemeι_genericPoint y.property).mp (hmem hy)).symm

variable {k : Type u} [Field k]
  (s : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 s]

include s in
/-- The lift of a center-preserving automorphism to the blowup of a closed point
on a smooth surface fixes every codimension-one point lying over a subset exactly
when the base automorphism fixes every codimension-one point in that subset. -/
theorem fixes_codimensionOne_preimage_blowup_iff {p : X} (hp : IsClosed ({p} : Set X))
    {I : X.IdealSheafData} (hI : I = (X.fromSpecResidueField p).ker)
    (e : X ≅ X) (hcenter : I.comap e.hom = I) (B : Set X) :
    (∀ y : CodimensionOnePoint I.blowup, I.blowupToBase y ∈ B →
      (I.blowupIso e hcenter).hom y = y) ↔
      ∀ x : CodimensionOnePoint X, (x : X) ∈ B → e.hom x = x := by
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 s
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsRegularLocalRing (X.presheaf.stalk p) := isRegularLocalRing_stalk_of_smooth s p
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq s 2).mp inferInstance).2 p hp
  let π := I.blowupToBase
  let g := I.blowupIso e hcenter
  have hsupport : (I.support : Set X) = {p} := by
    rw [hI, Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hp.closure_eq]
  have he : e.hom p = p := by
    have hm : p ∈ I.support := by simp only [← SetLike.mem_coe, hsupport, Set.mem_singleton_iff]
    have hh : p ∈ (I.comap e.hom).support := by rw [hcenter]; exact hm
    simpa only [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, hsupport, Set.mem_preimage,
      Set.mem_singleton_iff] using hh
  have hcomm (y : I.blowup) : π (g.hom y) = e.hom (π y) := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun f : I.blowup ⟶ X ↦ f y) (I.blowupIso_hom_blowupToBase e hcenter)
  have hiso {x : X} (hx : x ≠ p) : x ∈ π.isoLocus :=
    (π.le_isoLocus_iff.mpr (I.isIso_blowupToBase_restrict_compl_support))
      (by simpa only [← SetLike.mem_coe, Closeds.coe_compl, hsupport, Set.mem_compl_iff,
        Set.mem_singleton_iff] using hx)
  have hvanish := hI.trans (X.ker_fromSpecResidueField_eq_vanishingIdeal p)
  have : Surjective I.blowupToBase := by
    rw [hvanish]
    exact surjective_blowupToBase_point hp hdim
  constructor
  · intro h x hx
    have hne : (x : X) ≠ p := by
      intro heq
      have htwo := coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) s hp
      rw [← heq, x.property] at htwo
      exact (by decide : (1 : ℕ∞) ≠ 2) htwo
    obtain ⟨y, hy⟩ := π.surjective x
    have hcodim := (π.coheight_eq_of_apply_mem_isoLocus (hy ▸ hiso hne)).symm
    let z : CodimensionOnePoint I.blowup := ⟨y, hcodim.trans (hy ▸ x.property)⟩
    exact (congrArg e.hom hy).symm.trans
      ((hcomm y).symm.trans ((congrArg π (h z (hy ▸ hx))).trans hy))
  · intro h y hy
    by_cases hj : π y = p
    · have : IsIntegral (I.comap I.blowupToBase).subscheme := by
        rw [hvanish]
        exact isIntegral_exceptional_blowup_closed_point hdim hp
      have hcomm' : π (g.hom y) = π y := (hcomm y).trans (by rw [hj, he])
      exact eq_of_same_exceptional_prime (LocallyOfFiniteType.isLocallyNoetherian π)
        I.isEffectiveCartier_comap_blowupToBase hsupport g y hj hcomm'
    · have hπ := hiso hj
      let x : CodimensionOnePoint X :=
        ⟨π y, (π.coheight_eq_of_apply_mem_isoLocus hπ).trans y.property⟩
      have hh : π (g.hom y) = π y := (hcomm y).trans (h x hy)
      have hi : π (g.hom y) ∈ π.isoLocus := by rwa [hh]
      exact π.injOn_preimage_isoLocus hi hπ hh

end QPainleve
