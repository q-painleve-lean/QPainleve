/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Automorphism
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint

import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Smooth
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Component
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.Blowup.Restriction

/-!
# Boundary components under ordered blowup lifts

For an automorphism lifting through a specified tower of closed point blowups, fixing the
boundary components is equivalent on the base and on the blown-up surface. Each new
exceptional prime is fixed by the ordered lift, and every other prime can be compared over
the isomorphism locus. Combined with Picard descent, this gives a unique descended
automorphism fixing the original boundary components, including for a tower of nodal blowups.
The Picard descent is supplied by
`IsClosedPointTower.existsUnique_isLift_over_of_picard_trivial` and the exceptional generic
point is supplied by `IsEffectiveCartier.mem_support_iff_eq_subschemeι_genericPoint`.

This is the comparison of boundary components in the toric blowup reduction of
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*, Proposition 2.6](
https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower

variable {k : Type u} [Field k] [PerfectField k]
  {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}
  (s : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 s]

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

omit [PerfectField k] in
include s in
private theorem fixes_codimensionOne_preimage_blowup_iff {p : X} (hp : IsClosed ({p} : Set X))
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

include s in
/-- An ordered lift through a closed point blowup tower fixes all codimension-one points
supported on the reduced total transform exactly when the base isomorphism fixes all
codimension-one points supported on the original boundary. -/
theorem IsLift.fixes_boundary_components_iff (hT : IsClosedPointTower X T)
    {e : X ≅ X} {g : Y ≅ Y} (hg : IsLift e T T g) (D : X.IdealSheafData) :
    (∀ y : CodimensionOnePoint Y, (y : Y) ∈ (D.comap T.toBase).support → g.hom y = y) ↔
      ∀ x : CodimensionOnePoint X, (x : X) ∈ D.support → e.hom x = x := by
  induction hT with
  | nil =>
    rw [IsLift.nil_iff.mp hg, toBase_nil, comap_id]
  | @snoc m W U I hU p hp hI ih =>
    obtain ⟨f, hf, hcenter, rfl⟩ := IsLift.snoc_iff.mp hg
    have := hU.smoothOfRelativeDimension s
    rw [← ih hf, toBase_snoc, comap_comp]
    simpa only [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage] using
      fixes_codimensionOne_preimage_blowup_iff (U.toBase ≫ s) hp hI f hcenter
        ((D.comap U.toBase).support : Set W)

namespace IsClosedPointTower

variable [IsIntegral X] [IsNoetherian X] {D : X.IdealSheafData}

/-- An automorphism fixing the Picard group and all components of the reduced total
boundary descends through the specified closed point blowups to a unique automorphism
over the field. The descended automorphism fixes the Picard group, the reduced boundary
ideal and each boundary component on the original surface. -/
theorem existsUnique_isLift_over_fixing_boundary_of_picard_trivial
    (hT : IsClosedPointTower X T) (hD : D.IsEffectiveCartier)
    (g : Y ≅ Y) (hgPic : ∀ a, LineBundleClass.pullback g.hom a = a)
    (hgOver : g.hom ≫ T.toBase ≫ s = T.toBase ≫ s)
    (hgD : ∀ y : CodimensionOnePoint Y, (y : Y) ∈ (D.comap T.toBase).support → g.hom y = y) :
    ∃! e : X ≅ X, IsLift e T T g ∧ (∀ a, LineBundleClass.pullback e.hom a = a) ∧
      e.hom ≫ s = s ∧ D.radical.comap e.hom = D.radical ∧
      ∀ x : CodimensionOnePoint X, (x : X) ∈ D.support → e.hom x = x := by
  obtain ⟨e, ⟨he, hePic, heOver⟩, huniq⟩ :=
    hT.existsUnique_isLift_over_of_picard_trivial s g hgPic hgOver
  have hfix := (he.fixes_boundary_components_iff s hT D).mp hgD
  exact ⟨e, ⟨he, hePic, heOver, hD.comap_radical_eq_of_fixes_components e hfix, hfix⟩,
    fun a ha ↦ huniq a ⟨ha.1, ha.2.1, ha.2.2.1⟩⟩

end IsClosedPointTower
end QPainleve.BlowupTower
