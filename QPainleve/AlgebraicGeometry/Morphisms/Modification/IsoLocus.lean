/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
public import QPainleve.AlgebraicGeometry.Morphisms.Separated
public import QPainleve.AlgebraicGeometry.SpreadingOut
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Centre
public import TauCeti.AlgebraicGeometry.Scheme.Normal

import Mathlib.AlgebraicGeometry.Noetherian
import QPainleve.AlgebraicGeometry.Normalization.Lift
import QPainleve.Topology.KrullDimension
import QPainleve.Topology.NoetherianSpace
import TauCeti.AlgebraicGeometry.Birational.Irreducible
import TauCeti.AlgebraicGeometry.Normalization.Basic
import TauCeti.Topology.KrullDimension.Basic

/-!
# Isomorphism loci of proper birational morphisms

A modification with reduced source is an isomorphism at the valuation-ring stalks of its
integral target. If the target is normal, its isomorphism locus is the image of its quasi-finite
locus. For surfaces the centre is a finite set of closed points. These are the isomorphism and
finiteness criteria used to choose point blowups in a factorization of a proper birational morphism.

The proof uses Tau Ceti's `Scheme.Hom.isoLocus` and `Scheme.Hom.normalizationMap`, together with
Mathlib's relative form of Zariski's main theorem.

## References

* [The Stacks Project, Lemma 33.17.3](https://stacks.math.columbia.edu/tag/0BFP).
* [The Stacks Project, Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R).
-/

public section

open CategoryTheory Limits Order TopologicalSpace TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A modification induces an isomorphism of function fields. -/
theorem isIso_functionFieldMap_of_isModification [IrreducibleSpace X] [IrreducibleSpace Y]
    [IsModification f] : IsIso f.functionFieldMap := by
  obtain ⟨U, _, hpre, hIso⟩ := IsModification.exists_isIso_morphismRestrict (f := f)
  obtain ⟨x, hx⟩ := hpre.nonempty
  have hη : genericPoint X ∈ f ⁻¹ᵁ U :=
    (genericPoint_specializes x).mem_open (f ⁻¹ᵁ U).isOpen hx
  have := f.isIso_stalkMap_of_mem_isoLocus (f.le_isoLocus_iff.mpr hIso (f.mem_preimage.mp hη))
  infer_instance

/-- A modification cancels from the right of two dominant morphisms from a reduced,
irreducible scheme. -/
theorem eq_of_comp_eq_of_isModification {W : Scheme.{u}} [IsReduced W] [IrreducibleSpace W]
    [IrreducibleSpace Y] [IsModification f] {g h : W ⟶ X}
    [IsDominant g] [IsDominant h] (he : g ≫ f = h ≫ f) : g = h := by
  have : IrreducibleSpace X := (IsModification.birational f).irreducibleSpace
  have : IsIso f.functionFieldMap := f.isIso_functionFieldMap_of_isModification
  let : X.Over Y := ⟨f⟩
  let : W.Over Y := ⟨g ≫ f⟩
  have : g.IsOver Y := ⟨rfl⟩
  have : h.IsOver Y := ⟨he.symm⟩
  have : IsSeparated (X ↘ Y) := inferInstanceAs (IsSeparated f)
  apply Scheme.Hom.ext_of_functionFieldMap_eq Y
  apply (cancel_epi f.functionFieldMap).mp
  simp only [← Scheme.Hom.functionFieldMap_comp, he]

/-- A modification with irreducible target has a dominant section over the generic point
of the target. -/
theorem exists_dominant_generic_section [IrreducibleSpace Y] [IsModification f] :
    ∃ s : Spec Y.functionField ⟶ X,
      s ≫ f = Y.fromSpecStalk (genericPoint Y) ∧ IsDominant s := by
  obtain ⟨U, hU, hpre, hIso⟩ := IsModification.exists_isIso_morphismRestrict (f := f)
  obtain ⟨z, hz⟩ := hU.nonempty
  have hη : genericPoint Y ∈ U := (genericPoint_specializes z).mem_open U.isOpen hz
  let s := U.fromSpecStalkOfMem (genericPoint Y) hη ≫ inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι
  have hs : s ≫ f = Y.fromSpecStalk (genericPoint Y) := by
    simp [s, ← morphismRestrict_ι]
  have : IsDominant (f ⁻¹ᵁ U).ι := Opens.isDominant_ι hpre
  have : IsDominant (U.fromSpecStalkOfMem (genericPoint Y) hη ≫ U.ι) := by
    rw [Opens.fromSpecStalkOfMem_ι]
    infer_instance
  have : IsDominant (U.fromSpecStalkOfMem (genericPoint Y) hη) :=
    IsDominant.of_comp_of_isOpenImmersion _ U.ι
  have : IsDominant s := inferInstanceAs (IsDominant (_ ≫ inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι))
  exact ⟨s, hs, ‹IsDominant s›⟩

/-- A modification of integral schemes is an isomorphism near any point of the target
whose local ring is a valuation ring. -/
theorem mem_isoLocus_of_valuationRing [IsReduced X] [IsIntegral Y] [IsModification f]
    (y : Y) [ValuationRing (Y.presheaf.stalk y)] : y ∈ f.isoLocus := by
  obtain ⟨s, hs, hdom⟩ := f.exists_dominant_generic_section
  obtain ⟨V, hy, g, hg, hdom'⟩ := f.exists_dominant_section_over_open_of_valuationRing y s hs
  exact f.le_isoLocus_of_dominant_section g hg hy

/-- The relative normalization along a modification of integral schemes with normal target
is isomorphic to the target. -/
theorem isIso_fromNormalization_of_isModification [IsReduced X] [IsIntegral Y]
    [IsNormalScheme Y] [IsModification f] : IsIso f.fromNormalization := by
  let g := Y.fromSpecStalk (genericPoint Y)
  have hg : IsIso g.fromNormalization := Y.isIso_fromNormalization_fromSpecStalk_genericPoint
  obtain ⟨s, hs, hdom⟩ := f.exists_dominant_generic_section
  let m := g.normalizationMap f s hs
  have hcomp : g.toNormalization ≫ m = s ≫ f.toNormalization :=
    g.toNormalization_normalizationMap f s hs
  have : IsDominant (g.toNormalization ≫ m) :=
    hcomp.symm ▸ inferInstanceAs (IsDominant (s ≫ f.toNormalization))
  have : IsDominant m := IsDominant.of_comp g.toNormalization m
  refine f.fromNormalization.isIso_of_dominant_section (inv g.fromNormalization ≫ m) ?_
  rw [Category.assoc, g.normalizationMap_fromNormalization, IsIso.inv_hom_id]

/-- A modification of integral schemes with normal target is an isomorphism over a
neighbourhood of any point with a quasi-finite point in its fibre. -/
theorem mem_isoLocus_of_quasiFiniteAt [IsReduced X] [IsIntegral Y] [IsNormalScheme Y]
    [IsModification f] {x : X} (hx : f.QuasiFiniteAt x) : f x ∈ f.isoLocus := by
  let U := f.quasiFiniteLocus
  let g := U.ι ≫ f
  have := f.isIso_fromNormalization_of_isModification
  have : IsOpenImmersion g := by
    have h : g = (U.ι ≫ f.toNormalization) ≫ f.fromNormalization := by
      simp [g]
    have hOpen : IsOpenImmersion ((U.ι ≫ f.toNormalization) ≫ f.fromNormalization) :=
      inferInstance
    exact h.symm ▸ hOpen
  have := (IsModification.birational f).irreducibleSpace
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨x, f.mem_quasiFiniteLocus.mpr hx⟩)
  let s := g.isoOpensRange.inv ≫ U.ι
  have hs : s ≫ f = g.opensRange.ι := by
    simpa only [s, Category.assoc] using g.isoOpensRange_inv_comp
  have hy : f x ∈ g.opensRange := ⟨⟨x, f.mem_quasiFiniteLocus.mpr hx⟩, rfl⟩
  exact f.le_isoLocus_of_dominant_section s hs hy

section Normal

variable [IsReduced X] [IsIntegral Y] [IsNormalScheme Y] [IsModification f]

/-- A proper birational morphism to a normal integral scheme is an isomorphism over a
neighbourhood of a point exactly when the fibre contains a quasi-finite point. -/
theorem mem_isoLocus_iff_exists_quasiFiniteAt {y : Y} :
    y ∈ f.isoLocus ↔ ∃ x : X, f x = y ∧ f.QuasiFiniteAt x := by
  constructor
  · intro hy
    have : Surjective f := inferInstance
    obtain ⟨x, rfl⟩ := f.surjective y
    exact ⟨x, rfl, f.quasiFiniteAt_of_mem_isoLocus hy⟩
  · rintro ⟨x, rfl, hx⟩
    exact f.mem_isoLocus_of_quasiFiniteAt hx

/-- A finite fibre of a modification with normal integral target lies over the
isomorphism locus. -/
theorem mem_isoLocus_of_finite_preimage_singleton (y : Y) (hy : (f ⁻¹' {y}).Finite) :
    y ∈ f.isoLocus := by
  obtain ⟨x, rfl⟩ := f.surjective y
  have : Finite (f.fiber (f x)) := (f.fiberHomeo (f x)).finite_iff.mpr hy
  exact f.mem_isoLocus_of_quasiFiniteAt
    (quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _))

/-- Every codimension-one point of a locally Noetherian normal target belongs to the
isomorphism locus of a modification with reduced source. -/
theorem mem_isoLocus_of_coheight_eq_one [IsLocallyNoetherian Y] {y : Y} (hy : coheight y = 1) :
    y ∈ f.isoLocus := by
  have := IsNormalScheme.isDiscreteValuationRing_stalk y hy
  exact f.mem_isoLocus_of_valuationRing y

/-- On a normal locally Noetherian integral scheme of dimension at most two, the centre of a
modification with reduced source consists of closed points. -/
theorem centre_subset_closedPoints [IsLocallyNoetherian Y] (hY : topologicalKrullDim Y ≤ 2) :
    f.centre ⊆ closedPoints Y := by
  intro y hy
  have hnot : y ∉ f.isoLocus := by
    simpa only [f.centre_def, Set.mem_compl_iff, SetLike.mem_coe] using hy
  have hcodim0 : coheight y ≠ 0 := by
    intro h
    have he := Scheme.eq_genericPoint_of_isMax (coheight_eq_zero.mp h)
    obtain ⟨z, hz⟩ := (IsModification.dense_isoLocus f).nonempty
    exact hnot (he ▸ (genericPoint_specializes z).mem_open f.isoLocus.isOpen hz)
  have hcodim1 : coheight y ≠ 1 := fun h ↦ hnot (f.mem_isoLocus_of_coheight_eq_one h)
  have hy2 : 2 ≤ coheight y :=
    (ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mpr
      (lt_of_le_of_ne (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hcodim0)) hcodim1.symm)
  exact mem_closedPoints_iff.mpr
    (QPainleve.isClosed_singleton_of_le_coheight_of_topologicalKrullDim_le hY hy2)

/-- The centre of a proper birational morphism to a normal Noetherian integral surface is
a finite set of closed points. -/
theorem finite_centre [IsNoetherian Y] (hY : topologicalKrullDim Y ≤ 2) :
    f.centre.Finite :=
  f.isClosed_centre.finite_of_subset_closedPoints (f.centre_subset_closedPoints hY)

end Normal

end AlgebraicGeometry.Scheme.Hom
