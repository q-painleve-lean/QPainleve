/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Centre
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.ClosedImmersion.IsoLocus
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Exceptional curves disjoint from a contraction

An exceptional curve with closed image in the isomorphism locus of a morphism descends
to an exceptional curve with the same conormal bundle. For a contraction of one
exceptional curve, the other members of a disjoint configuration therefore remain
exceptional and pairwise disjoint. A subsequent contraction has the union of the two
centres and retains the scheme-theoretic fibres over previously contracted points.

This allows the single-curve contraction of the
[Stacks Project, Lemma 54.16.9](https://stacks.math.columbia.edu/tag/0C2N)
to be iterated on disjoint configurations.
-/

public section

open CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

variable {X Y : Scheme.{u}} {E : X.IdealSheafData}

/-- An exceptional curve with closed image in the isomorphism locus maps
isomorphically to an exceptional curve, and the square is cartesian. -/
theorem map_of_image_subset_isoLocus (hE : E.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) (hclosed : IsClosed (f '' (E.support : Set X)))
    (h : f '' (E.support : Set X) ⊆ f.isoLocus) :
    let J := E.map f
    J.IsExceptionalCurveOfFirstKind ∧
      IsIso (E.subschemeι ≫ f).toImage ∧
      IsPullback E.subschemeι (E.subschemeι ≫ f).toImage f J.subschemeι := by
  intro J
  let g := E.subschemeι ≫ f
  have hr : Set.range g = f '' (E.support : Set X) := by
    dsimp only [g]
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, E.range_subschemeι]
  have hU : Set.range g ⊆ f.isoLocus := hr.symm ▸ h
  have : IsClosedImmersion g :=
    E.subschemeι.isClosedImmersion_comp_of_range_subset_isoLocus f (hr.symm ▸ hclosed) hU
  have hpb : IsPullback E.subschemeι g.toImage f g.imageι :=
    E.subschemeι.isPullback_toImage_of_range_subset_isoLocus f hU
  have hcomap : g.ker.comap f = E := by
    simpa only [Scheme.Hom.imageι, ker_subschemeι] using
      (ker_eq_comap_of_isPullback g.imageι hpb).symm
  have hJ : (g.ker.support : Set Y) ⊆ f.isoLocus := by
    simpa only [g.support_ker, Closeds.coe_closure, g.isClosedMap.isClosed_range.closure_eq]
      using hU
  have hC : g.ker.IsEffectiveCartier :=
    (isEffectiveCartier_comap_iff_of_support_subset_isoLocus f hJ).mp
      (hcomap.symm ▸ hE.isEffectiveCartier)
  let eJ := asIso g.toImage
  have hcomp : eJ.hom ≫ g.imageι = E.subschemeι ≫ f := g.toImage_imageι
  have hIso : IsIso g.toImage := inferInstance
  refine ⟨?_, hIso, hpb⟩
  obtain ⟨hCE, κ, _, e, he⟩ := isExceptionalCurveOfFirstKind_iff_intersectionNumber.mp hE
  have hExceptional : g.ker.IsExceptionalCurveOfFirstKind := by
    refine isExceptionalCurveOfFirstKind_iff_intersectionNumber.mpr ⟨hC, κ, _, e ≪≫ eJ, ?_⟩
    have hclass := (hC.pullback_mk_toInvertibleSheaf (hcomap.symm ▸ hCE)).trans
      (LineBundleClass.mk_toInvertibleSheaf_congr _ hCE hcomap)
    rw [Iso.trans_hom, Category.assoc, hcomp,
      ← Category.assoc, ← LineBundleClass.intersectionNumber_pullback,
      LineBundleClass.pullback_inv, hclass, he]
  exact hExceptional

/-- An exceptional curve disjoint from the inverse image of the centre of a proper morphism
descends to an exceptional curve. Its ideal pulls back to the original ideal, and its
support lies in the isomorphism locus. -/
theorem map_of_disjoint_contraction (hE : E.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) [IsProper f]
    (hd : Disjoint (E.support : Set X) (f ⁻¹' f.centre)) :
    (E.map f).IsExceptionalCurveOfFirstKind ∧ (E.map f).comap f = E ∧
      ((E.map f).support : Set Y) ⊆ f.isoLocus := by
  have h : f '' (E.support : Set X) ⊆ f.isoLocus := by
    rw [← f.compl_centre]
    rintro _ ⟨x, hx, rfl⟩
    exact fun hp ↦ Set.disjoint_left.mp hd hx hp
  have hclosed := f.isClosedMap _ E.support.isClosed
  obtain ⟨hE', _, hpb⟩ := hE.map_of_image_subset_isoLocus f hclosed h
  refine ⟨hE', ?_, ?_⟩
  · simpa only [ker_subschemeι] using
      (ker_eq_comap_of_isPullback (E.map f).subschemeι hpb).symm
  · simpa only [support_map, Closeds.coe_closure, hclosed.closure_eq] using h

/-- Contracting one member of a pairwise disjoint configuration preserves the remaining
configuration, with the original scheme-theoretic pullbacks at all surviving labels. -/
theorem map_pairwise_disjoint_of_contraction {ι : Type*} (C : ι → X.IdealSheafData) (i₀ : ι)
    (hC : ∀ i, (C i).IsExceptionalCurveOfFirstKind) (f : X ⟶ Y) [IsModification f] {p : Y}
    (hc : f.centre = {p}) (hF : (Y.fromSpecResidueField p).ker.comap f = C i₀)
    (hpair : Pairwise fun i j ↦ Disjoint ((C i).support : Set X) (C j).support) :
    let C' (i : {i // i ≠ i₀}) := (C i).map f
    (∀ i, (C' i).IsExceptionalCurveOfFirstKind ∧ (C' i).comap f = C i ∧
      p ∉ (C' i).support) ∧
    Pairwise fun i j ↦ Disjoint ((C' i).support : Set Y) (C' j).support := by
  have hp : IsClosed ({p} : Set Y) := hc ▸ f.isClosed_centre
  have hpre : ((C i₀).support : Set X) = f ⁻¹' f.centre := by
    rw [← hF, support_comap, Closeds.coe_preimage,
      Scheme.support_ker_fromSpecResidueField_of_isClosed hp, hc]
  have h' (i : {i // i ≠ i₀}) := (hC i).map_of_disjoint_contraction f
    (hpre ▸ hpair i.property)
  refine ⟨fun i ↦ ⟨(h' i).1, (h' i).2.1, ?_⟩, ?_⟩
  · intro hi
    have hi' := (h' i).2.2 hi
    rw [← f.compl_centre, hc] at hi'
    exact hi' (Set.mem_singleton p)
  · intro i j hij
    apply Disjoint.of_preimage f.surjective
    rw [← Closeds.coe_preimage _ f.continuous, ← support_comap, (h' i).2.1,
      ← Closeds.coe_preimage _ f.continuous, ← support_comap, (h' j).2.1]
    exact hpair fun h ↦ hij (Subtype.ext h)

/-- A further contraction of a disjoint exceptional curve adds one point to the centre
and preserves all previous scheme-theoretic fibres over closed points. The new fibre
pulls back to the original curve on the source of the composite. -/
theorem comp_of_disjoint_contraction (hE : E.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) [IsModification f] [IsReduced Y]
    (hd : Disjoint (E.support : Set X) (f ⁻¹' f.centre))
    {Z : Scheme.{u}} (g : Y ⟶ Z) [IsModification g] {q : Z}
    (hg : g.centre = {q}) (hF : (Z.fromSpecResidueField q).ker.comap g = E.map f) :
    (f ≫ g).centre = insert q (g '' f.centre) ∧
      q ∉ g '' f.centre ∧ Set.InjOn g f.centre ∧
      (Z.fromSpecResidueField q).ker.comap (f ≫ g) = E ∧
      ∀ p ∈ f.centre, IsClosed ({p} : Set Y) → IsClosed ({g p} : Set Z) ∧
        (Z.fromSpecResidueField (g p)).ker.comap (f ≫ g) =
          (Y.fromSpecResidueField p).ker.comap f := by
  obtain ⟨_, hE', hU⟩ := hE.map_of_disjoint_contraction f hd
  have hq : IsClosed ({q} : Set Z) := hg ▸ g.isClosed_centre
  have hpre : ((E.map f).support : Set Y) = g ⁻¹' {q} := by
    rw [← hF, support_comap, Closeds.coe_preimage,
      Scheme.support_ker_fromSpecResidueField_of_isClosed hq]
  have haway {p : Y} (hp : p ∈ f.centre) : g p ∈ (g.isoLocus : Set Z) := by
    rw [← g.compl_centre, hg, Set.mem_compl_iff]
    intro hpq
    have hpE : p ∈ ((E.map f).support : Set Y) := hpre.symm ▸ hpq
    have := hU hpE
    rw [← f.compl_centre] at this
    exact this hp
  refine ⟨?_, ?_, fun _ hp _ hp' ↦ g.injOn_preimage_isoLocus
    (haway hp) (haway hp'), ?_, ?_⟩
  · rw [f.centre_comp g, hg, Set.singleton_union]
  · rintro ⟨p, hp, rfl⟩
    have := haway hp
    rw [← g.compl_centre, hg] at this
    exact this (Set.mem_singleton (g p))
  · rw [comap_comp, hF, hE']
  · intro p hp hpclosed
    have hclosed : IsClosed ({g p} : Set Z) := by
      simpa only [Set.image_singleton] using g.isClosedMap {p} hpclosed
    exact ⟨hclosed, by
      rw [comap_comp, g.comap_ker_fromSpecResidueField_of_mem_isoLocus hclosed (haway hp)]⟩

end AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
