/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Relative
public import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Locus
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.StalkMap

/-!
# Nodes on reduced inverse images of closed subschemes

The pointwise nodal condition uses a nodal neighborhood and excludes its smooth
locus. It is invariant on restriction to an open subscheme. In particular, nodes
of a reduced inverse image are preserved over the isomorphism locus of the map.
These statements let one move a nodal blowup center past a disjoint blowup.

The definition uses Tau Ceti's `AtWorstNodalOfRelativeDimensionOne`.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {C W S : Scheme.{u}}

/-- A node of a relative curve is a nonsmooth point on an open neighborhood that is
at worst nodal of relative dimension one. -/
def IsNodeAt (f : C ⟶ S) (x : C) : Prop :=
  ¬ (f.stalkMap x).hom.FormallySmooth ∧
    ∃ (V : Scheme.{u}) (i : V ⟶ C) (_ : IsOpenImmersion i) (z : V),
      i z = x ∧ AtWorstNodalOfRelativeDimensionOne (i ≫ f)

/-- On a nodal relative curve, its nodes are precisely its nonsmooth points. -/
theorem isNodeAt_iff_notMem_smoothLocus (f : C ⟶ S)
    (hf : AtWorstNodalOfRelativeDimensionOne f) (x : C) :
    let : SyntomicOfRelativeDimension 1 f := hf.syntomic
    f.IsNodeAt x ↔ x ∉ f.smoothLocus := by
  dsimp only
  have := hf.syntomic
  rw [mem_smoothLocus]
  exact ⟨And.left, fun hx ↦ ⟨hx, C, 𝟙 C, inferInstance, x, by simp, by simpa⟩⟩

/-- A point of the smooth locus is not a node. -/
theorem not_isNodeAt_of_mem_smoothLocus (f : C ⟶ S) [LocallyOfFinitePresentation f]
    {x : C} (hx : x ∈ f.smoothLocus) : ¬ f.IsNodeAt x :=
  fun h ↦ h.1 (f.mem_smoothLocus.mp hx)

/-- The node condition is invariant under passage to an open neighborhood. -/
theorem isNodeAt_comp_iff_of_isOpenImmersion (f : C ⟶ S) (j : W ⟶ C)
    [IsOpenImmersion j] (x : W) : (j ≫ f).IsNodeAt x ↔ f.IsNodeAt (j x) := by
  have hs := RingHom.FormallySmooth.respectsIso.stalkMap_comp_isOpenImmersion_iff j f x
  unfold IsNodeAt
  rw [hs]
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨V, i, _, z, hz, hn⟩
    exact ⟨V, i ≫ j, inferInstance, z, by simp [hz], by simpa only [Category.assoc] using hn⟩
  · rintro ⟨V, i, _, z, hz, hn⟩
    let p := pullback.fst j i
    let q := pullback.snd j i
    have hmem : x ∈ Set.range p := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨z, hz⟩
    obtain ⟨w, hw⟩ := hmem
    have hcomp : p ≫ j ≫ f = q ≫ i ≫ f := by
      rw [← Category.assoc, ← Category.assoc, pullback.condition]
    exact ⟨_, p, inferInstance, w, hw, hcomp.symm ▸ hn.comp_of_etale q⟩

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y S : Scheme.{u}}

/-- A closed subscheme ideal, after taking its radical, has a node at the specified
ambient point if the reduced subscheme has a node above that point. -/
def IsNodeOfReducedBoundary (D : Y.IdealSheafData) (g : Y ⟶ S) (x : Y) : Prop :=
  ∃ z : D.radical.subscheme, D.radical.subschemeι z = x ∧ (D.radical.subschemeι ≫ g).IsNodeAt z

/-- Taking the radical of the boundary ideal preserves its reduced node condition. -/
@[simp]
theorem isNodeOfReducedBoundary_radical (D : Y.IdealSheafData) (g : Y ⟶ S) (x : Y) :
    D.radical.IsNodeOfReducedBoundary g x ↔ D.IsNodeOfReducedBoundary g x := by
  unfold IsNodeOfReducedBoundary
  rw [← vanishingIdeal_support (I := D.radical), support_radical, vanishingIdeal_support]

/-- A node of the reduced boundary belongs to the support of the original boundary ideal. -/
theorem mem_support_of_isNodeOfReducedBoundary {D : Y.IdealSheafData} {g : Y ⟶ S} {x : Y}
    (hx : D.IsNodeOfReducedBoundary g x) : x ∈ D.support := by
  obtain ⟨z, rfl, _⟩ := hx
  rw [← SetLike.mem_coe, ← support_radical, ← range_subschemeι]
  exact Set.mem_range_self z

/-- For an already reduced boundary, the node condition can be read on the original
closed subscheme. -/
theorem isNodeOfReducedBoundary_iff_of_isReduced (D : Y.IdealSheafData) [IsReduced D.subscheme]
    (g : Y ⟶ S) (x : Y) :
    D.IsNodeOfReducedBoundary g x ↔
      ∃ z : D.subscheme, D.subschemeι z = x ∧ (D.subschemeι ≫ g).IsNodeAt z := by
  unfold IsNodeOfReducedBoundary
  rw [(D.isReduced_subscheme_iff_radical_eq).mp inferInstance]

/-- The node condition for the ideal of a closed immersion with reduced source can be read
on that source. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.isNodeOfReducedBoundary_ker_iff
    (i : X ⟶ Y) [IsClosedImmersion i] [IsReduced X] (g : Y ⟶ S) (y : Y) :
    i.ker.IsNodeOfReducedBoundary g y ↔ ∃ x : X, i x = y ∧ (i ≫ g).IsNodeAt x := by
  have : IsReduced i.ker.subscheme := isReduced_of_isOpenImmersion (asIso i.toImage).inv
  rw [isNodeOfReducedBoundary_iff_of_isReduced]
  have hcomp : i.toImage ≫ i.ker.subschemeι = i := i.toImage_imageι
  have heval (x : X) : i.ker.subschemeι (i.toImage x) = i x := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun f : X ⟶ Y ↦ f x) hcomp
  have hnode (x : X) :
      (i ≫ g).IsNodeAt x ↔ (i.ker.subschemeι ≫ g).IsNodeAt (i.toImage x) := by
    rw [← reassoc_of% hcomp]
    exact (i.ker.subschemeι ≫ g).isNodeAt_comp_iff_of_isOpenImmersion i.toImage x
  constructor
  · rintro ⟨z, hz, hn⟩
    obtain ⟨x, rfl⟩ := i.toImage.surjective z
    exact ⟨x, (heval x).symm.trans hz, (hnode x).mpr hn⟩
  · rintro ⟨x, hx, hn⟩
    exact ⟨i.toImage x, (heval x).trans hx, (hnode x).mp hn⟩

/-- If the reduced boundary is nodal, its nodes are its nonsmooth points read in the
ambient scheme. -/
theorem isNodeOfReducedBoundary_iff (D : Y.IdealSheafData) (g : Y ⟶ S)
    (h : AtWorstNodalOfRelativeDimensionOne (D.radical.subschemeι ≫ g)) (x : Y) :
    let : SyntomicOfRelativeDimension 1 (D.radical.subschemeι ≫ g) := h.syntomic
    D.IsNodeOfReducedBoundary g x ↔
      ∃ z : D.radical.subscheme, D.radical.subschemeι z = x ∧
        z ∉ (D.radical.subschemeι ≫ g).smoothLocus := by
  dsimp only
  exact exists_congr fun z ↦ and_congr_right fun _ ↦
    (D.radical.subschemeι ≫ g).isNodeAt_iff_notMem_smoothLocus h z

/-- Nodes of the reduced subscheme restrict to, and are detected on, open subschemes. -/
theorem isNodeOfReducedBoundary_comap_iff_of_isOpenImmersion
    (D : Y.IdealSheafData) (g : Y ⟶ S) (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    (D.comap f).IsNodeOfReducedBoundary (f ≫ g) x ↔ D.IsNodeOfReducedBoundary g (f x) :=
  exists_reducedBoundaryPoint_comap_iff_of_isOpenImmersion
    (fun {_} q z ↦ q.IsNodeAt z) Scheme.Hom.isNodeAt_comp_iff_of_isOpenImmersion D g f x

/-- A reduced inverse image has the same nodes over the isomorphism locus of the map. -/
theorem isNodeOfReducedBoundary_comap_iff_of_mem_isoLocus
    (D : Y.IdealSheafData) (g : Y ⟶ S) (f : X ⟶ Y) {x : X} (hx : f x ∈ f.isoLocus) :
    (D.comap f).IsNodeOfReducedBoundary (f ≫ g) x ↔ D.IsNodeOfReducedBoundary g (f x) :=
  exists_reducedBoundaryPoint_comap_iff_of_mem_isoLocus
    (fun {_} q z ↦ q.IsNodeAt z) Scheme.Hom.isNodeAt_comp_iff_of_isOpenImmersion D g f hx

end AlgebraicGeometry.Scheme.IdealSheafData
