/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Relative
public import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra

import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Locus
import QPainleve.AlgebraicGeometry.Scheme.Stalk
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Etale
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Smooth
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
import TauCeti.AlgebraicGeometry.Pullback.Carrier
import TauCeti.AlgebraicGeometry.Scheme.LocalSpectrum

/-!
# The nodal locus of a relative curve

The pointwise nodal condition uses a nodal neighborhood and excludes its smooth
locus. It is invariant on restriction to an open subscheme. In particular, nodes
of a reduced inverse image are preserved over the isomorphism locus of the map.
These statements let one move a nodal blowup center past a disjoint blowup.

On a syntomic curve over a field, a reduced-point stalk of the singular subscheme
with separable residue field detects a node.

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

/-- The stalk map at a node is not formally smooth. -/
theorem IsNodeAt.not_formallySmooth_stalkMap {f : C ⟶ S} {x : C} (h : f.IsNodeAt x) :
    ¬ (f.stalkMap x).hom.FormallySmooth :=
  h.1

/-- A node lies in an open neighborhood on which the curve is at worst nodal. -/
theorem IsNodeAt.exists_nodal_neighbourhood {f : C ⟶ S} {x : C} (h : f.IsNodeAt x) :
    ∃ (V : Scheme.{u}) (i : V ⟶ C), IsOpenImmersion i ∧ x ∈ Set.range i ∧
      AtWorstNodalOfRelativeDimensionOne (i ≫ f) := by
  obtain ⟨V, i, hi, z, hz, hnodal⟩ := h.2
  exact ⟨V, i, hi, ⟨z, hz⟩, hnodal⟩

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

namespace AlgebraicGeometry.Scheme

open IsLocalRing IdealSheafData

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (.of k))]

local notation "S[" K "]" => Spec (CommRingCat.of K)

variable [SyntomicOfRelativeDimension 1 (C ↘ S[k])]

private theorem exists_nodal_neighbourhood_of_unramified_singularLocus_restriction
    (W : (C.singularLocus k).subscheme.Opens)
    [Unramified (W.ι ≫ (C.singularLocus k).subschemeι ≫ (C ↘ S[k]))] :
    ∃ U : C.Opens, (C.singularLocus k).subschemeι ⁻¹ᵁ U = W ∧
      AtWorstNodalOfRelativeDimensionOne (U.ι ≫ (C ↘ S[k])) := by
  let J := C.singularLocus k
  obtain ⟨V, hV, hpre⟩ := J.subschemeι.isClosedEmbedding.isInducing.isOpen_iff.mp W.isOpen
  let U : C.Opens := ⟨V, hV⟩
  have hW : J.subschemeι ⁻¹ᵁ U = W := SetLike.coe_injective hpre
  refine ⟨U, hW, ?_⟩
  let : U.toScheme.Over S[k] := ⟨U.ι ≫ (C ↘ S[k])⟩
  let : U.ι.IsOver S[k] := ⟨rfl⟩
  have hS : SyntomicOfRelativeDimension 1 (U.toScheme ↘ S[k]) :=
    zero_add 1 ▸ inferInstanceAs (SyntomicOfRelativeDimension (0 + 1) (U.ι ≫ (C ↘ S[k])))
  let : SyntomicOfRelativeDimension 1 (U.ι ≫ (C ↘ S[k])) := hS
  apply (atWorstNodalOfRelativeDimensionOne_iff_of_iso_spec _ (Iso.refl S[k])).mpr
  rw [Iso.refl_hom, Category.comp_id]
  refine AffineAtWorstNodalOfRelativeDimensionOne.mk hS ?_
  let I := U.toScheme.singularLocus k
  let j := I.subschemeMap J U.ι (le_map_iff_comap_le.mpr
    (singularLocus_eq_comap_of_etale (R := k) U.ι).ge)
  have H : IsPullback I.subschemeι j U.ι J.subschemeι :=
    isPullback_singularLocus_subschemeι_of_etale (R := k) U.ι
  have : IsOpenImmersion j := MorphismProperty.of_isPullback (P := @IsOpenImmersion) H inferInstance
  have hr : Set.range j ⊆ Set.range W.ι := by
    rw [Scheme.Pullback.range_snd_of_isPullback H, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι, ← hW]
    exact Set.Subset.rfl
  let g := IsOpenImmersion.lift W.ι j hr
  have : IsOpenImmersion g := IsOpenImmersion.of_comp g W.ι
  rw [← Category.assoc, H.w, ← IsOpenImmersion.lift_fac W.ι j hr]
  simpa only [Category.assoc] using
    (inferInstance : Unramified (g ≫ (W.ι ≫ J.subschemeι ≫ (C ↘ S[k]))))

/-- A point on a syntomic curve over a field is a node if its singular
subscheme has reduced-point stalk there and its residue field is separable over the base. -/
theorem isNodeAt_of_singularLocus_stalkIdeal_eq_maximalIdeal
    (x : C) [Algebra.IsSeparable k (C.residueField x)]
    (hx : (C.singularLocus k).stalkIdeal x = maximalIdeal (C.presheaf.stalk x)) :
    (C ↘ S[k]).IsNodeAt x := by
  let J := C.singularLocus k
  have hxJ : x ∈ J.support :=
    (J.mem_support_iff_stalkIdeal_ne_top x).mpr (hx.symm ▸ Ideal.IsMaximal.ne_top inferInstance)
  have hnot := (C.mem_support_singularLocus_iff_notMem_smoothLocus (R := k) x).mp hxJ
  obtain ⟨z, rfl⟩ := J.range_subschemeι.ge hxJ
  let g := J.subschemeι ≫ (C ↘ S[k])
  let : J.subscheme.Over S[k] := ⟨g⟩
  let : J.subschemeι.IsOver S[k] := ⟨rfl⟩
  let π := J.subschemeι.stalkMapAlgHom (k := k) z
  have hπ : Function.Surjective π := by
    intro b
    obtain ⟨a, ha⟩ := J.subschemeι.stalkMap_surjective z b
    exact ⟨a, (Hom.stalkMapAlgHom_apply _ _ _).trans ha⟩
  have hk : RingHom.ker π = maximalIdeal (C.presheaf.stalk (J.subschemeι z)) := by
    dsimp only [π]
    rw [AlgHom.ker_coe, J.subschemeι.stalkMapAlgHom_toRingHom,
      J.subschemeι.ker_stalkMap_of_isClosedImmersion,
      ker_subschemeι, hx]
  let e : C.residueField (J.subschemeι z) ≃ₐ[k] J.subscheme.presheaf.stalk z :=
    (Ideal.quotientEquivAlgOfEq k hk.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hπ)
  have : Algebra.FormallyUnramified k (C.residueField (J.subschemeι z)) := .of_isSeparable _ _
  have : Algebra.FormallyUnramified k (J.subscheme.presheaf.stalk z) := .of_equiv e
  let t := J.subscheme.fromSpecStalk z
  let w : Spec (J.subscheme.presheaf.stalk z) := closedPoint (J.subscheme.presheaf.stalk z)
  have htcomp : t ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap k (J.subscheme.presheaf.stalk z))) :=
    J.subscheme.fromSpecStalk_comp_over (k := k) z
  have ht : ((t ≫ g).stalkMap w).hom.FormallyUnramified := by
    rw [htcomp]
    have : FormallyUnramified
        (Spec.map (CommRingCat.ofHom (algebraMap k (J.subscheme.presheaf.stalk z)))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.formallyUnramified_algebraMap.mpr inferInstance)
    exact FormallyUnramified.stalkMap _ _
  have hg : (g.stalkMap z).hom.FormallyUnramified := by
    simp only [Scheme.Hom.stalkMap_comp] at ht
    have ht' := (RingHom.FormallyUnramified.respectsIso.cancel_right_isIso _ _).mp ht
    have hw : t w = z := fromSpecStalk_closedPoint
    exact hw ▸ ht'
  obtain ⟨W, hzW, -, hW⟩ := (g.unramifiedAt_iff_stalkMap z).mpr hg
  have : FormallyUnramified (W.ι ≫ J.subschemeι ≫ (C ↘ S[k])) := hW
  have : Unramified (W.ι ≫ J.subschemeι ≫ (C ↘ S[k])) := ⟨⟩
  obtain ⟨U, hUW, hn⟩ := exists_nodal_neighbourhood_of_unramified_singularLocus_restriction W
  have hU : J.subschemeι z ∈ U := (Scheme.Hom.mem_preimage _).mp (hUW.symm ▸ hzW)
  have := hn.syntomic
  let u : U := ⟨_, hU⟩
  apply ((C ↘ S[k]).isNodeAt_comp_iff_of_isOpenImmersion U.ι u).mp
  apply ((U.ι ≫ (C ↘ S[k])).isNodeAt_iff_notMem_smoothLocus hn u).mpr
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  exact hnot

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y S : Scheme.{u}}

/-- A common open subscheme on which two closed subschemes agree provides a nodal
neighborhood on one whenever the other is nodal over the same base. -/
theorem exists_nodal_neighbourhood_of_comap_eq
    {X Y U S : Scheme.{u}}
    (D : X.IdealSheafData) {E : Y.IdealSheafData}
    {s : X ⟶ S} {t : Y ⟶ S}
    (j : U ⟶ X) (i : U ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion i]
    (hbase : j ≫ s = i ≫ t) (hDE : D.comap j = E.comap i)
    (hE : AtWorstNodalOfRelativeDimensionOne (E.subschemeι ≫ t))
    (p : D.subscheme) (hp : D.subschemeι p ∈ Set.range j) :
    ∃ (W : Scheme.{u}) (g : W ⟶ D.subscheme), IsOpenImmersion g ∧ p ∈ Set.range g ∧
      AtWorstNodalOfRelativeDimensionOne (g ≫ D.subschemeι ≫ s) := by
  let g := subschemeMap (D.comap j) D j (le_map_comap _ _)
  let h := subschemeMap (E.comap i) E i (le_map_comap _ _)
  have hpb : IsPullback (D.comap j).subschemeι g j D.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (by simp [g]) (by simp)
  have hpb' : IsPullback (E.comap i).subschemeι h i E.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (by simp [h]) (by simp)
  have : IsOpenImmersion h := MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    hpb' inferInstance
  refine ⟨_, g, MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb inferInstance, ?_, ?_⟩
  · rw [Scheme.Pullback.range_snd_of_isPullback hpb]
    exact hp
  · rw [← hpb.w_assoc, hbase, hDE, hpb'.w_assoc]
    exact hE.comp_of_etale h

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

/-- A point on a reduced nodal boundary that is not a node lies in the smooth locus
of the boundary. -/
theorem exists_mem_smoothLocus_of_mem_support_of_not_isNodeOfReducedBoundary
    (D : Y.IdealSheafData) [IsReduced D.subscheme] (g : Y ⟶ S)
    (hD : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ g)) {x : Y} (hx : x ∈ D.support)
    (hn : ¬ D.IsNodeOfReducedBoundary g x) :
    let : SyntomicOfRelativeDimension 1 (D.subschemeι ≫ g) := hD.syntomic
    ∃ z : D.subscheme, D.subschemeι z = x ∧ z ∈ (D.subschemeι ≫ g).smoothLocus := by
  dsimp only
  have hr : x ∈ Set.range D.subschemeι := by rwa [D.range_subschemeι]
  obtain ⟨z, hz⟩ := hr
  have := hD.syntomic
  refine ⟨z, hz, ?_⟩
  by_contra hs
  exact hn ((D.isNodeOfReducedBoundary_iff_of_isReduced g x).mpr
    ⟨z, hz, ((D.subschemeι ≫ g).isNodeAt_iff_notMem_smoothLocus hD z).mpr hs⟩)

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
