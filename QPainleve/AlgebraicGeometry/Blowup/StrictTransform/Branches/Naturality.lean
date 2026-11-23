/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Isomorphism
public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Isomorphism

import QPainleve.AlgebraicGeometry.Blowup.Comparison
import QPainleve.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Branches and attachment points in a nodal blowup

The blowup of the singular locus of a nodal curve maps canonically to the
strict transform of the curve in the ambient blowup of a node. On the fiber
over that node it identifies the actual branches with the points where the
strict transform meets the exceptional divisor. This identification is natural
under isomorphisms of the ambient pairs, including at a self-node.

The naturality records the branch data needed to lift automorphisms through
nodal blowups in the toric reduction of [Gross, Hacking and Keel, *Moduli of
surfaces with an anti-canonical cycle*, Proposition 2.6][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public noncomputable section

open CategoryTheory Limits TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

open IdealSheafData

variable {k : Type u} [Field k] {D Y : Scheme.{u}} [D.Over (Spec (.of k))]
  (i : D ⟶ Y) [IsClosedImmersion i]
  (hnodal : AtWorstNodalOfRelativeDimensionOne (D ↘ Spec (.of k))) {x : D}
  (hx : (letI := hnodal.syntomic; x ∈ (D.singularLocus k).support))

local notation "pointIdeal" a:arg =>
  vanishingIdeal (Closeds.mk (closure (singleton a)) isClosed_closure)
local notation "P" => pointIdeal (i x)
local notation "J" => comap (pointIdeal (i x)) i

include hx in
private theorem isEffectiveCartier_comap_strictTransformCenter :
    letI := hnodal.syntomic
    ((J).comap (D.singularLocus k).blowupToBase).IsEffectiveCartier := by
  have := hnodal.syntomic
  rw [comap_vanishingIdeal_closure_singleton_of_isClosedImmersion i x]
  exact D.isEffectiveCartier_comap_blowupToBase_singularLocus_of_node hnodal hx

private def normalizationToStrictTransform :
    letI := hnodal.syntomic
    (D.singularLocus k).blowup ⟶ (J).blowup := by
  letI := hnodal.syntomic
  exact (J).blowupLift _ (isEffectiveCartier_comap_strictTransformCenter i hnodal hx)

@[reassoc]
private theorem normalizationToStrictTransform_blowupToBase :
    letI := hnodal.syntomic
    normalizationToStrictTransform i hnodal hx ≫ (J).blowupToBase =
      (D.singularLocus k).blowupToBase := by
  have := hnodal.syntomic
  exact (J).blowupLift_blowupToBase _ _

/-- The branch scheme maps to the strict transform in the ambient blowup of the
specified node. The map restricts the lift of the normalization morphism. -/
def strictTransformBranchMap :
    letI := hnodal.syntomic
    D.branchScheme k ⟶ (J).blowup := by
  letI := hnodal.syntomic
  exact D.branchSchemeToBlowup k ≫ normalizationToStrictTransform i hnodal hx

/-- The map from the branch scheme to the strict transform commutes with both maps
to the original curve. -/
@[reassoc (attr := simp)]
theorem strictTransformBranchMap_blowupToBase :
    letI := hnodal.syntomic
    strictTransformBranchMap i hnodal hx ≫ (J).blowupToBase =
      D.branchSchemeToSingularLocus k ≫ (D.singularLocus k).subschemeι := by
  have := hnodal.syntomic
  rw [strictTransformBranchMap, Category.assoc, normalizationToStrictTransform_blowupToBase,
    Scheme.branchSchemeToSingularLocus_subschemeι]

/-- On the fiber over a node, the canonical branch map is a bijection to the fiber of
the strict transform. Over a separably closed field this identifies the two branches
even at a self-node. -/
theorem bijOn_strictTransformBranchMap :
    letI := hnodal.syntomic
    Set.BijOn (strictTransformBranchMap i hnodal hx)
      {q | (D.singularLocus k).subschemeι (D.branchSchemeToSingularLocus k q) = x}
      ((J).blowupToBase ⁻¹' {x}) := by
  have := hnodal.syntomic
  obtain ⟨U, hxU, h⟩ := D.exists_comap_singularLocus_eq_comap_vanishingIdeal_of_node hnodal hx
  have hJ : (D.singularLocus k).comap U.ι = (J).comap U.ι :=
    h.trans (congrArg (fun L : D.IdealSheafData ↦ L.comap U.ι)
      (comap_vanishingIdeal_closure_singleton_of_isClosedImmersion i x)).symm
  have hν :=
    bijOn_fiber_of_comap_eq (normalizationToStrictTransform_blowupToBase i hnodal hx) hJ hxU
  let a := D.branchSchemeToBlowup k
  let b := D.branchSchemeToSingularLocus k ≫ (D.singularLocus k).subschemeι
  let ν := (D.singularLocus k).blowupToBase
  let H := D.isPullback_branchScheme k
  have hb : (a ≫ ν) = b := (D.branchSchemeToSingularLocus_subschemeι k).symm
  have ha : Set.BijOn a (b ⁻¹' {x}) (ν ⁻¹' {x}) := by
    have : IsClosedImmersion a := MorphismProperty.of_isPullback H inferInstance
    refine ⟨?_, a.isClosedEmbedding.injective.injOn, ?_⟩
    · intro y hy
      simpa only [Set.mem_preimage, ← Scheme.Hom.comp_apply, hb] using hy
    · intro y hy
      obtain ⟨z, hz⟩ : x ∈ Set.range (D.singularLocus k).subschemeι :=
        (D.singularLocus k).range_subschemeι.ge hx
      obtain ⟨q, -, hq⟩ := Scheme.exists_preimage_of_isPullback H z y
        (hz.trans (Set.mem_singleton_iff.mp hy).symm)
      have hq' : a q = y := hq
      have hqBase : b q = ν y := by rw [← hb, Scheme.Hom.comp_apply, hq']
      exact ⟨q, hqBase.trans (Set.mem_singleton_iff.mp hy), hq'⟩
  exact hν.comp ha

/-- The actual branches over a node are equivalent to the points of the ambient
strict transform over that node. -/
def strictTransformBranchEquiv :
    letI := hnodal.syntomic
    ({q | (D.singularLocus k).subschemeι (D.branchSchemeToSingularLocus k q) = x} :
      Set (D.branchScheme k)) ≃ ((J).blowupToBase ⁻¹' {x} : Set (J).blowup) :=
  (bijOn_strictTransformBranchMap i hnodal hx).equiv _

/-- The forward map of the branch equivalence is induced by the canonical scheme
morphism from the branch scheme. -/
@[simp]
theorem strictTransformBranchEquiv_apply_coe :
    letI := hnodal.syntomic
    ∀ q, (strictTransformBranchEquiv i hnodal hx q).val = strictTransformBranchMap i hnodal hx q :=
  fun _ ↦ (rfl)

variable {D' Y' : Scheme.{u}} [D'.Over (Spec (.of k))]
  (i' : D' ⟶ Y') [IsClosedImmersion i']
  (hnodal' : AtWorstNodalOfRelativeDimensionOne (D' ↘ Spec (.of k)))
  (e : D ≅ D') [e.hom.IsOver (Spec (.of k))] (g : Y ≅ Y')
  (h : e.hom ≫ i' = i ≫ g.hom)
  {x' : D'} (hxx' : e.hom x = x')
  (hx' : (letI := hnodal'.syntomic; x' ∈ (D'.singularLocus k).support))

local notation "P'" => pointIdeal (i' x')

omit [IsClosedImmersion i] [IsClosedImmersion i'] in
include h hxx' in
/-- An isomorphism carrying one embedded nodal curve to another transports the
ambient point ideal of a node to the ideal of its image. -/
theorem comap_nodeIdeal_eq_of_iso :
    (P').comap g.hom = P := by
  have he : i' x' = g.hom (i x) := hxx' ▸ congrArg (fun f : D ⟶ Y' ↦ f x) h
  rw [he]
  exact comap_vanishingIdeal_closure_singleton_of_isClosedImmersion g.hom (i x)

/-- The strict-transform attachment map is equivariant under isomorphisms of embedded
nodal curves. This compares the actual maps to the ambient blowups, using the induced
isomorphism of branch schemes. -/
@[reassoc]
theorem strictTransformBranchMap_comp_blowupIso :
    letI := hnodal.syntomic
    letI := hnodal'.syntomic
    strictTransformBranchMap i hnodal hx ≫ (P).blowupMap i ≫
        ((P').blowupIso g (comap_nodeIdeal_eq_of_iso i i' e g h hxx')).hom =
      (e.branchSchemeIso (R := k)).hom ≫ strictTransformBranchMap i' hnodal' hx' ≫
        (P').blowupMap i' := by
  have := hnodal.syntomic
  have := hnodal'.syntomic
  let E := ((P').blowupIso g (comap_nodeIdeal_eq_of_iso i i' e g h hxx')).hom
  let N := normalizationToStrictTransform i hnodal hx
  let N' := normalizationToStrictTransform i' hnodal' hx'
  let ν := (D.singularLocus k).blowupToBase
  have hleft : (N ≫ (P).blowupMap i ≫ E) ≫ (P').blowupToBase = ν ≫ i ≫ g.hom := by
    simp only [Category.assoc, E, blowupIso_hom_blowupToBase,
      ← Category.assoc ((P).blowupMap i), blowupMap_blowupToBase, Category.assoc,
      N, normalizationToStrictTransform_blowupToBase_assoc, ν]
  have hright :
      ((e.singularLocusBlowupIso (R := k)).hom ≫ N' ≫ (P').blowupMap i') ≫
          (P').blowupToBase = ν ≫ i ≫ g.hom := by
    simp only [Category.assoc, blowupMap_blowupToBase, N',
      normalizationToStrictTransform_blowupToBase_assoc,
      Iso.singularLocusBlowupIso_hom_blowupToBase_assoc, h, ν]
  have hcartier : ((P').comap (ν ≫ i ≫ g.hom)).IsEffectiveCartier := by
    rw [comap_comp, comap_comp, comap_nodeIdeal_eq_of_iso i i' e g h hxx']
    exact isEffectiveCartier_comap_strictTransformCenter i hnodal hx
  have hnorm : N ≫ (P).blowupMap i ≫ E =
      (e.singularLocusBlowupIso (R := k)).hom ≫ N' ≫ (P').blowupMap i' :=
    (P').blowup_hom_ext (hleft.trans hright.symm) (hleft.symm ▸ hcartier)
  simpa only [strictTransformBranchMap, Category.assoc, E, N, N',
    Iso.branchSchemeIso_hom_branchSchemeToBlowup_assoc] using
    congrArg (fun f ↦ D.branchSchemeToBlowup k ≫ f) hnorm

section Automorphism

variable (d : D ≅ D) [d.hom.IsOver (Spec (.of k))] (f : Y ≅ Y)
  (hd : d.hom ≫ i = i ≫ f.hom) (hfix : d.hom x = x)

local notation "nodeMap" =>
  Scheme.branchSchemeToSingularLocus k D ≫ IdealSheafData.subschemeι (D.singularLocus k)
local notation "liftHom" =>
  Iso.hom (IdealSheafData.blowupIso (P) f (comap_nodeIdeal_eq_of_iso i i d f hd hfix))
local notation "branchHom" => Iso.hom (d.branchSchemeIso (R := k))

include hx in
/-- A lift fixing the blown-up node fixes each attachment point of the strict
transform exactly when the original boundary automorphism fixes each point of the branch
scheme over that node. In particular, the two branches of a split self-node are
tested individually. -/
theorem blowupIso_fixes_strictTransform_fiber_iff :
    letI := hnodal.syntomic
    (∀ y : (J).blowup, (J).blowupToBase y = x →
      liftHom ((P).blowupMap i y) = (P).blowupMap i y) ↔
    ∀ q : D.branchScheme k, (nodeMap) q = x → (branchHom) q = q := by
  have := hnodal.syntomic
  let a := strictTransformBranchMap i hnodal hx
  let j := (P).blowupMap i
  have hbij := bijOn_strictTransformBranchMap i hnodal hx
  have hnat := strictTransformBranchMap_comp_blowupIso i hnodal hx i hnodal d f hd hfix hx
  have hpoint (q : D.branchScheme k) : liftHom (j (a q)) = j (a ((branchHom) q)) :=
    congrArg (fun v : D.branchScheme k ⟶ (P).blowup ↦ v q) hnat
  have hnode : (branchHom) ≫ (nodeMap) = (nodeMap) ≫ d.hom := by
    simp only [Iso.branchSchemeIso_hom_branchSchemeToSingularLocus_assoc,
      Iso.singularLocusIso_hom_subschemeι, Category.assoc]
  constructor
  · intro h q hq
    have hq' : (nodeMap) ((branchHom) q) = x :=
      (congrArg (fun v : D.branchScheme k ⟶ D ↦ v q) hnode).trans
        ((congrArg d.hom hq).trans hfix)
    apply hbij.injOn hq' hq
    apply j.injective
    exact (hpoint q).symm.trans (h (a q) (hbij.mapsTo hq))
  · intro h y hy
    obtain ⟨q, hq, hqy⟩ := hbij.surjOn hy
    have hp := hpoint q
    rw [h q hq, hqy] at hp
    exact hp

end Automorphism

end AlgebraicGeometry.Scheme.Hom
