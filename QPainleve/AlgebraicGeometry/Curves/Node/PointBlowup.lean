/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Normalization
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import QPainleve.AlgebraicGeometry.Blowup.Comparison
import QPainleve.AlgebraicGeometry.Fiber
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Blowing up a single node of a nodal curve

Near a chosen node of a nodal curve over a field, its reduced point ideal agrees
with the ideal of the singular subscheme. The blowup of that point thus agrees
near its exceptional fiber with the blowup of the singular subscheme. In
particular, the ideal of the node pulls back to an effective Cartier divisor
on the normalization. The fiber comparison identifies the branches at the node.
See the [Stacks Project, Section 53.19](https://stacks.math.columbia.edu/tag/0C46).
-/

public section

open CategoryTheory Limits TopologicalSpace TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- Every point of the singular locus of a nodal curve over a field is a closed
point of the curve. -/
theorem isClosed_singleton_of_mem_singularLocus
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) {x : X}
    (hx : (letI := hnodal.syntomic; x ∈ (X.singularLocus k).support)) :
    IsClosed ({x} : Set X) := by
  have := hnodal.syntomic
  let I := X.singularLocus k
  have : Etale (I.subschemeι ≫ (X ↘ Spec (.of k))) := X.etale_singularLocus_subschemeι_comp hnodal
  have : IsLocallyArtinian I.subscheme := .of_locallyQuasiFinite (I.subschemeι ≫ (X ↘ Spec (.of k)))
  obtain ⟨z, rfl⟩ : x ∈ Set.range I.subschemeι := I.range_subschemeι.ge hx
  rw [← Set.image_singleton]
  exact I.subschemeι.isClosedEmbedding.isClosedMap _ (isClosed_discrete _)

/-- The fiber of the blowup of the singular locus over a node is finite étale
over the residue field of the node. -/
theorem isFinite_etale_fiberToSpecResidueField_blowup_singularLocus_of_node
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) {x : X}
    (hx : (letI := hnodal.syntomic; x ∈ (X.singularLocus k).support)) :
    letI := hnodal.syntomic
    let f := (X.singularLocus k).blowupToBase.fiberToSpecResidueField x
    IsFinite f ∧ Etale f := by
  let := hnodal.syntomic
  let I := X.singularLocus k
  obtain ⟨z, rfl⟩ := I.range_subschemeι.ge hx
  have := X.isFinite_branchSchemeToSingularLocus hnodal
  have := X.etale_branchSchemeToSingularLocus hnodal
  let f := (X.branchSchemeToSingularLocus k).fiberToSpecResidueField z
  let g := Spec.map (I.subschemeι.residueFieldMap z)
  have : Etale f := MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (X.branchSchemeToSingularLocus k)
      (I.subscheme.fromSpecResidueField z)) inferInstance
  have h₁ : IsFinite (f ≫ g) := inferInstance
  have h₂ : Etale (f ≫ g) := inferInstance
  obtain ⟨e⟩ := (X.isPullback_branchScheme k).flip.nonempty_iso_fiberToSpecResidueField z
  let e' := (Over.forget _).mapIso e
  have hw : e'.hom ≫ I.blowupToBase.fiberToSpecResidueField (I.subschemeι z) = f ≫ g :=
    Over.w e.hom
  rw [← e'.inv_hom_id_assoc (I.blowupToBase.fiberToSpecResidueField (I.subschemeι z)), hw]
  exact ⟨inferInstance, inferInstance⟩

/-- An open neighbourhood of a node identifies the singular ideal with the reduced ideal
of that point. -/
theorem exists_comap_singularLocus_eq_comap_vanishingIdeal_of_node
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) {x : X}
    (hx : (letI := hnodal.syntomic; x ∈ (X.singularLocus k).support)) :
    letI := hnodal.syntomic
    ∃ U : X.Opens, x ∈ U ∧ (X.singularLocus k).comap U.ι =
      (vanishingIdeal ⟨closure {x}, isClosed_closure⟩).comap U.ι := by
  have := hnodal.syntomic
  let I := X.singularLocus k
  let g := I.subschemeι ≫ (X ↘ Spec (.of k))
  have : Etale g := X.etale_singularLocus_subschemeι_comp hnodal
  have : IsLocallyArtinian I.subscheme := .of_locallyQuasiFinite g
  have hregular : IsRegular I.subscheme := IsRegular.of_smooth g
  obtain ⟨s, rfl⟩ : x ∈ Set.range I.subschemeι := (range_subschemeι I).ge hx
  have hclosed : IsClosed ({I.subschemeι s} : Set X) :=
    X.isClosed_singleton_of_mem_singularLocus hnodal (I.range_subschemeι.le ⟨s, rfl⟩)
  obtain ⟨V, hV, hpre⟩ := I.subschemeι.isClosedEmbedding.isInducing.isOpen_iff.mp
    (isOpen_discrete ({s} : Set I.subscheme))
  let U : X.Opens := ⟨V, hV⟩
  have hsU : I.subschemeι s ∈ U := by
    have : s ∈ I.subschemeι ⁻¹' V := hpre ▸ Set.mem_singleton s
    exact this
  refine ⟨U, hsU, ?_⟩
  have hsupport : (I.support : Set X) ∩ V = {I.subschemeι s} := by
    rw [← range_subschemeι, Set.inter_comm, ← Set.image_preimage_eq_inter_range, hpre,
      Set.image_singleton]
  have hrad : I.radical = I := (isReduced_subscheme_iff_radical_eq I).mp inferInstance
  have hI : (vanishingIdeal I.support).comap U.ι = I.comap U.ι :=
    congrArg (fun J : X.IdealSheafData ↦ J.comap U.ι) (vanishingIdeal_support.trans hrad)
  refine hI.symm.trans ?_
  rw [comap_vanishingIdeal_of_isOpenImmersion, comap_vanishingIdeal_of_isOpenImmersion]
  congr 1
  apply Closeds.ext
  have hU : U.ι ⁻¹' V = Set.univ := Set.preimage_eq_univ_iff.mpr <| by
    rw [Scheme.Opens.range_ι]
    exact Set.Subset.rfl
  simp only [Closeds.coe_mk]
  rw [hclosed.closure_eq, ← hsupport, Set.preimage_inter, hU, Set.inter_univ]

local notation "pointIdeal" x:arg =>
  vanishingIdeal (Closeds.mk (closure (singleton x)) isClosed_closure)

/-- Pulling the ideal of a node back to the blowup separating all the nodes gives an
effective Cartier divisor. -/
theorem isEffectiveCartier_comap_blowupToBase_singularLocus_of_node
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) {x : X}
    (hx : (letI := hnodal.syntomic; x ∈ (X.singularLocus k).support)) :
    letI := hnodal.syntomic
    ((pointIdeal x).comap (X.singularLocus k).blowupToBase).IsEffectiveCartier := by
  have := hnodal.syntomic
  obtain ⟨U, hxU, h⟩ := X.exists_comap_singularLocus_eq_comap_vanishingIdeal_of_node hnodal hx
  apply isEffectiveCartier_comap_blowupToBase_of_comap_eq h
  rw [coe_support_vanishingIdeal, Closeds.coe_mk,
    (X.isClosed_singleton_of_mem_singularLocus hnodal hx).closure_eq]
  exact Set.singleton_subset_iff.mpr hxU

/-- The fiber of the single-node blowup agrees over the residue field with the fiber of
the blowup of the whole singular subscheme. The latter is the node's branch fiber. -/
theorem nonempty_fiberToSpecResidueFieldIso_blowup_singularLocus_of_node
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) {x : X}
    (hx : (letI := hnodal.syntomic; x ∈ (X.singularLocus k).support)) :
    letI := hnodal.syntomic
    let J := vanishingIdeal ⟨closure {x}, isClosed_closure⟩
    Nonempty (Over.mk (J.blowupToBase.fiberToSpecResidueField x) ≅
      Over.mk ((X.singularLocus k).blowupToBase.fiberToSpecResidueField x)) := by
  have := hnodal.syntomic
  let I := X.singularLocus k
  let J := vanishingIdeal ⟨closure {x}, isClosed_closure⟩
  obtain ⟨U, hxU, h⟩ := X.exists_comap_singularLocus_eq_comap_vanishingIdeal_of_node hnodal hx
  have hr : Set.range (X.fromSpecResidueField x) ⊆ Set.range U.ι := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    exact Set.singleton_subset_iff.mpr hxU
  let a := IsOpenImmersion.lift U.ι (X.fromSpecResidueField x) hr
  have ha : a ≫ U.ι = X.fromSpecResidueField x := IsOpenImmersion.lift_fac _ _ _
  -- Both charts are pulled back to the same residue field of the original curve.
  have iso (L : X.IdealSheafData) :
      Nonempty (Over.mk (pullback.snd (L.comap U.ι).blowupToBase a) ≅
        Over.mk (L.blowupToBase.fiberToSpecResidueField x)) := by
    have H := (IsPullback.of_hasPullback (L.comap U.ι).blowupToBase a).paste_horiz
      (L.isPullback_blowupMap_of_flat U.ι).flip
    rw [ha] at H
    exact ⟨Over.isoMk H.isoPullback H.isoPullback_hom_snd⟩
  obtain ⟨eI⟩ := iso I
  obtain ⟨eJ⟩ := iso J
  exact ⟨eJ.symm ≪≫ eqToIso (congrArg
    (fun L : U.toScheme.IdealSheafData ↦ Over.mk (pullback.snd L.blowupToBase a))
    (h : I.comap U.ι = J.comap U.ι).symm) ≪≫ eI⟩

/-- The blowup of a single node is regular at every point above that node. -/
theorem isRegularLocalRing_stalk_blowupToBase_vanishingIdeal_of_node
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) {x : X}
    (hx : (letI := hnodal.syntomic; x ∈ (X.singularLocus k).support)) :
    let J := vanishingIdeal ⟨closure {x}, isClosed_closure⟩
    ∀ y : J.blowup, J.blowupToBase y = x → IsRegularLocalRing (J.blowup.presheaf.stalk y) := by
  have := hnodal.syntomic
  let I := X.singularLocus k
  let J := vanishingIdeal ⟨closure {x}, isClosed_closure⟩
  dsimp only
  intro y hy
  obtain ⟨U, hxU, h⟩ := X.exists_comap_singularLocus_eq_comap_vanishingIdeal_of_node hnodal hx
  have : IsRegular I.blowup := X.isRegular_blowup_singularLocus hnodal
  have hreg : IsRegular (J.comap U.ι).blowup :=
    (h : I.comap U.ι = J.comap U.ι) ▸ IsRegular.of_isOpenImmersion (I.blowupMap U.ι)
  obtain ⟨z, rfl⟩ : y ∈ Set.range (J.blowupMap U.ι) := by
    rw [← Scheme.Hom.coe_opensRange, SetLike.mem_coe, J.opensRange_blowupMap,
      Scheme.Opens.opensRange_ι]
    exact J.blowupToBase.mem_preimage.mpr (hy.symm ▸ hxU)
  exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion (J.blowupMap U.ι) z).mpr inferInstance

end AlgebraicGeometry.Scheme
