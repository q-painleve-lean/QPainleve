/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.DualGraph
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.SchematicDensity
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Finite
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.Topology.NoetherianSpace.IrreducibleComponents
import TauCeti.Topology.Sober

/-!
# Normal components of nodal curves

The normalization of a nodal curve is the blowup of its singular subscheme.
Each component meets the locus where this blowup is an isomorphism. In particular,
the normalization maps a component isomorphically onto its reduced image whenever
that image is normal.
-/

public section

open CategoryTheory TopologicalSpace TauCeti TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] (C : Scheme.{u}) [C.Over (Spec (.of k))]
  [PrestableFamily (C ↘ Spec (.of k))]

local notation "I" => singularLocus k C
local notation "ν" => IdealSheafData.blowupToBase I
local notation "N" => IdealSheafData.blowup I
local notation "V" => irreducibleComponents N
local notation "η" => genericPoints.ofComponent

/-- Each component's generic point lies over the isomorphism locus of the
normalization morphism. -/
theorem blowupComponentGeneric_mem_isoLocus (v : V) : ν (η v) ∈ (ν).isoLocus := by
  have : IsFinite ν := C.isFinite_blowupToBase_singularLocus
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have : IsNoetherian N := isNoetherian_of_finiteType (ν ≫ C ↘ Spec (.of k))
  have hcartier := (I).isEffectiveCartier_comap_blowupToBase
  have := hcartier.isSchemeTheoreticallyDominant_support_compl_ι
  have hdense : Dense (((I).comap ν).support : Set N)ᶜ := by
    simpa only [DenseRange, Scheme.Opens.range_ι, Closeds.coe_compl] using
      (Scheme.Opens.ι ((I).comap ν).support.compl).denseRange
  have hv : IsOpen (v : Set N) := by
    rw [← C.coe_blowupComponent v]
    exact (C.blowupComponent v).isOpen
  obtain ⟨y, hyv, hy⟩ := hdense.inter_open_nonempty _ hv v.property.1.nonempty
  have hη : (η v : N) ∈ ((I).comap ν).support.compl :=
    ((genericPoints.isGenericPoint_ofComponent v).specializes hyv).mem_open
      ((I).comap ν).support.compl.isOpen hy
  have hIso := C.isIso_blowupToBase_singularLocus_restrict_smoothLocus (R := k)
  apply (ν).le_isoLocus_iff.mpr hIso
  apply not_not.mp
  exact (C.mem_support_singularLocus_iff_notMem_smoothLocus (ν (η v))).not.mp
    (by simpa only [← SetLike.mem_coe, Closeds.coe_compl, Set.mem_compl_iff,
      support_comap, Closeds.coe_preimage, Set.mem_preimage] using hη)

/-- The image of a normalization component under the normalization followed by a
closed morphism is the closure of the image of its generic point. -/
theorem range_blowupComponent_comp {Y : Scheme.{u}} (v : V) (j : C ⟶ Y) (hj : IsClosedMap j) :
    Set.range ((C.blowupComponent v).ι ≫ ν ≫ j) = closure {j (ν (η v))} := by
  have : IsFinite ν := C.isFinite_blowupToBase_singularLocus
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  let f := ν ≫ j
  have hf : IsClosedMap f := hj.comp (ν).isClosedMap
  rw [Hom.comp_base, TopCat.coe_comp, Set.range_comp, Opens.range_ι,
    C.coe_blowupComponent v, ← (genericPoints.isGenericPoint_ofComponent v).def,
    ← hf.closure_image_eq_of_continuous f.continuous, Set.image_singleton]
  rfl

/-- Containment of the image of one normalization component in another's image
forces equality of the components. -/
theorem eq_of_range_blowupComponent_subset {v w : V}
    (h : Set.range ((C.blowupComponent v).ι ≫ ν) ⊆ Set.range ((C.blowupComponent w).ι ≫ ν)) :
    v = w := by
  let y := η v
  have hy : y.val ∈ (C.blowupComponent v : Set N) := by
    rw [coe_blowupComponent]
    exact (genericPoints.isGenericPoint_ofComponent v).mem
  have hr : ν y ∈ Set.range ((C.blowupComponent w).ι ≫ ν) := by
    exact h ⟨⟨y, hy⟩, rfl⟩
  obtain ⟨z, hz⟩ := hr
  rw [Hom.comp_apply] at hz
  have hv := C.blowupComponentGeneric_mem_isoLocus v
  have he := (ν).injOn_preimage_isoLocus (by rw [Set.mem_preimage, hz]; exact hv) hv hz
  apply Subtype.ext
  refine eq_of_mem_irreducibleComponents_of_nonempty_inter_open v.property w.property
    (C.blowupComponent v).isOpen (by rw [coe_blowupComponent]) ?_ |>.symm
  refine ⟨y, ?_, hy⟩
  rw [← he, ← coe_blowupComponent]
  exact z.property

private theorem isIso_morphismRestrict_of_blowupComponent
    {Y : Scheme.{u}} [IsReduced Y] (j : Y ⟶ C)
    (v : V) (g : (C.blowupComponent v).toScheme ⟶ Y)
    [IsFinite g] [Surjective g] (h : g ≫ j = (C.blowupComponent v).ι ≫ ν) :
    IsIso (g ∣_ (j ⁻¹ᵁ (ν).isoLocus)) := by
  let W := (ν).isoLocus
  let U := j ⁻¹ᵁ W
  let P := g ⁻¹ᵁ U
  let f := P.ι ≫ (C.blowupComponent v).ι
  have hr : Set.range f ⊆ Set.range ((ν) ⁻¹ᵁ W).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Opens.range_ι]
    apply (ν).mem_preimage.mpr
    dsimp only [f]
    rw [Hom.comp_apply, ← Hom.comp_apply (C.blowupComponent v).ι ν, ← h, Hom.comp_apply]
    exact j.mem_preimage.mp (g.mem_preimage.mp x.property)
  let l := IsOpenImmersion.lift ((ν) ⁻¹ᵁ W).ι f hr
  have hl : l ≫ ((ν) ⁻¹ᵁ W).ι = P.ι ≫ (C.blowupComponent v).ι :=
    IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion l := by
    have : IsOpenImmersion (l ≫ ((ν) ⁻¹ᵁ W).ι) :=
      hl.symm ▸ inferInstanceAs (IsOpenImmersion (P.ι ≫ (C.blowupComponent v).ι))
    exact IsOpenImmersion.of_comp l ((ν) ⁻¹ᵁ W).ι
  have : IsIso ((ν) ∣_ W) := (ν).le_isoLocus_iff.mp le_rfl
  have he : (g ∣_ U) ≫ U.ι ≫ j = l ≫ (ν ∣_ W) ≫ W.ι := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, h, ← Category.assoc,
      ← hl, Category.assoc, ← morphismRestrict_ι]
  have : IsOpenImmersion ((g ∣_ U) ≫ U.ι ≫ j) :=
    he.symm ▸ inferInstanceAs (IsOpenImmersion (l ≫ (ν ∣_ W) ≫ W.ι))
  have : IsImmersion (g ∣_ U) := IsImmersion.of_comp _ (U.ι ≫ j)
  have : IsClosedImmersion (g ∣_ U) :=
    .of_isPreimmersion _ (g ∣_ U).isClosedMap.isClosed_range
  have : Surjective (g ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict g U).flip ‹Surjective g›
  exact isIso_of_isClosedImmersion_of_surjective _

/-- A normalization component is uniquely isomorphic over the curve to any normal
closed subscheme with the same image. -/
theorem existsUnique_blowupComponentIso_of_range_eq {Y : Scheme.{u}} [IsNormalScheme Y]
    (j : Y ⟶ C) [IsClosedImmersion j] (v : V)
    (hrange : Set.range ((C.blowupComponent v).ι ≫ ν) = Set.range j) :
    ∃! e : (C.blowupComponent v).toScheme ≅ Y,
      e.hom ≫ j = (C.blowupComponent v).ι ≫ ν := by
  let f := (C.blowupComponent v).ι ≫ ν
  have hker : j.ker ≤ f.ker := by
    rw [j.ker_eq_vanishingIdeal_support]
    apply vanishingIdeal_le_ker_of_range_subset f
    rw [j.support_ker, j.isClosedEmbedding.isClosed_range.closure_eq]
    exact hrange.le
  let g := IsClosedImmersion.lift j f hker
  have hg : g ≫ j = f := IsClosedImmersion.lift_fac _ _ _
  have : Surjective g := ⟨fun y ↦ by
    obtain ⟨x, hx⟩ := hrange.ge (Set.mem_range_self y)
    exact ⟨x, j.isClosedEmbedding.injective (by rw [← Hom.comp_apply, hg, hx])⟩⟩
  have : IrreducibleSpace Y := g.surjective.irreducibleSpace g.continuous
  have : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  have : IsFinite ν := C.isFinite_blowupToBase_singularLocus
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have : IsClosedImmersion (C.blowupComponent v).ι := .of_isPreimmersion _ (by
    rw [Opens.range_ι, coe_blowupComponent]
    exact isClosed_of_mem_irreducibleComponents _ v.property)
  have : IsFinite (g ≫ j) := hg.symm ▸ inferInstanceAs (IsFinite f)
  have : IsFinite g := IsFinite.of_comp g j
  let U := j ⁻¹ᵁ (ν).isoLocus
  have hv : (η v : N) ∈ (C.blowupComponent v : Set N) := by
    rw [coe_blowupComponent]
    exact (genericPoints.isGenericPoint_ofComponent v).mem
  let y : (C.blowupComponent v).toScheme := ⟨η v, hv⟩
  have hy : g y ∈ U := by
    rw [Hom.mem_preimage, ← Hom.comp_apply, hg, Hom.comp_apply]
    exact C.blowupComponentGeneric_mem_isoLocus v
  have : IsModification g :=
    ⟨⟨U, U.isOpen.dense ⟨g y, hy⟩, (g ⁻¹ᵁ U).isOpen.dense ⟨y, hy⟩,
      C.isIso_morphismRestrict_of_blowupComponent j v g hg⟩⟩
  have := IsModification.isIso_of_isFinite g
  refine ⟨asIso g, hg, fun e he ↦ Iso.ext ?_⟩
  exact (cancel_mono j).mp (he.trans hg.symm)

end AlgebraicGeometry.Scheme
