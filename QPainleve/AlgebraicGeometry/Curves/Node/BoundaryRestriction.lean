/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import QPainleve.AlgebraicGeometry.CartierDivisor.Excision
public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection
public import QPainleve.AlgebraicGeometry.Curves.Node.Multidegree
import QPainleve.AlgebraicGeometry.Curves.Degree.Pullback
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.SchematicDensity
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
import TauCeti.Topology.Sober

/-!
# Restricting surface classes to a nodal boundary

For a Cartier boundary with rational normalization components, the surface classes whose
restriction belongs to `Pic⁰` of the boundary are exactly those orthogonal to the prime
boundary classes. This is the domain of the boundary period map in Gross, Hacking and Keel,
*Moduli of surfaces with an anti-canonical cycle*, §2.
-/

public section

open CategoryTheory Order TopologicalSpace TauCeti TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.LineBundleClass

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ Spec (.of k))]

local notation "C" => IdealSheafData.subscheme D
local notation "I" => Scheme.singularLocus k C
local notation "ν" => IdealSheafData.blowupToBase I
local notation "N" => IdealSheafData.blowup I
local notation "V" => irreducibleComponents N
local notation "η" => genericPoints.ofComponent

private theorem blowupComponentGeneric_mem_isoLocus (v : V) : ν (η v) ∈ (ν).isoLocus := by
  have : IsFinite ν := (C).isFinite_blowupToBase_singularLocus
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have : IsNoetherian N := isNoetherian_of_finiteType (ν ≫ C ↘ Spec (.of k))
  have hcartier := (I).isEffectiveCartier_comap_blowupToBase
  have := hcartier.isSchemeTheoreticallyDominant_support_compl_ι
  have hdense : Dense (((I).comap ν).support : Set N)ᶜ := by
    simpa only [DenseRange, Scheme.Opens.range_ι, Closeds.coe_compl] using
      (Scheme.Opens.ι ((I).comap ν).support.compl).denseRange
  have hv : IsOpen (v : Set N) := by
    rw [← (C).coe_blowupComponent v]
    exact ((C).blowupComponent v).isOpen
  obtain ⟨y, hyv, hy⟩ := hdense.inter_open_nonempty _ hv v.property.1.nonempty
  have hη : (η v : N) ∈ ((I).comap ν).support.compl :=
    ((genericPoints.isGenericPoint_ofComponent v).specializes hyv).mem_open
      ((I).comap ν).support.compl.isOpen hy
  have hIso := (C).isIso_blowupToBase_singularLocus_restrict_smoothLocus (R := k)
  apply (ν).le_isoLocus_iff.mpr hIso
  apply not_not.mp
  exact ((C).mem_support_singularLocus_iff_notMem_smoothLocus (ν (η v))).not.mp
    (by simpa only [← SetLike.mem_coe, Closeds.coe_compl, Set.mem_compl_iff,
      support_comap, Closeds.coe_preimage, Set.mem_preimage] using hη)

private theorem coheight_image_blowupComponentGeneric [IsLocallyNoetherian X]
    (hD : D.IsEffectiveCartier) (v : V) : coheight (D.subschemeι (ν (η v))) = 1 := by
  have hgeneric : IsMax (η v : N) := fun y hy ↦
    le_of_eq (TauCeti.mem_genericPoints_iff.mp (η v).property y (Scheme.le_iff_specializes.mp hy))
  have hco : coheight (ν (η v)) = 0 :=
    ((ν).coheight_eq_of_apply_mem_isoLocus (blowupComponentGeneric_mem_isoLocus v)).trans
      hgeneric.coheight_eq_zero
  have hdim := hD.ringKrullDim_stalk_add_one (ν (η v))
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hco, WithBot.coe_zero,
    zero_add, ← WithBot.coe_one, WithBot.coe_inj] at hdim
  exact hdim.symm

/-- Each normalized component maps onto the reduced prime curve through the image of its
generic point. The image point has codimension one in the ambient scheme. -/
theorem range_blowupComponent_comp_subschemeι [IsLocallyNoetherian X]
    (hD : D.IsEffectiveCartier) (v : V) :
    ∃ p : CodimensionOnePoint X, (p : X) ∈ D.support ∧
      Set.range (((C).blowupComponent v).ι ≫ ν ≫ D.subschemeι) = closure {(p : X)} := by
  let p : CodimensionOnePoint X := ⟨D.subschemeι (ν (η v)),
    coheight_image_blowupComponentGeneric hD v⟩
  have : IsFinite ν := (C).isFinite_blowupToBase_singularLocus
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  let f := ν ≫ D.subschemeι
  refine ⟨p, D.range_subschemeι.le ⟨_, rfl⟩, ?_⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    (C).coe_blowupComponent v, ← (genericPoints.isGenericPoint_ofComponent v).def,
    ← f.isClosedMap.closure_image_eq_of_continuous f.continuous, Set.image_singleton]
  rfl

/-- Every prime curve of the boundary is the image of a normalized component. -/
theorem exists_range_blowupComponent_comp_subschemeι [IsLocallyNoetherian X]
    (hD : D.IsEffectiveCartier) {p : CodimensionOnePoint X} (hp : (p : X) ∈ D.support) :
    ∃ v : V, Set.range (((C).blowupComponent v).ι ≫ ν ≫ D.subschemeι) = closure {(p : X)} := by
  have : Surjective ν := (C).surjective_blowupToBase_singularLocus
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  obtain ⟨x, hx⟩ := D.range_subschemeι.ge hp
  obtain ⟨y, hy⟩ := (ν).surjective x
  let v := irreducibleComponentOf y
  have hyv : y ∈ ((C).blowupComponent v : Set N) := by
    rw [(C).coe_blowupComponent v]
    exact mem_irreducibleComponentOf y
  obtain ⟨q, -, hq⟩ := hD.range_blowupComponent_comp_subschemeι v
  have hqp : (p : X) ∈ closure {(q : X)} := by
    rw [← hq]
    let y' : ((C).blowupComponent v).toScheme := ⟨y, hyv⟩
    refine ⟨y', ?_⟩
    have hy' : ((C).blowupComponent v).ι y' = y := (rfl)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy', hy, hx]
  have he := CodimensionOnePoint.eq_of_specializes (specializes_iff_mem_closure.mpr hqp)
  exact ⟨v, he ▸ hq⟩

section Surface

variable [X.IsProjectiveOver k] [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

private theorem eulerDegree_pullback_blowupComponent_eq_zero_iff [Infinite k]
    (hX : topologicalKrullDim X = 2) (v : V) (p : CodimensionOnePoint X)
    (hrange : Set.range (((C).blowupComponent v).ι ≫ ν ≫ D.subschemeι) = closure {(p : X)})
    (a : LineBundleClass X) :
    eulerDegree k (pullback (((C).blowupComponent v).ι ≫ ν ≫ D.subschemeι) a) = 0 ↔
      Chow.classIntersectionNumber k X (primeDivisorClass p) a = 0 := by
  let L := ((C).blowupComponent v).toScheme
  let f := ((C).blowupComponent v).ι ≫ ν ≫ D.subschemeι
  let P := vanishingIdeal ⟨closure {(p : X)}, isClosed_closure⟩
  let g := IsClosedImmersion.lift P.subschemeι f (by
    rw [ker_subschemeι]
    exact vanishingIdeal_le_ker_of_range_subset f hrange.le)
  have hfac : g ≫ P.subschemeι = f := IsClosedImmersion.lift_fac _ _ _
  have hg : Surjective g := by
    constructor
    intro y
    have hy := P.range_subschemeι.le (Set.mem_range_self y)
    obtain ⟨z, hz⟩ : P.subschemeι y ∈ Set.range f := by
      rw [hrange]
      simpa only [P, coe_support_vanishingIdeal, Closeds.coe_mk] using hy
    exact ⟨z, P.subschemeι.isClosedEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, hfac, hz])⟩
  have : IsFinite ν := (C).isFinite_blowupToBase_singularLocus
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have : IsClosedImmersion ((C).blowupComponent v).ι := .of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι, (C).coe_blowupComponent v]
    exact isClosed_of_mem_irreducibleComponents _ v.property)
  have : IsFinite f := inferInstanceAs
    (IsFinite (((C).blowupComponent v).ι ≫ ν ≫ D.subschemeι))
  have : IsFinite (g ≫ P.subschemeι) := by
    rw [hfac]
    infer_instance
  have : IsFinite g := IsFinite.of_comp g P.subschemeι
  have hP := QPainleve.topologicalKrullDim_vanishingIdeal_subscheme k hX p
  have : P.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k P.subschemeι
  have : P.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, hP⟩
  have : L.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, (g.topologicalKrullDim_eq_of_isClosedMap_of_surjective
      g.isClosedMap).trans hP⟩
  have : g.IsOver (Spec (.of k)) := ⟨by
    rw [← comp_over P.subschemeι, ← Category.assoc, hfac]
    simp [f, Category.assoc]⟩
  obtain ⟨n, hn, hdegree⟩ := exists_pos_eulerDegree_pullback (k := k) g
  dsimp only [f] at hfac
  rw [← hfac, ← pullback_comp, hdegree,
    Chow.classIntersectionNumber_comm,
    Chow.classIntersectionNumber_primeDivisorClass_eq_intersectionNumber k hX,
    intersectionNumber_def, mul_eq_zero]
  simp only [Nat.cast_eq_zero, hn.ne', false_or, P]

/-- Restriction to a nodal Cartier boundary with genus-zero normalization components has
multidegree zero exactly for classes orthogonal to every prime boundary class. -/
theorem pullback_blowupToBase_comp_subschemeι_eq_one_iff
    (hD : D.IsEffectiveCartier) [IsAlgClosed k] (hX : topologicalKrullDim X = 2)
    (hgenus : ∀ v : V, ((C).blowupComponent v).toScheme.genus k = 0) (a : LineBundleClass X) :
    pullback (ν ≫ D.subschemeι) a = 1 ↔
      ∀ p : CodimensionOnePoint X, (p : X) ∈ D.support →
        Chow.classIntersectionNumber k X (primeDivisorClass p) a = 0 := by
  rw [← pullback_comp, (C).pullback_blowupToBase_singularLocus_eq_one_iff hgenus]
  simp only [pullback_comp, Category.assoc]
  refine ⟨fun h p hp ↦ ?_, fun h v ↦ ?_⟩
  · obtain ⟨v, hv⟩ := hD.exists_range_blowupComponent_comp_subschemeι (k := k) hp
    exact (eulerDegree_pullback_blowupComponent_eq_zero_iff hX v p hv a).mp (h v)
  · obtain ⟨p, hp, hv⟩ := hD.range_blowupComponent_comp_subschemeι v
    exact (eulerDegree_pullback_blowupComponent_eq_zero_iff hX v p hv a).mpr (h p hp)

end Surface

section SmoothSurface

variable [IsAlgClosed k] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "M" => Scheme.Opens.primeDivisorSpanCompl (Closeds.compl (D.support))
local notation "B" => Chow.intersectionBilinForm k X

/-- On a smooth surface with a nodal Cartier boundary of rational components, the inverse
image of the normalization kernel under boundary restriction is the boundary orthogonal. -/
theorem pullback_blowupToBase_comp_subschemeι_eq_one_iff_mem_orthogonal
    (hD : D.IsEffectiveCartier)
    (hgenus : ∀ v : V, ((C).blowupComponent v).toScheme.genus k = 0)
    (a : Additive (LineBundleClass X)) :
    letI := isNoetherian_of_finiteType (X ↘ Spec (.of k))
    letI := (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    pullback (ν ≫ D.subschemeι) a.toMul = 1 ↔ a ∈ (B).orthogonal M := by
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  let := (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)
  let P := {p : CodimensionOnePoint X // (p : X) ∈ D.support}
  have hsupport : (D.support.compl : Set X)ᶜ = ⋃ p : P, closure {(p.val : X)} := by
    rw [Closeds.coe_compl, compl_compl]
    ext x
    rw [Set.mem_iUnion]
    exact hD.mem_support_iff_exists_codimensionOnePoint.trans
      ⟨fun ⟨p, hp, h⟩ ↦ ⟨⟨p, hp⟩, specializes_iff_mem_closure.mp h⟩,
        fun ⟨p, h⟩ ↦ ⟨p.val, p.property, specializes_iff_mem_closure.mpr h⟩⟩
  rw [hD.pullback_blowupToBase_comp_subschemeι_eq_one_iff hX hgenus,
    Scheme.Opens.primeDivisorSpanCompl_eq_span_of_iUnion_closure _ Subtype.val hsupport,
    LinearMap.BilinForm.orthogonal, Submodule.mem_orthogonalBilin_span]
  simp only [Set.forall_mem_range, Chow.intersectionBilinForm_apply, toMul_ofMul,
    Subtype.forall]

end SmoothSurface

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
