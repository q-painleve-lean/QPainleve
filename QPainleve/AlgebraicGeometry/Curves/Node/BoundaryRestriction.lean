/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection
public import QPainleve.AlgebraicGeometry.Curves.Node.Multidegree
import QPainleve.AlgebraicGeometry.Curves.Degree.Pullback
import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Naturality
import QPainleve.AlgebraicGeometry.Curves.Node.NormalizationComponent
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite

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

variable {k : Type u} [Field k] {X : Scheme.{u}} {D : X.IdealSheafData}

local notation "C" => IdealSheafData.subscheme D
local notation "I" => Scheme.singularLocus k C
local notation "ν" => IdealSheafData.blowupToBase I
local notation "N" => IdealSheafData.blowup I
local notation "V" => irreducibleComponents N
local notation "η" => genericPoints.ofComponent

section Components

variable [D.subscheme.Over (Spec (.of k))] [PrestableFamily (D.subscheme ↘ Spec (.of k))]

/-- Each normalized component maps onto the reduced prime curve through the image of its
generic point. The image point has codimension one in the ambient scheme. -/
theorem range_blowupComponent_comp_subschemeι [IsLocallyNoetherian X]
    (hD : D.IsEffectiveCartier) (v : V) :
    ∃ p : CodimensionOnePoint X, (p : X) ∈ D.support ∧
      Set.range (((C).blowupComponent v).ι ≫ ν ≫ D.subschemeι) = closure {(p : X)} := by
  let p : CodimensionOnePoint X := ⟨D.subschemeι (ν (η v)),
    hD.coheight_subschemeι_of_coheight_eq_zero ((C).coheight_blowupComponentGeneric v)⟩
  exact ⟨p, D.range_subschemeι.le ⟨_, rfl⟩,
    (C).range_blowupComponent_comp v D.subschemeι D.subschemeι.isClosedMap⟩

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

/-- Every prime of a Cartier nodal boundary is the image of the generic point of
a component of its normalization. -/
theorem exists_subschemeι_blowupComponentGeneric_eq [IsLocallyNoetherian X]
    (hD : D.IsEffectiveCartier) {p : CodimensionOnePoint X} (hp : (p : X) ∈ D.support) :
    ∃ v : V, D.subschemeι (ν (η v)) = p.val := by
  obtain ⟨v, hv⟩ := hD.exists_range_blowupComponent_comp_subschemeι (k := k) hp
  rw [(C).range_blowupComponent_comp v D.subschemeι D.subschemeι.isClosedMap] at hv
  exact ⟨v, isGenericPoint_closure.eq (hv.symm ▸ isGenericPoint_closure)⟩

end Components

variable [X.Over (Spec (.of k))] [PrestableFamily (D.subscheme ↘ Spec (.of k))]

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

/-- On a smooth surface with a nodal Cartier boundary of rational components, the inverse
image of the normalization kernel under boundary restriction is the boundary orthogonal. -/
theorem pullback_blowupToBase_comp_subschemeι_eq_one_iff_mem_orthogonal
    (hD : D.IsEffectiveCartier)
    (hgenus : ∀ v : V, ((C).blowupComponent v).toScheme.genus k = 0)
    (a : Additive (LineBundleClass X)) :
    pullback (ν ≫ D.subschemeι) a.toMul = 1 ↔ a ∈ D.boundaryOrthogonal k := by
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
  rw [D.boundaryOrthogonal_def k, hD.pullback_blowupToBase_comp_subschemeι_eq_one_iff hX hgenus,
    Scheme.Opens.primeDivisorSpanCompl_eq_span_of_iUnion_closure _ Subtype.val hsupport,
    LinearMap.BilinForm.orthogonal, Submodule.mem_orthogonalBilin_span]
  simp only [Set.forall_mem_range, Chow.intersectionBilinForm_apply, toMul_ofMul,
    Subtype.forall]

variable (hD : D.IsEffectiveCartier)

local notation "PicZero" => MonoidHom.ker (pullbackHom ν)

local notation "K[" S "," J "]" =>
  Scheme.IdealSheafData.boundaryOrthogonal (X := S) J k

variable (hgenus : ∀ v : irreducibleComponents (D.subscheme.singularLocus k).blowup,
    (D.subscheme.blowupComponent (K := k) v).toScheme.genus k = 0)

/-- A boundary-orthogonal surface class restricts to a class in the normalization kernel
of a nodal Cartier boundary with genus-zero normalized components. -/
noncomputable def restrictBoundaryOrthogonal : Multiplicative K[X,D] →* PicZero :=
  let f := (pullbackHom D.subschemeι).comp
    (AddMonoidHom.toMultiplicativeLeft (K[X,D]).subtype.toAddMonoidHom)
  f.codRestrict PicZero fun a ↦ by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, pullbackHom_apply, pullbackHom_apply,
      pullback_comp]
    exact (hD.pullback_blowupToBase_comp_subschemeι_eq_one_iff_mem_orthogonal
      hgenus a.toAdd.val).mpr a.toAdd.property

/-- The underlying line-bundle class of a boundary-orthogonal restriction is the
ordinary pullback to the boundary. -/
@[simp]
theorem restrictBoundaryOrthogonal_apply (a : Multiplicative K[X,D]) :
    (hD.restrictBoundaryOrthogonal hgenus a).val = pullback D.subschemeι a.toAdd.val.toMul := by
  simp only [restrictBoundaryOrthogonal, MonoidHom.codRestrict_apply]
  exact pullbackHom_apply _ _

include hD hgenus in
/-- The class of an effective Cartier divisor disjoint from the boundary lies in the
boundary orthogonal. -/
theorem effectiveCartierClass_mem_orthogonal_of_disjoint {E : X.IdealSheafData}
    (hE : E.IsEffectiveCartier) (h : Disjoint (D.support : Set X) (E.support : Set X)) :
    Additive.ofMul (LineBundleClass.mk hE.toInvertibleSheaf)⁻¹ ∈ K[X,D] := by
  apply (hD.pullback_blowupToBase_comp_subschemeι_eq_one_iff_mem_orthogonal hgenus _).mp
  rw [toMul_ofMul, ← pullback_comp, hE.pullback_effectiveCartierClass_eq_one_of_disjoint h,
    pullback_one]

section Pullback

variable {Y : Scheme.{u}} [Y.Over (Spec (.of k))] [Y.IsProjectiveOver k] [IsIntegral Y]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  {E : Y.IdealSheafData} [PrestableFamily (E.subscheme ↘ Spec (.of k))]
  (hE : E.IsEffectiveCartier)

variable (hgenus' : ∀ v : irreducibleComponents (E.subscheme.singularLocus k).blowup,
    (E.subscheme.blowupComponent (K := k) v).toScheme.genus k = 0)

variable (f : X ⟶ Y) (g : D.subscheme ≅ E.subscheme) [g.hom.IsOver (Spec (.of k))]
  (hcomm : D.subschemeι ≫ f = g.hom ≫ E.subschemeι)

/-- A morphism inducing an isomorphism of the nodal boundaries pulls back classes
orthogonal to the target boundary to classes orthogonal to the source boundary. -/
noncomputable def boundaryOrthogonalPullback : K[Y,E] →ₗ[ℤ] K[X,D] :=
  ((pullbackHom f).toAdditive.toIntLinearMap.comp (K[Y,E]).subtype).codRestrict
    K[X,D] fun b ↦ by
      apply (hD.pullback_blowupToBase_comp_subschemeι_eq_one_iff_mem_orthogonal hgenus _).mp
      have hb := (g.nodalPicardKernelPullback (k := k)
        (hE.restrictBoundaryOrthogonal hgenus' (Multiplicative.ofAdd b))).property
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, AddMonoidHom.coe_toIntLinearMap,
        MonoidHom.coe_toAdditive, Function.comp_apply, toMul_ofMul, pullbackHom_apply]
      rw [← pullback_comp (D.subscheme.singularLocus k).blowupToBase D.subschemeι,
        pullback_comp D.subschemeι f, hcomm, ← pullback_comp g.hom E.subschemeι]
      simpa only [MonoidHom.mem_ker, pullbackHom_apply, Iso.coe_nodalPicardKernelPullback,
        restrictBoundaryOrthogonal_apply, toAdd_ofAdd] using hb

/-- The underlying boundary-orthogonal class is the ordinary pullback. -/
@[simp]
theorem coe_boundaryOrthogonalPullback (b : K[Y,E]) :
    (hD.boundaryOrthogonalPullback hgenus hE hgenus' f g hcomm b).val.toMul =
      pullback f b.val.toMul := by
  simp only [boundaryOrthogonalPullback, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive,
    Function.comp_apply, toMul_ofMul, pullbackHom_apply]

end Pullback

end SmoothSurface

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
