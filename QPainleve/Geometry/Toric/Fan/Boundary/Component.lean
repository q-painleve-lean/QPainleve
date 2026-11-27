/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Center
public import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
public import TauCeti.AlgebraicGeometry.IdealSheaf.Colon
public import TauCeti.Geometry.Toric.Algebraic.IntegralModel

import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Section
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Scheme.Regular.LocalRing

/-!
# Ray components of the toric boundary

A reduced ray divisor embeds in the reduced toric boundary. The ray's open orbit
belongs to that component alone. The binomial center is regular on its component,
and its ideal in the boundary restricts to a Cartier ideal on every component.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]

local notation "D" => Φ.boundaryIdeal inferInstance

variable (ρ : Φ.Ray) (hΦ : Φ.IsRegular)

/-- The reduced ray divisor is a closed subscheme of the reduced toric boundary. -/
theorem boundaryIdeal_le_rayBoundaryIdeal : D ≤ Φ.rayBoundaryIdeal hΦ ρ := by
  have : IsReduced (Φ.rayBoundaryIdeal hΦ ρ).subscheme := by
    rw [rayBoundaryIdeal_def]
    infer_instance
  rw [boundaryIdeal_def, ← ker_subschemeι (Φ.rayBoundaryIdeal hΦ ρ)]
  apply vanishingIdeal_le_ker_of_range_subset
  rw [range_subschemeι, coe_support_rayBoundaryIdeal]
  exact closure_minimal
    (Set.singleton_subset_iff.mpr (fun h ↦ Φ.rayBoundaryPoint_notMem_range_denseTorusι hΦ ρ
      (by simpa only [Φ.denseTorusι_eq inferInstance ⟨ρ.toCone⟩] using h)))
    (Φ.denseTorusι inferInstance).isOpenEmbedding.isOpen_range.isClosed_compl

/-- The closed immersion of a reduced ray component into the reduced toric boundary. -/
def Ray.boundaryComponentι : (Φ.rayBoundaryIdeal hΦ ρ).subscheme ⟶ (D).subscheme :=
  IsClosedImmersion.lift (D).subschemeι (Φ.rayBoundaryIdeal hΦ ρ).subschemeι
    (by simpa only [ker_subschemeι] using boundaryIdeal_le_rayBoundaryIdeal ρ hΦ)

@[reassoc (attr := simp)]
theorem Ray.boundaryComponentι_subschemeι :
    ρ.boundaryComponentι hΦ ≫ (D).subschemeι = (Φ.rayBoundaryIdeal hΦ ρ).subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

instance Ray.isClosedImmersion_boundaryComponentι :
    IsClosedImmersion (ρ.boundaryComponentι hΦ) := by
  have : IsClosedImmersion (ρ.boundaryComponentι hΦ ≫ (D).subschemeι) := by
    rw [Ray.boundaryComponentι_subschemeι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (D).subschemeι

/-- The closed ray components cover the reduced toric boundary. -/
theorem iUnion_range_boundaryComponentι :
    ⋃ ρ : Φ.Ray, Set.range (ρ.boundaryComponentι hΦ) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : (D).subschemeι x ∈ ((D).support : Set Φ.algebraicRealization) := by
    rw [← range_subschemeι]
    exact Set.mem_range_self _
  rw [Φ.support_boundaryIdeal_eq_iUnion_closure hΦ, Set.mem_iUnion] at hx
  obtain ⟨ρ, hρ⟩ := hx
  rw [← Φ.coe_support_rayBoundaryIdeal hΦ, ← range_subschemeι] at hρ
  obtain ⟨y, hy⟩ := hρ
  apply Set.mem_iUnion.mpr
  refine ⟨ρ, y, (D).subschemeι.isClosedEmbedding.injective ?_⟩
  simpa only [← Scheme.Hom.comp_apply, Ray.boundaryComponentι_subschemeι] using hy

variable (hdim : Module.finrank ℤ N = 2) {m : N →+ ℤ}
  (hm : m ρ.primitiveGenerator = 0) (hprim : Function.Surjective m)

local notation "chartIso" =>
  (Functor.mapIso (Over.forget (Spec (CommRingCat.of ℂ)))
    (Iso.symm (affineToricSchemeIsoAddMonoidAlgebraSpec (Fan.lattice Φ)
      (Subtype.val (Fan.Ray.toCone Φ ρ)))))

local notation "rayOrbit" =>
  (CategoryTheory.CategoryStruct.comp (Fan.Ray.orbitToRayChart (k := ℂ) ρ hdim hm hprim)
    (Iso.hom chartIso))

omit [Nonempty Φ.cones] in
private theorem comap_rayBoundaryIdeal_eq_ker_orbitToRayChart :
    (Φ.rayBoundaryIdeal hΦ ρ).comap (Φ.affineToricChartι ρ.toCone) =
      (rayOrbit).ker := by
  let σ := ρ.toCone
  let hσ := Φ.isToricCone σ.property
  let r := ρ.toToricRay Φ σ le_rfl
  let e := AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ (dualSemigroup Φ.lattice σ.val)
  have hmap : (rayChartIdeal Φ.lattice hσ r ℂ).map e.toRingEquiv =
      rayIdeal Φ.lattice hσ r := by
    obtain ⟨l, b, hb⟩ := (Fan.isRegular_iff.1 hΦ _ σ.property).exists_basis_sum
    rw [rayChartIdeal_eq_span_rayCoordinate _ _ _ _ hb, rayIdeal_eq_span _ _ hb,
      Ideal.map_span, Set.image_singleton]
    simp [e, MonoidAlgebra.of_apply]
  let t := chartIso
  let f := ρ.orbitToRayChart (k := ℂ) hdim hm hprim
  have hpb : IsPullback (f ≫ t.hom) (𝟙 _) t.inv f :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  rw [Φ.comap_rayBoundaryIdeal_eq_ofIdealTop hΦ ρ ρ.toCone le_rfl,
    ker_eq_comap_of_isPullback_of_isOpenImmersion t.inv hpb]
  change _ = (ρ.orbitToRayChart (k := ℂ) hdim hm hprim).ker.comap (chartIso).inv
  rw [Ray.ker_orbitToRayChart, Functor.mapIso_inv, Over.forget_map, Iso.symm_inv,
    affineToricSchemeIsoAddMonoidAlgebraSpec_hom_left, comap_ofIdealTop_map_ΓSpecIso_inv]
  change ofIdealTop ((rayIdeal Φ.lattice hσ r).map
      (Scheme.ΓSpecIso (.of (affineCoordinateRing Φ.lattice σ.val))).inv.hom) =
    ofIdealTop (((rayChartIdeal Φ.lattice hσ r ℂ).map e.toRingEquiv).map
      (Scheme.ΓSpecIso (.of (affineCoordinateRing Φ.lattice σ.val))).inv.hom)
  rw [hmap]

/-- The ray orbit as an open subscheme of its reduced ray divisor. -/
def Ray.orbitToComponent :
    Spec (.of (LaurentPolynomial ℂ)) ⟶ (Φ.rayBoundaryIdeal hΦ ρ).subscheme :=
  IsClosedImmersion.lift (Φ.rayBoundaryIdeal hΦ ρ).subschemeι
    (rayOrbit ≫ Φ.affineToricChartι ρ.toCone) (by
      rw [ker_subschemeι, Scheme.Hom.ker_comp,
        ← comap_rayBoundaryIdeal_eq_ker_orbitToRayChart ρ hΦ hdim hm hprim]
      exact le_map_comap _ _)

omit [Nonempty Φ.cones] in
/-- The ray orbit inclusion into the fan scheme factors through the ray divisor. -/
@[reassoc (attr := simp)]
theorem Ray.orbitToComponent_subschemeι :
    ρ.orbitToComponent hΦ hdim hm hprim ≫ (Φ.rayBoundaryIdeal hΦ ρ).subschemeι =
      rayOrbit ≫ Φ.affineToricChartι ρ.toCone :=
  IsClosedImmersion.lift_fac _ _ _

instance Ray.isOpenImmersion_orbitToComponent :
    IsOpenImmersion (ρ.orbitToComponent hΦ hdim hm hprim) :=
  MorphismProperty.of_isPullback
    (isPullback_of_isClosedImmersion (rayOrbit)
      (Φ.rayBoundaryIdeal hΦ ρ).subschemeι _ (Φ.affineToricChartι ρ.toCone)
      (ρ.orbitToComponent_subschemeι hΦ hdim hm hprim).symm
      (by rw [ker_subschemeι, comap_rayBoundaryIdeal_eq_ker_orbitToRayChart ρ hΦ hdim hm hprim]))
    (Φ.isOpenImmersion_affineToricChartι ρ.toCone)

/-- The ray orbit inclusion into the full boundary factors through the ray divisor. -/
@[reassoc (attr := simp)]
theorem Ray.orbitToComponent_boundaryComponentι :
    ρ.orbitToComponent hΦ hdim hm hprim ≫ ρ.boundaryComponentι hΦ =
      ρ.orbitToBoundary hdim hm hprim := by
  rw [← cancel_mono (D).subschemeι]
  simp

/-- The open ray orbit is a morphism over `ℂ`. -/
instance Ray.isOver_orbitToComponent :
    (ρ.orbitToComponent hΦ hdim hm hprim).IsOver (Spec (.of ℂ)) where
  comp_over := by
    rw [over_eq_subschemeι_comp, ← Category.assoc, ρ.orbitToComponent_subschemeι,
      Category.assoc, Fan.algebraicRealization_over]
    simpa only [ρ.orbitToBoundary_comp_subschemeι_assoc, Category.assoc, specOverSpec_over,
      Spec.algebraMap] using
      ρ.orbitToBoundary_comp_algebraicRealizationStructureMap hdim hm hprim

/-- The binomial center on its own reduced ray divisor. -/
def Ray.binomialCenterOnComponent (c : ℂˣ) :
    Spec (.of ℂ) ⟶ (Φ.rayBoundaryIdeal hΦ ρ).subscheme :=
  Spec.map (CommRingCat.ofHom (laurentEval ((-1 : ℂˣ) * c⁻¹)).toRingHom) ≫
    ρ.orbitToComponent hΦ hdim hm hprim

omit [Nonempty Φ.cones] in
/-- In Laurent coordinates the center is evaluation at the root `-c⁻¹` of the binomial. -/
theorem Ray.binomialCenterOnComponent_eq (c : ℂˣ) :
    ρ.binomialCenterOnComponent hΦ hdim hm hprim c =
      Spec.map (CommRingCat.ofHom (laurentEval ((-1 : ℂˣ) * c⁻¹)).toRingHom) ≫
        ρ.orbitToComponent hΦ hdim hm hprim :=
  (rfl)

/-- The center on its ray component maps to the binomial center on the full boundary. -/
@[reassoc (attr := simp)]
theorem Ray.binomialCenterOnComponent_boundaryComponentι (c : ℂˣ) :
    ρ.binomialCenterOnComponent hΦ hdim hm hprim c ≫ ρ.boundaryComponentι hΦ =
      ρ.binomialCenterOnBoundary hdim hm hprim c := by
  rw [Ray.binomialCenterOnComponent_eq, Category.assoc, Ray.orbitToComponent_boundaryComponentι]
  apply (cancel_mono (D).subschemeι).mp
  rw [Category.assoc, Ray.orbitToBoundary_comp_subschemeι,
    Ray.binomialCenterOnBoundary_comp_subschemeι, Ray.binomialCenter_def,
    Ray.orbitToRayChart_def, Functor.mapIso_hom, Over.forget_map, Iso.symm_hom,
    affineToricSchemeIsoAddMonoidAlgebraSpec_inv_left, Category.assoc,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
    Ray.binomialCenterEval_def]
  rfl

private theorem boundaryComponentι_binomialCenterOnComponent_apply (c : ℂˣ) (z : Spec (.of ℂ)) :
    ρ.boundaryComponentι hΦ (ρ.binomialCenterOnComponent hΦ hdim hm hprim c z) =
      ρ.binomialCenterOnBoundary hdim hm hprim c z := by
  rw [← Scheme.Hom.comp_apply, Ray.binomialCenterOnComponent_boundaryComponentι]

private theorem smoothOfRelativeDimension_orbitToComponent :
    SmoothOfRelativeDimension 1
      (ρ.orbitToComponent hΦ hdim hm hprim ≫
        (Φ.rayBoundaryIdeal hΦ ρ).subschemeι ≫ Φ.algebraicRealizationStructureMap) := by
  have h : ρ.orbitToComponent hΦ hdim hm hprim ≫ (Φ.rayBoundaryIdeal hΦ ρ).subschemeι =
      ρ.orbitToBoundary hdim hm hprim ≫ (D).subschemeι := by
    rw [← ρ.boundaryComponentι_subschemeι hΦ, Ray.orbitToComponent_boundaryComponentι_assoc]
  simpa only [← Category.assoc, h] using
    ρ.smoothOfRelativeDimension_orbitToBoundary hdim hm hprim

private theorem isRegularLocalRing_stalk_binomialCenterOnComponent (c : ℂˣ) :
    IsRegularLocalRing ((Φ.rayBoundaryIdeal hΦ ρ).subscheme.presheaf.stalk
      (ρ.binomialCenterOnComponent hΦ hdim hm hprim c (IsLocalRing.closedPoint ℂ))) := by
  let j := ρ.orbitToComponent hΦ hdim hm hprim
  let f := j ≫ (Φ.rayBoundaryIdeal hΦ ρ).subschemeι ≫ Φ.algebraicRealizationStructureMap
  have : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_orbitToComponent ρ hΦ hdim
    hm hprim
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion j _).mpr
    (isRegularLocalRing_stalk_of_smooth f _)

private theorem isEffectiveCartier_ker_binomialCenterOnComponent (c : ℂˣ) :
    (ρ.binomialCenterOnComponent hΦ hdim hm hprim c).ker.IsEffectiveCartier := by
  let j := ρ.orbitToComponent hΦ hdim hm hprim
  let U := j.opensRange
  let t := ρ.binomialCenterOnComponent hΦ hdim hm hprim c
  let f := (Φ.rayBoundaryIdeal hΦ ρ).subschemeι ≫ Φ.algebraicRealizationStructureMap
  have hf : t ≫ f = 𝟙 _ := by
    simp only [t, f, ← ρ.boundaryComponentι_subschemeι hΦ, ← Category.assoc,
      Ray.binomialCenterOnComponent_boundaryComponentι,
      Ray.binomialCenterOnBoundary_comp_subschemeι, Ray.binomialCenter_comp_structureMap]
  have : IsClosedImmersion (t ≫ ρ.boundaryComponentι hΦ) := by
    simp only [t, Ray.binomialCenterOnComponent_boundaryComponentι]
    infer_instance
  have : IsClosedImmersion t := IsClosedImmersion.of_comp_isClosedImmersion t
    (ρ.boundaryComponentι hΦ)
  have hU : Set.range t ⊆ U := by
    simpa only [t, Ray.binomialCenterOnComponent, U, j, Scheme.Hom.coe_opensRange,
      Scheme.Hom.comp_base, TopCat.coe_comp] using Set.range_comp_subset_range _ _
  let a := IsOpenImmersion.isoOfRangeEq j U.ι U.range_ι.symm
  have ha : a.hom ≫ U.ι = j := IsOpenImmersion.isoOfRangeEq_hom_fac j U.ι U.range_ι.symm
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{0} 1) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).respectsIso
  have : SmoothOfRelativeDimension 1 (U.ι ≫ f) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) a.hom,
      ← Category.assoc, ha]
    exact smoothOfRelativeDimension_orbitToComponent ρ hΦ hdim hm hprim
  exact Scheme.Hom.isEffectiveCartier_ker_of_comp_eq_id t hf U hU

private theorem binomialCenter_notMem_range_boundaryComponentι {τ : Φ.Ray} (hne : ρ ≠ τ)
    (c : ℂˣ) :
    ρ.binomialCenterOnBoundary hdim hm hprim c (IsLocalRing.closedPoint ℂ) ∉
      Set.range (τ.boundaryComponentι hΦ) := by
  have hle : ¬ τ.toCone ≤ ρ.toCone := by
    intro h
    have heq : τ.toToricRay Φ ρ.toCone h = ρ.toToricRay Φ ρ.toCone le_rfl := by
      apply ToricRay.eq_of_toPointedCone_le (Φ.isToricCone ρ.toCone.property).salient
      simpa only [Ray.toPointedCone_toToricRay] using Subtype.coe_le_coe.mpr h
    exact hne (Subtype.ext (Subtype.ext
      (by simpa only [Ray.toPointedCone_toToricRay] using
        (congrArg ToricRay.toPointedCone heq).symm)))
  let a := Φ.affineToricChartι ρ.toCone
  let z : Spec (.of ℂ) := IsLocalRing.closedPoint ℂ
  have hdisj : a ⁻¹ᵁ (Φ.rayBoundaryIdeal hΦ τ).support.compl = ⊤ :=
    (comap_eq_top_iff _ _).mp (Φ.comap_rayBoundaryIdeal_eq_top hΦ τ ρ.toCone hle)
  have hpre (x : Φ.affineToricChart ρ.toCone) :
      x ∈ a ⁻¹ᵁ (Φ.rayBoundaryIdeal hΦ τ).support.compl := by
    rw [hdisj]
    trivial
  have hpt : ρ.binomialCenter hdim hm hprim c z ∈
      (Φ.rayBoundaryIdeal hΦ τ).support.compl := by
    rw [Ray.binomialCenter_def, Scheme.Hom.comp_apply]
    exact hpre _
  rintro ⟨q, hq⟩
  have heq := congrArg (fun x ↦ (D).subschemeι x) hq
  simp only [← Scheme.Hom.comp_apply, Ray.boundaryComponentι_subschemeι] at heq
  have hcenter := congrArg (fun g : Spec (.of ℂ) ⟶ Φ.algebraicRealization ↦ g z)
    (ρ.binomialCenterOnBoundary_comp_subschemeι hdim hm hprim c)
  rw [Scheme.Hom.comp_apply] at hcenter
  have hqmem : (Φ.rayBoundaryIdeal hΦ τ).subschemeι q ∈
      ((Φ.rayBoundaryIdeal hΦ τ).support : Set Φ.algebraicRealization) :=
    (Φ.rayBoundaryIdeal hΦ τ).range_subschemeι ▸ Set.mem_range_self q
  exact hpt ((heq.trans hcenter) ▸ hqmem)
variable (c : ℂˣ) (τ : Φ.Ray)

local notation "center" => Ray.binomialCenterOnBoundary ρ hdim hm hprim c
local notation "z" => (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ))

/-- A binomial center lies on precisely the boundary component of its ray. -/
theorem Ray.binomialCenterOnBoundary_mem_range_boundaryComponentι_iff :
    center z ∈ Set.range (τ.boundaryComponentι hΦ) ↔ ρ = τ := by
  refine ⟨fun h ↦ of_not_not (fun hn ↦
    binomialCenter_notMem_range_boundaryComponentι ρ hΦ hdim hm hprim hn c h), ?_⟩
  rintro rfl
  exact ⟨_, boundaryComponentι_binomialCenterOnComponent_apply ρ hΦ hdim hm hprim c z⟩

/-- In the ambient toric surface a binomial center belongs exactly to its own ray divisor. -/
@[simp]
theorem Ray.binomialCenter_mem_support_rayBoundaryIdeal_iff :
    ρ.binomialCenter hdim hm hprim c z ∈ (Φ.rayBoundaryIdeal hΦ τ).support ↔ ρ = τ := by
  let q : Spec (.of ℂ) := z
  have h : (D).subschemeι (center q) = ρ.binomialCenter hdim hm hprim c q :=
    (Scheme.Hom.comp_apply (center) (D).subschemeι q).symm.trans
      (congrArg (fun f : Spec (.of ℂ) ⟶ Φ.algebraicRealization ↦ f q)
        (ρ.binomialCenterOnBoundary_comp_subschemeι hdim hm hprim c))
  have hrange : Set.range (τ.boundaryComponentι hΦ ≫ (D).subschemeι) =
      (D).subschemeι '' Set.range (τ.boundaryComponentι hΦ) := by
    rw [← Set.range_comp']
    exact congrArg Set.range (funext (Scheme.Hom.comp_apply (τ.boundaryComponentι hΦ)
      (D).subschemeι))
  rw [← SetLike.mem_coe, ← range_subschemeι, ← τ.boundaryComponentι_subschemeι hΦ, hrange,
    ← h, (D).subschemeι.isClosedEmbedding.injective.mem_set_image]
  exact ρ.binomialCenterOnBoundary_mem_range_boundaryComponentι_iff hΦ hdim hm hprim c τ

/-- A binomial point lies on its ray divisor away from the residual toric boundary. -/
theorem Ray.binomialCenter_mem_support_sdiff_colon :
    ρ.binomialCenter hdim hm hprim c (z : Spec (.of ℂ)) ∈
      ((Φ.rayBoundaryIdeal hΦ ρ).support : Set Φ.algebraicRealization) \
        ((D).colon (Φ.rayBoundaryIdeal hΦ ρ)).support := by
  let j := Φ.affineToricChartι ρ.toCone
  let C := Φ.rayBoundaryIdeal hΦ ρ
  have hDC : D ≤ C := boundaryIdeal_le_rayBoundaryIdeal ρ hΦ
  have hC := Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ
  have hcart : (C.comap j).IsEffectiveCartier := hC.comap j
  have heq : (D).comap j = C.comap j := by
    rw [comap_rayBoundaryIdeal_eq_ker_orbitToRayChart ρ hΦ hdim hm hprim]
    simpa only [ker_subschemeι] using
      ker_eq_comap_of_isPullback _ (ρ.isPullback_orbitToBoundary hdim hm hprim) |>.symm
  have hres : ((D).colon C).comap j = ⊤ := by
    rw [comap_colon _ _ hC.locallyPrincipal hDC j hcart, heq, colon_self]
  constructor
  · exact (ρ.binomialCenter_mem_support_rayBoundaryIdeal_iff hΦ hdim hm hprim c ρ).mpr rfl
  · have hx : ρ.binomialCenter hdim hm hprim c (z : Spec (.of ℂ)) ∈ Set.range j := by
      rw [Ray.binomialCenter_def]
      exact Set.mem_range_self _
    obtain ⟨x, hx⟩ := hx
    rw [← hx]
    intro hmem
    have hx' : x ∈ (((D).colon C).comap j).support := by
      simpa only [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage]
        using hmem
    rwa [hres, support_top] at hx'

/-- On a different ray, the restricted binomial center ideal is the unit ideal. -/
theorem Ray.comap_ker_binomialCenterOnBoundary_eq_top_of_ne (hne : ρ ≠ τ) :
    (center).ker.comap (τ.boundaryComponentι hΦ) = ⊤ := by
  have hnot :=
    (ρ.binomialCenterOnBoundary_mem_range_boundaryComponentι_iff hΦ hdim hm hprim c τ).not.mpr hne
  rw [comap_eq_top_iff, ← Opens.coe_eq_univ, Scheme.Hom.coe_preimage, Closeds.coe_compl,
    Scheme.Hom.support_ker, (center).isClosedEmbedding.isClosed_range.closure_eq,
    Set.range_eq_singleton (f := center) (fun q ↦ congrArg center (Subsingleton.elim q z)),
    Set.eq_univ_iff_forall]
  exact fun q hq ↦ hnot ⟨q, hq⟩

/-- The ideal of a binomial center restricts to a Cartier ideal on every reduced ray
component. Away from the ray of the center the restricted ideal is the unit ideal. -/
theorem Ray.isEffectiveCartier_comap_ker_binomialCenterOnBoundary :
    ((center).ker.comap (τ.boundaryComponentι hΦ)).IsEffectiveCartier := by
  by_cases h : ρ = τ
  · subst τ
    have hcomp := ρ.binomialCenterOnComponent_boundaryComponentι hΦ hdim hm hprim c
    rw [← hcomp, Scheme.Hom.comap_ker_comp_of_isClosedImmersion]
    exact isEffectiveCartier_ker_binomialCenterOnComponent ρ hΦ hdim hm hprim c
  · rw [ρ.comap_ker_binomialCenterOnBoundary_eq_top_of_ne hΦ hdim hm hprim c τ h]
    exact isEffectiveCartier_top _

/-- A point on a reduced ray component above a binomial center has regular local ring. -/
theorem Ray.isRegularLocalRing_stalk_of_boundaryComponentι_eq_binomialCenter
    (q : (Φ.rayBoundaryIdeal hΦ τ).subscheme) (hq : τ.boundaryComponentι hΦ q = center z) :
    IsRegularLocalRing ((Φ.rayBoundaryIdeal hΦ τ).subscheme.presheaf.stalk q) := by
  have h :=
    (ρ.binomialCenterOnBoundary_mem_range_boundaryComponentι_iff hΦ hdim hm hprim c τ).mp ⟨q, hq⟩
  subst τ
  let t := ρ.binomialCenterOnComponent hΦ hdim hm hprim c
  have hEq : q = t z := (ρ.boundaryComponentι hΦ).isClosedEmbedding.injective
    (hq.trans (boundaryComponentι_binomialCenterOnComponent_apply ρ hΦ hdim hm hprim c z).symm)
  exact hEq ▸ isRegularLocalRing_stalk_binomialCenterOnComponent ρ hΦ hdim hm hprim c

end TauCeti.Toric.Fan
