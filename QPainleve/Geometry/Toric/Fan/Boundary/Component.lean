/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Center
public import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
public import TauCeti.AlgebraicGeometry.IdealSheaf.Colon

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

universe u

variable (k : Type u) [Field k] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]

local notation "D" => Φ.toricBoundaryIdeal k inferInstance

variable (ρ : Φ.Ray) (hΦ : Φ.IsRegular)

/-- The reduced ray divisor is a closed subscheme of the reduced toric boundary. -/
theorem boundaryIdeal_le_rayBoundaryIdeal : D ≤ Φ.rayDivisorIdeal k hΦ ρ := by
  have : IsReduced (Φ.rayDivisorIdeal k hΦ ρ).subscheme := by
    rw [rayDivisorIdeal_def k]
    infer_instance
  rw [toricBoundaryIdeal_def k, ← ker_subschemeι (Φ.rayDivisorIdeal k hΦ ρ)]
  apply vanishingIdeal_le_ker_of_range_subset
  rw [range_subschemeι, coe_support_rayDivisorIdeal k]
  let hbot := Φ.bot_mem (inferInstance : Nonempty Φ.cones).some.property
  exact closure_minimal
    (Set.singleton_subset_iff.mpr (Φ.rayBoundaryChartPoint_notMem_zeroChart (R := k) hΦ ρ hbot))
    (Φ.affineChartι k ⟨⊥, hbot⟩).isOpenEmbedding.isOpen_range.isClosed_compl

/-- The closed immersion of a reduced ray component into the reduced toric boundary. -/
def Ray.boundaryComponentι : (Φ.rayDivisorIdeal k hΦ ρ).subscheme ⟶ (D).subscheme :=
  IsClosedImmersion.lift (D).subschemeι (Φ.rayDivisorIdeal k hΦ ρ).subschemeι
    (by simpa only [ker_subschemeι] using boundaryIdeal_le_rayBoundaryIdeal k ρ hΦ)

@[reassoc (attr := simp)]
theorem Ray.boundaryComponentι_subschemeι :
    ρ.boundaryComponentι k hΦ ≫ (D).subschemeι = (Φ.rayDivisorIdeal k hΦ ρ).subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

instance Ray.isClosedImmersion_boundaryComponentι :
    IsClosedImmersion (ρ.boundaryComponentι k hΦ) := by
  have : IsClosedImmersion (ρ.boundaryComponentι k hΦ ≫ (D).subschemeι) := by
    rw [Ray.boundaryComponentι_subschemeι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (D).subschemeι

/-- The closed ray components cover the reduced toric boundary. -/
theorem iUnion_range_boundaryComponentι :
    ⋃ ρ : Φ.Ray, Set.range (ρ.boundaryComponentι k hΦ) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : (D).subschemeι x ∈ ((D).support : Set (Φ.finiteFanScheme k)) := by
    rw [← range_subschemeι]
    exact Set.mem_range_self _
  rw [Φ.support_toricBoundaryIdeal_eq_iUnion_closure k hΦ, Set.mem_iUnion] at hx
  obtain ⟨ρ, hρ⟩ := hx
  rw [← Φ.coe_support_rayDivisorIdeal k hΦ, ← range_subschemeι] at hρ
  obtain ⟨y, hy⟩ := hρ
  apply Set.mem_iUnion.mpr
  refine ⟨ρ, y, (D).subschemeι.isClosedEmbedding.injective ?_⟩
  simpa only [← Scheme.Hom.comp_apply, Ray.boundaryComponentι_subschemeι] using hy

variable (hdim : Module.finrank ℤ N = 2) {m : N →+ ℤ}
  (hm : m ρ.primitiveGenerator = 0) (hprim : Function.Surjective m)

omit [Nonempty Φ.cones] in
private theorem comap_rayBoundaryIdeal_eq_ker_orbitToRayChart :
    (Φ.rayDivisorIdeal k hΦ ρ).comap (Φ.affineChartι k ρ.toCone) =
      (ρ.orbitToRayChart k hdim hm hprim).ker := by
  rw [Φ.comap_rayDivisorIdeal_eq_ofIdealTop k hΦ ρ ρ.toCone le_rfl, Ray.orbitToRayChart_def,
    Scheme.Hom.ker_Spec_map, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe,
    ← AlgHom.ker_coe, Ray.ker_orbitCoordinateMap]

/-- The ray orbit as an open subscheme of its reduced ray divisor. -/
def Ray.orbitToComponent :
    Spec (.of (LaurentPolynomial k)) ⟶ (Φ.rayDivisorIdeal k hΦ ρ).subscheme :=
  IsClosedImmersion.lift (Φ.rayDivisorIdeal k hΦ ρ).subschemeι
    (ρ.orbitToRayChart k hdim hm hprim ≫ Φ.affineChartι k ρ.toCone) (by
      rw [ker_subschemeι, Scheme.Hom.ker_comp,
        ← comap_rayBoundaryIdeal_eq_ker_orbitToRayChart k ρ hΦ hdim hm hprim]
      exact le_map_comap _ _)

omit [Nonempty Φ.cones] in
/-- The ray orbit inclusion into the fan scheme factors through the ray divisor. -/
@[reassoc (attr := simp)]
theorem Ray.orbitToComponent_subschemeι :
    ρ.orbitToComponent k hΦ hdim hm hprim ≫ (Φ.rayDivisorIdeal k hΦ ρ).subschemeι =
      ρ.orbitToRayChart k hdim hm hprim ≫ Φ.affineChartι k ρ.toCone :=
  IsClosedImmersion.lift_fac _ _ _

instance Ray.isOpenImmersion_orbitToComponent :
    IsOpenImmersion (ρ.orbitToComponent k hΦ hdim hm hprim) :=
  MorphismProperty.of_isPullback
    (isPullback_of_isClosedImmersion (ρ.orbitToRayChart k hdim hm hprim)
      (Φ.rayDivisorIdeal k hΦ ρ).subschemeι _ (Φ.affineChartι k ρ.toCone)
      (ρ.orbitToComponent_subschemeι k hΦ hdim hm hprim).symm
      (by rw [ker_subschemeι, comap_rayBoundaryIdeal_eq_ker_orbitToRayChart k ρ hΦ hdim hm hprim]))
    (Φ.isOpenImmersion_affineChartι k ρ.toCone)

/-- The ray orbit inclusion into the full boundary factors through the ray divisor. -/
@[reassoc (attr := simp)]
theorem Ray.orbitToComponent_boundaryComponentι :
    ρ.orbitToComponent k hΦ hdim hm hprim ≫ ρ.boundaryComponentι k hΦ =
      ρ.orbitToBoundary k hdim hm hprim := by
  rw [← cancel_mono (D).subschemeι]
  simp

/-- The open ray orbit is a morphism over the coefficient field. -/
instance Ray.isOver_orbitToComponent :
    (ρ.orbitToComponent k hΦ hdim hm hprim).IsOver (Spec (.of k)) where
  comp_over := by
    rw [over_eq_subschemeι_comp, ← Category.assoc, ρ.orbitToComponent_subschemeι k,
      Category.assoc, comp_over, Ray.orbitToRayChart_def]
    exact comp_over (Spec.map (CommRingCat.ofHom
      (ρ.orbitCoordinateMap k hdim hm hprim).toRingHom)) (Spec (.of k))

/-- The binomial center on its own reduced ray divisor. -/
def Ray.binomialCenterOnComponent (c : kˣ) :
    Spec (.of k) ⟶ (Φ.rayDivisorIdeal k hΦ ρ).subscheme :=
  Spec.map (CommRingCat.ofHom (laurentEval ((-1 : kˣ) * c⁻¹)).toRingHom) ≫
    ρ.orbitToComponent k hΦ hdim hm hprim

omit [Nonempty Φ.cones] in
/-- In Laurent coordinates the center is evaluation at the root `-c⁻¹` of the binomial. -/
theorem Ray.binomialCenterOnComponent_eq (c : kˣ) :
    ρ.binomialCenterOnComponent k hΦ hdim hm hprim c =
      Spec.map (CommRingCat.ofHom (laurentEval ((-1 : kˣ) * c⁻¹)).toRingHom) ≫
        ρ.orbitToComponent k hΦ hdim hm hprim :=
  (rfl)

/-- The center on its ray component maps to the binomial center on the full boundary. -/
@[reassoc (attr := simp)]
theorem Ray.binomialCenterOnComponent_boundaryComponentι (c : kˣ) :
    ρ.binomialCenterOnComponent k hΦ hdim hm hprim c ≫ ρ.boundaryComponentι k hΦ =
      ρ.binomialCenterOnBoundary k hdim hm hprim c := by
  rw [Ray.binomialCenterOnComponent_eq, Category.assoc, Ray.orbitToComponent_boundaryComponentι]
  apply (cancel_mono (D).subschemeι).mp
  rw [Category.assoc, Ray.orbitToBoundary_comp_subschemeι,
    Ray.binomialCenterOnBoundary_comp_subschemeι, Ray.binomialCenter_def,
    Ray.orbitToRayChart_def, ← Spec.map_comp_assoc, Ray.binomialCenterEval_def]
  rfl

private theorem boundaryComponentι_binomialCenterOnComponent_apply (c : kˣ) (z : Spec (.of k)) :
    ρ.boundaryComponentι k hΦ (ρ.binomialCenterOnComponent k hΦ hdim hm hprim c z) =
      ρ.binomialCenterOnBoundary k hdim hm hprim c z := by
  rw [← Scheme.Hom.comp_apply, Ray.binomialCenterOnComponent_boundaryComponentι]

private theorem smoothOfRelativeDimension_orbitToComponent :
    SmoothOfRelativeDimension 1
      (ρ.orbitToComponent k hΦ hdim hm hprim ≫
        (Φ.rayDivisorIdeal k hΦ ρ).subschemeι ≫ Φ.finiteFanSchemeToSpec k) := by
  have h : ρ.orbitToComponent k hΦ hdim hm hprim ≫ (Φ.rayDivisorIdeal k hΦ ρ).subschemeι =
      ρ.orbitToBoundary k hdim hm hprim ≫ (D).subschemeι := by
    rw [← ρ.boundaryComponentι_subschemeι k hΦ, Ray.orbitToComponent_boundaryComponentι_assoc]
  simpa only [← Category.assoc, h] using
    ρ.smoothOfRelativeDimension_orbitToBoundary k hdim hm hprim

private theorem isRegularLocalRing_stalk_binomialCenterOnComponent (c : kˣ) :
    IsRegularLocalRing ((Φ.rayDivisorIdeal k hΦ ρ).subscheme.presheaf.stalk
      (ρ.binomialCenterOnComponent k hΦ hdim hm hprim c (IsLocalRing.closedPoint k))) := by
  let j := ρ.orbitToComponent k hΦ hdim hm hprim
  let f := j ≫ (Φ.rayDivisorIdeal k hΦ ρ).subschemeι ≫ Φ.finiteFanSchemeToSpec k
  have : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_orbitToComponent k ρ hΦ hdim
    hm hprim
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion j _).mpr
    (isRegularLocalRing_stalk_of_smooth f _)

private theorem isEffectiveCartier_ker_binomialCenterOnComponent (c : kˣ) :
    (ρ.binomialCenterOnComponent k hΦ hdim hm hprim c).ker.IsEffectiveCartier := by
  let j := ρ.orbitToComponent k hΦ hdim hm hprim
  let U := j.opensRange
  let t := ρ.binomialCenterOnComponent k hΦ hdim hm hprim c
  let f := (Φ.rayDivisorIdeal k hΦ ρ).subschemeι ≫ Φ.finiteFanSchemeToSpec k
  have hf : t ≫ f = 𝟙 _ := by
    simp only [t, f, ← ρ.boundaryComponentι_subschemeι k hΦ, ← Category.assoc,
      Ray.binomialCenterOnComponent_boundaryComponentι,
      Ray.binomialCenterOnBoundary_comp_subschemeι, Ray.binomialCenter_comp_structureMap]
  have : IsClosedImmersion (t ≫ ρ.boundaryComponentι k hΦ) := by
    simp only [t, Ray.binomialCenterOnComponent_boundaryComponentι]
    infer_instance
  have : IsClosedImmersion t := IsClosedImmersion.of_comp_isClosedImmersion t
    (ρ.boundaryComponentι k hΦ)
  have hU : Set.range t ⊆ U := by
    simpa only [t, Ray.binomialCenterOnComponent, U, j, Scheme.Hom.coe_opensRange,
      Scheme.Hom.comp_base, TopCat.coe_comp] using Set.range_comp_subset_range _ _
  let a := IsOpenImmersion.isoOfRangeEq j U.ι U.range_ι.symm
  have ha : a.hom ≫ U.ι = j := IsOpenImmersion.isoOfRangeEq_hom_fac j U.ι U.range_ι.symm
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{u} 1) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).respectsIso
  have : SmoothOfRelativeDimension 1 (U.ι ≫ f) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) a.hom,
      ← Category.assoc, ha]
    exact smoothOfRelativeDimension_orbitToComponent k ρ hΦ hdim hm hprim
  exact Scheme.Hom.isEffectiveCartier_ker_of_comp_eq_id t hf U hU

private theorem binomialCenter_notMem_range_boundaryComponentι {τ : Φ.Ray} (hne : ρ ≠ τ)
    (c : kˣ) :
    ρ.binomialCenterOnBoundary k hdim hm hprim c (IsLocalRing.closedPoint k) ∉
      Set.range (τ.boundaryComponentι k hΦ) := by
  have hle : ¬ τ.toCone ≤ ρ.toCone := by
    intro h
    have heq : τ.toToricRay Φ ρ.toCone h = ρ.toToricRay Φ ρ.toCone le_rfl := by
      apply ToricRay.eq_of_toPointedCone_le (Φ.isToricCone ρ.toCone.property).salient
      simpa only [Ray.toPointedCone_toToricRay] using Subtype.coe_le_coe.mpr h
    exact hne (Subtype.ext (Subtype.ext
      (by simpa only [Ray.toPointedCone_toToricRay] using
        (congrArg ToricRay.toPointedCone heq).symm)))
  let a := Φ.affineChartι k ρ.toCone
  let z : Spec (.of k) := IsLocalRing.closedPoint k
  have hdisj : a ⁻¹ᵁ (Φ.rayDivisorIdeal k hΦ τ).support.compl = ⊤ :=
    (comap_eq_top_iff _ _).mp (Φ.comap_rayDivisorIdeal_eq_top k hΦ τ ρ.toCone hle)
  have hpre (x : affineChart k Φ.lattice ρ.toCone.val) :
      x ∈ a ⁻¹ᵁ (Φ.rayDivisorIdeal k hΦ τ).support.compl := by
    rw [hdisj]
    trivial
  have hpt : ρ.binomialCenter k hdim hm hprim c z ∈
      (Φ.rayDivisorIdeal k hΦ τ).support.compl := by
    rw [Ray.binomialCenter_def, Scheme.Hom.comp_apply]
    exact hpre _
  rintro ⟨q, hq⟩
  have heq := congrArg (fun x ↦ (D).subschemeι x) hq
  simp only [← Scheme.Hom.comp_apply, Ray.boundaryComponentι_subschemeι] at heq
  have hcenter := congrArg (fun g : Spec (.of k) ⟶ (Φ.finiteFanScheme k) ↦ g z)
    (ρ.binomialCenterOnBoundary_comp_subschemeι k hdim hm hprim c)
  rw [Scheme.Hom.comp_apply] at hcenter
  have hqmem : (Φ.rayDivisorIdeal k hΦ τ).subschemeι q ∈
      ((Φ.rayDivisorIdeal k hΦ τ).support : Set (Φ.finiteFanScheme k)) :=
    (Φ.rayDivisorIdeal k hΦ τ).range_subschemeι ▸ Set.mem_range_self q
  exact hpt ((heq.trans hcenter) ▸ hqmem)
variable (c : kˣ) (τ : Φ.Ray)

local notation "center" => Ray.binomialCenterOnBoundary ρ k hdim hm hprim c
local notation "z" => (IsLocalRing.closedPoint k : Spec (CommRingCat.of k))

/-- A binomial center lies on precisely the boundary component of its ray. -/
theorem Ray.binomialCenterOnBoundary_mem_range_boundaryComponentι_iff :
    center z ∈ Set.range (τ.boundaryComponentι k hΦ) ↔ ρ = τ := by
  refine ⟨fun h ↦ of_not_not (fun hn ↦
    binomialCenter_notMem_range_boundaryComponentι k ρ hΦ hdim hm hprim hn c h), ?_⟩
  rintro rfl
  exact ⟨_, boundaryComponentι_binomialCenterOnComponent_apply k ρ hΦ hdim hm hprim c z⟩

/-- In the ambient toric surface a binomial center belongs exactly to its own ray divisor. -/
@[simp]
theorem Ray.binomialCenter_mem_support_rayBoundaryIdeal_iff :
    ρ.binomialCenter k hdim hm hprim c z ∈ (Φ.rayDivisorIdeal k hΦ τ).support ↔ ρ = τ := by
  let q : Spec (.of k) := z
  have h : (D).subschemeι (center q) = ρ.binomialCenter k hdim hm hprim c q :=
    (Scheme.Hom.comp_apply (center) (D).subschemeι q).symm.trans
      (congrArg (fun f : Spec (.of k) ⟶ (Φ.finiteFanScheme k) ↦ f q)
        (ρ.binomialCenterOnBoundary_comp_subschemeι k hdim hm hprim c))
  have hrange : Set.range (τ.boundaryComponentι k hΦ ≫ (D).subschemeι) =
      (D).subschemeι '' Set.range (τ.boundaryComponentι k hΦ) := by
    rw [← Set.range_comp']
    exact congrArg Set.range (funext (Scheme.Hom.comp_apply (τ.boundaryComponentι k hΦ)
      (D).subschemeι))
  rw [← SetLike.mem_coe, ← range_subschemeι, ← τ.boundaryComponentι_subschemeι k hΦ, hrange,
    ← h, (D).subschemeι.isClosedEmbedding.injective.mem_set_image]
  exact ρ.binomialCenterOnBoundary_mem_range_boundaryComponentι_iff k hΦ hdim hm hprim c τ

/-- A binomial point lies on its ray divisor away from the residual toric boundary. -/
theorem Ray.binomialCenter_mem_support_sdiff_colon :
    ρ.binomialCenter k hdim hm hprim c (z : Spec (.of k)) ∈
      ((Φ.rayDivisorIdeal k hΦ ρ).support : Set (Φ.finiteFanScheme k)) \
        ((D).colon (Φ.rayDivisorIdeal k hΦ ρ)).support := by
  let j := Φ.affineChartι k ρ.toCone
  let C := Φ.rayDivisorIdeal k hΦ ρ
  have hDC : D ≤ C := boundaryIdeal_le_rayBoundaryIdeal k ρ hΦ
  have hC := Φ.isEffectiveCartier_rayDivisorIdeal k hΦ ρ
  have hcart : (C.comap j).IsEffectiveCartier := hC.comap j
  have heq : (D).comap j = C.comap j := by
    rw [comap_rayBoundaryIdeal_eq_ker_orbitToRayChart k ρ hΦ hdim hm hprim]
    simpa only [ker_subschemeι] using
      ker_eq_comap_of_isPullback _ (ρ.isPullback_orbitToBoundary k hdim hm hprim) |>.symm
  have hres : ((D).colon C).comap j = ⊤ := by
    rw [comap_colon _ _ hC.locallyPrincipal hDC j hcart, heq, colon_self]
  constructor
  · exact (ρ.binomialCenter_mem_support_rayBoundaryIdeal_iff k hΦ hdim hm hprim c ρ).mpr rfl
  · have hx : ρ.binomialCenter k hdim hm hprim c (z : Spec (.of k)) ∈ Set.range j := by
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
    (center).ker.comap (τ.boundaryComponentι k hΦ) = ⊤ := by
  have hnot :=
    (ρ.binomialCenterOnBoundary_mem_range_boundaryComponentι_iff k hΦ hdim hm hprim c τ).not.mpr hne
  rw [comap_eq_top_iff, ← Opens.coe_eq_univ, Scheme.Hom.coe_preimage, Closeds.coe_compl,
    Scheme.Hom.support_ker, (center).isClosedEmbedding.isClosed_range.closure_eq,
    Set.range_eq_singleton (f := center) (fun q ↦ congrArg center (Subsingleton.elim q z)),
    Set.eq_univ_iff_forall]
  exact fun q hq ↦ hnot ⟨q, hq⟩

/-- The ideal of a binomial center restricts to a Cartier ideal on every reduced ray
component. Away from the ray of the center the restricted ideal is the unit ideal. -/
theorem Ray.isEffectiveCartier_comap_ker_binomialCenterOnBoundary :
    ((center).ker.comap (τ.boundaryComponentι k hΦ)).IsEffectiveCartier := by
  by_cases h : ρ = τ
  · subst τ
    have hcomp := ρ.binomialCenterOnComponent_boundaryComponentι k hΦ hdim hm hprim c
    rw [← hcomp, Scheme.Hom.comap_ker_comp_of_isClosedImmersion]
    exact isEffectiveCartier_ker_binomialCenterOnComponent k ρ hΦ hdim hm hprim c
  · rw [ρ.comap_ker_binomialCenterOnBoundary_eq_top_of_ne k hΦ hdim hm hprim c τ h]
    exact isEffectiveCartier_top _

/-- A point on a reduced ray component above a binomial center has regular local ring. -/
theorem Ray.isRegularLocalRing_stalk_of_boundaryComponentι_eq_binomialCenter
    (q : (Φ.rayDivisorIdeal k hΦ τ).subscheme) (hq : τ.boundaryComponentι k hΦ q = center z) :
    IsRegularLocalRing ((Φ.rayDivisorIdeal k hΦ τ).subscheme.presheaf.stalk q) := by
  have h :=
    (ρ.binomialCenterOnBoundary_mem_range_boundaryComponentι_iff k hΦ hdim hm hprim c τ).mp ⟨q, hq⟩
  subst τ
  let t := ρ.binomialCenterOnComponent k hΦ hdim hm hprim c
  have hEq : q = t z := (ρ.boundaryComponentι k hΦ).isClosedEmbedding.injective
    (hq.trans (boundaryComponentι_binomialCenterOnComponent_apply k ρ hΦ hdim hm hprim c z).symm)
  exact hEq ▸ isRegularLocalRing_stalk_binomialCenterOnComponent k ρ hΦ hdim hm hprim c

end TauCeti.Toric.Fan
