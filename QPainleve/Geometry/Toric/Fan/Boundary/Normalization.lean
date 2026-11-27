/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Isomorphism
public import QPainleve.AlgebraicGeometry.Curves.Node.GenericPoint
public import QPainleve.AlgebraicGeometry.Curves.Node.NormalizationComponent
public import QPainleve.Geometry.Toric.Fan.Boundary.Component
public import QPainleve.Geometry.Toric.Fan.Boundary.Equiv
public import QPainleve.Geometry.Toric.BaseChange.Point
public import TauCeti.AlgebraicGeometry.Cohomology.Genus

import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter
import QPainleve.Geometry.Toric.Fan.Boundary.Node
import QPainleve.Geometry.Toric.Fan.Boundary.ProjectiveLine
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.Basic
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced
import TauCeti.Topology.Sober

/-!
# Normalization components of the reduced toric boundary

The actual blowup of the singular subscheme separates the reduced ray divisors.
Each resulting component projects isomorphically onto its ray divisor. In the
projective-line coordinate induced by a primitive character, the two ends of the
ray component lie above the adjacent torus-fixed points. This identifies the
points on the normalization used to evaluate boundary gluing data.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

universe u

variable (k : Type u) [Field k] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] (hΦ : Φ.IsRegular)

local notation "X" => Φ.finiteFanScheme k
local notation "D" => Φ.toricBoundaryIdeal k inferInstance
local notation "C" => Scheme.IdealSheafData.subscheme D
local notation "I" => Scheme.singularLocus k C
local notation "ν" => Scheme.IdealSheafData.blowupToBase I
local notation "W" => irreducibleComponents (Scheme.IdealSheafData.blowup I)
local notation "base" => Spec (CommRingCat.of k)

include hΦ in
private theorem comp_blowupToBase_mem_singularLocus_of_distinguishedSection
    (hn : AtWorstNodalOfRelativeDimensionOne (C ↘ base))
    (hdim : Module.finrank ℤ N = 2) {σ : Φ.cones} (hc : Nat.card (ToricRay σ.val) = 2) :
    letI := hn.syntomic
    ∀ (l : base ⟶ (I).blowup), l ≫ ν ≫ (D).subschemeι = Φ.distinguishedSection (R := k) σ →
      ∀ x : base, (l ≫ ν) x ∈ ((I).support : Set C) := by
  let := hn.syntomic
  intro l hl x
  have : IsReduced C := hn.isReduced
  obtain ⟨z, hz, hnz⟩ := ((D).isNodeOfReducedBoundary_iff_of_isReduced
    (Φ.finiteFanSchemeToSpec k) _).mp
    (Φ.isNodeOfReducedBoundary_distinguishedSection k hΦ σ hdim hc)
  have hx : (l ≫ ν) x = z := by
    apply (D).subschemeι.isClosedEmbedding.injective
    have he := congrArg (fun f : base ⟶ X ↦ f x)
      ((Category.assoc l ν (D).subschemeι).trans hl)
    rw [Scheme.Hom.comp_apply] at he
    exact he.trans ((congrArg (Φ.distinguishedSection (R := k) σ)
      (Subsingleton.elim x (IsLocalRing.closedPoint k))).trans hz.symm)
  have hnz' : (C ↘ base).IsNodeAt z := hnz
  rw [hx]
  exact ((C).mem_support_singularLocus_iff_notMem_smoothLocus z).mpr
    (((C ↘ base).isNodeAt_iff_notMem_smoothLocus hn z).mp hnz')

include hΦ in
/-- A normalized point projecting to the distinguished point of a two-ray chart lifts
uniquely to the branch scheme. This applies to the projective zero and pole after
transporting them along the component isomorphism and using the ray endpoint formulas. -/
theorem existsUnique_branchScheme_point_of_comp_eq_distinguishedSection
    (hn : AtWorstNodalOfRelativeDimensionOne (C ↘ base))
    (hdim : Module.finrank ℤ N = 2) {σ : Φ.cones} (hc : Nat.card (ToricRay σ.val) = 2) :
    letI := hn.syntomic
    ∀ (l : base ⟶ (I).blowup), l ≫ ν ≫ (D).subschemeι = Φ.distinguishedSection (R := k) σ →
      ∃! q : base ⟶ (C).branchScheme k, q ≫ (C).branchSchemeToBlowup k = l ∧
        q ≫ (C).branchSchemeToSingularLocus k ≫ (I).subschemeι ≫ (C ↘ base) = 𝟙 _ := by
  let := hn.syntomic
  intro l hl
  have : Etale ((I).subschemeι ≫ (C ↘ base)) :=
    (C).etale_singularLocus_subschemeι_comp hn
  have : IsReduced (I).subscheme := ((I).subschemeι ≫ (C ↘ base)).isReduced_of_smooth
  have hred : (I).radical = I := (isReduced_subscheme_iff_radical_eq _).mp inferInstance
  have hker : I ≤ (l ≫ ν).ker := by
    calc
      I = vanishingIdeal (I).support := hred.symm.trans vanishingIdeal_support.symm
      _ ≤ _ := vanishingIdeal_le_ker_of_range_subset _ (by
        rintro _ ⟨x, rfl⟩
        exact comp_blowupToBase_mem_singularLocus_of_distinguishedSection k hΦ
          hn hdim hc l hl x)
  let s := IsClosedImmersion.lift (I).subschemeι (l ≫ ν) (by rwa [ker_subschemeι])
  have hs : s ≫ (I).subschemeι = l ≫ ν := IsClosedImmersion.lift_fac _ _ _
  let sq := (C).isPullback_branchScheme k
  have : IsClosedImmersion ((C).branchSchemeToBlowup k) :=
    MorphismProperty.of_isPullback sq inferInstance
  let q := sq.lift s l hs
  have hq : q ≫ (C).branchSchemeToBlowup k = l := sq.lift_snd _ _ _
  refine ⟨q, ⟨hq, ?_⟩, fun q' hq' ↦ (cancel_mono ((C).branchSchemeToBlowup k)).mp
    (hq'.1.trans hq.symm)⟩
  calc
    _ = l ≫ ν ≫ (C ↘ base) := by
      rw [(C).branchSchemeToSingularLocus_subschemeι_assoc k, ← Category.assoc, hq]
    _ = (l ≫ ν ≫ (D).subschemeι) ≫ (X ↘ base) :=
      (congrArg (fun a ↦ l ≫ ν ≫ a) ((D).over_eq_subschemeι_comp (S := base))).trans (by
        simp only [Category.assoc])
    _ = _ := by
      rw [hl, Φ.finiteFanScheme_over k,
        Φ.distinguishedSection_comp_finiteFanSchemeToSpec (R := k)]

variable [PrestableFamily ((Φ.toricBoundaryIdeal k inferInstance).subscheme ↘ Spec (.of k))]

private theorem range_blowupComponent_subset_ray (v : W) :
    ∃ ρ : Φ.Ray, Set.range (((C).blowupComponent (K := k) v).ι ≫ ν ≫ (D).subschemeι) ⊆
      closure {((Φ.rayBoundaryChartPoint (R := k) hΦ ρ).val)} := by
  have hx : (D).subschemeι (ν (genericPoints.ofComponent v)) ∈ ((D).support : Set X) :=
    (D).range_subschemeι.le (Set.mem_range_self _)
  rw [Φ.support_toricBoundaryIdeal_eq_iUnion_closure k hΦ inferInstance, Set.mem_iUnion] at hx
  obtain ⟨ρ, hρ⟩ := hx
  rw [(C).range_blowupComponent_comp (k := k) _ (D).subschemeι (D).subschemeι.isClosedMap]
  exact ⟨ρ, closure_minimal (Set.singleton_subset_iff.mpr hρ) isClosed_closure⟩

private theorem exists_normalizationComponent (ρ : Φ.Ray) :
    ∃ v : W, Set.range (((C).blowupComponent (K := k) v).ι ≫ ν ≫ (D).subschemeι) =
      closure {((Φ.rayBoundaryChartPoint (R := k) hΦ ρ).val)} := by
  have hx : (Φ.rayBoundaryChartPoint (R := k) hΦ ρ).val ∈ ((D).support : Set X) := by
    rw [Φ.support_toricBoundaryIdeal k]
    exact Φ.rayBoundaryChartPoint_notMem_zeroChart (R := k) hΦ ρ
      (Φ.bot_mem (Nonempty.some (α := Φ.cones) inferInstance).property)
  obtain ⟨x, hx⟩ := (D).range_subschemeι.ge hx
  have : Surjective ν := (C).surjective_blowupToBase_singularLocus
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  obtain ⟨y, hy⟩ := (ν).surjective x
  let v := irreducibleComponentOf y
  have hyv : y ∈ ((C).blowupComponent (K := k) v : Set (I).blowup) := by
    rw [(C).coe_blowupComponent]
    exact mem_irreducibleComponentOf y
  have hr : (Φ.rayBoundaryChartPoint (R := k) hΦ ρ).val ∈
      Set.range (((C).blowupComponent (K := k) v).ι ≫ ν ≫ (D).subschemeι) := by
    let z : ((C).blowupComponent (K := k) v).toScheme := ⟨y, hyv⟩
    refine ⟨z, ?_⟩
    have hz : ((C).blowupComponent v).ι z = y := (rfl)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz, hy, hx]
  obtain ⟨τ, hτ⟩ := range_blowupComponent_subset_ray k hΦ v
  have he : τ = ρ := Φ.rayBoundaryChartPoint_injective (R := k) hΦ
    (CodimensionOnePoint.eq_of_specializes (specializes_iff_mem_closure.mpr (hτ hr)))
  subst τ
  refine ⟨v, hτ.antisymm ?_⟩
  rw [(C).range_blowupComponent_comp (k := k) _ (D).subschemeι (D).subschemeι.isClosedMap] at hr ⊢
  exact closure_minimal (Set.singleton_subset_iff.mpr hr) isClosed_closure

private theorem normalizationComponent_bijective :
    Function.Bijective (fun ρ : Φ.Ray ↦ (exists_normalizationComponent k hΦ ρ).choose) := by
  have hr (ρ : Φ.Ray) := (exists_normalizationComponent k hΦ ρ).choose_spec
  constructor
  · intro ρ τ he
    dsimp only at he
    have h := (hr ρ).symm.trans (he ▸ hr τ)
    apply Φ.rayBoundaryChartPoint_injective (R := k) hΦ
    apply CodimensionOnePoint.eq_of_specializes
    exact specializes_iff_mem_closure.mpr (h ▸ subset_closure (Set.mem_singleton _))
  · intro v
    obtain ⟨ρ, hρ⟩ := range_blowupComponent_subset_ray k hΦ v
    refine ⟨ρ, ((C).eq_of_range_blowupComponent_subset (k := k) ?_).symm⟩
    rw [← Set.image_subset_image_iff (D).subschemeι.isClosedEmbedding.injective,
      ← Set.range_comp, ← Set.range_comp]
    exact hρ.trans (hr ρ).ge

variable (Φ) in
/-- The rays index the irreducible components of the normalization of the reduced
toric boundary. -/
def boundaryNormalizationComponentEquiv : Φ.Ray ≃ W :=
  Equiv.ofBijective _ (normalizationComponent_bijective k hΦ)

variable (Φ) in
/-- The component indexed by a ray maps onto the corresponding reduced ray divisor. -/
theorem range_boundaryNormalizationComponentEquiv (ρ : Φ.Ray) :
    Set.range (((C).blowupComponent (K := k)
      (Φ.boundaryNormalizationComponentEquiv k hΦ ρ)).ι ≫ ν) =
      Set.range (ρ.boundaryComponentι k hΦ) := by
  apply (D).subschemeι.isClosedEmbedding.injective.image_injective
  rw [← Set.range_comp, ← Set.range_comp]
  have hrange := (exists_normalizationComponent k hΦ ρ).choose_spec
  have hR : Set.range ((Φ.rayDivisorIdeal k hΦ ρ).subschemeι) =
      closure {((Φ.rayBoundaryChartPoint (R := k) hΦ ρ).val)} := by
    rw [range_subschemeι, Φ.coe_support_rayDivisorIdeal k]
  refine hrange.trans (hR.symm.trans ?_)
  exact congrArg (fun f : _ ⟶ X ↦ Set.range f) (ρ.boundaryComponentι_subschemeι k hΦ).symm

private theorem range_normalizationComponent_to_toric (ρ : Φ.Ray) :
    Set.range (((C).blowupComponent (K := k) (Φ.boundaryNormalizationComponentEquiv k hΦ ρ)).ι ≫
      ν ≫ (D).subschemeι) = closure {(Φ.rayBoundaryChartPoint (R := k) hΦ ρ).val} := by
  rw [← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Φ.range_boundaryNormalizationComponentEquiv k hΦ ρ, ← Set.range_comp, ← TopCat.coe_comp,
    ← Scheme.Hom.comp_base, ρ.boundaryComponentι_subschemeι k hΦ,
    Scheme.IdealSheafData.range_subschemeι,
    Φ.coe_support_rayDivisorIdeal k]

variable [IsSepClosed k] in
/-- The generic point of a numbered toric boundary component is the prime of
the corresponding ray, viewed in the ambient surface. -/
theorem subschemeι_componentGenericPoint_eq_rayBoundaryPoint
    {γ : Type*} {p : γ → (C ↘ base).smoothLocus} {n : ℕ} [NeZero n]
    (A : Scheme.NodalCycleNumbering p n) (hΦ : Φ.IsRegular) (j : ZMod n) (ρ : Φ.Ray)
    (hρ : A.component j = Φ.boundaryNormalizationComponentEquiv k hΦ ρ) :
    (D).subschemeι (A.componentGenericPoint j) = (Φ.rayBoundaryChartPoint (R := k) hΦ ρ).val := by
  have h := (C).range_blowupComponent_comp (k := k) (A.component j) (D).subschemeι
    (D).subschemeι.isClosedMap
  rw [← A.componentGenericPoint_def, hρ, range_normalizationComponent_to_toric k hΦ ρ] at h
  exact isGenericPoint_closure.eq (h.symm ▸ isGenericPoint_closure)

variable (ρ : Φ.Ray)

local notation "R" => Scheme.IdealSheafData.subscheme (Φ.rayDivisorIdeal k hΦ ρ)
local notation "U" =>
  Scheme.blowupComponent (K := k) C (Φ.boundaryNormalizationComponentEquiv k hΦ ρ)

private theorem exists_boundaryNormalizationComponentIso :
    ∃ e : (U).toScheme ≅ R, e.hom ≫ ρ.boundaryComponentι k hΦ = (U).ι ≫ ν := by
  have : TauCeti.AlgebraicGeometry.IsRegular R := Φ.isRegular_rayBoundary k hΦ ρ
  exact ((C).existsUnique_blowupComponentIso_of_range_eq (k := k) (ρ.boundaryComponentι k hΦ) _
    (Φ.range_boundaryNormalizationComponentEquiv k hΦ ρ)).exists

/-- The normalized component indexed by a ray is isomorphic to the reduced ray
divisor, with its projection given by the closed immersion into the boundary. -/
def Ray.boundaryNormalizationComponentIso : (U).toScheme ≅ R :=
  (exists_boundaryNormalizationComponentIso k hΦ ρ).choose

@[reassoc (attr := simp)]
theorem Ray.boundaryNormalizationComponentIso_hom_boundaryComponentι :
    (ρ.boundaryNormalizationComponentIso k hΦ).hom ≫ ρ.boundaryComponentι k hΦ = (U).ι ≫ ν :=
  (exists_boundaryNormalizationComponentIso k hΦ ρ).choose_spec

@[reassoc (attr := simp)]
theorem Ray.boundaryNormalizationComponentIso_inv_ι_blowupToBase :
    (ρ.boundaryNormalizationComponentIso k hΦ).inv ≫ (U).ι ≫ ν = ρ.boundaryComponentι k hΦ := by
  rw [← Ray.boundaryNormalizationComponentIso_hom_boundaryComponentι, Iso.inv_hom_id_assoc]

/-- A point on the normalized ray component is determined by its image in the boundary. -/
theorem Ray.injOn_blowupToBase_boundaryNormalizationComponent :
    Set.InjOn ν (Φ.boundaryNormalizationComponentEquiv k hΦ ρ : Set (I).blowup) := by
  intro x hx y hy hxy
  have hx' : x ∈ Set.range (U).ι := by
    rwa [Scheme.Opens.range_ι, Scheme.coe_blowupComponent]
  have hy' : y ∈ Set.range (U).ι := by
    rwa [Scheme.Opens.range_ι, Scheme.coe_blowupComponent]
  obtain ⟨p, rfl⟩ := hx'
  obtain ⟨q, rfl⟩ := hy'
  let e := ρ.boundaryNormalizationComponentIso k hΦ
  have he : (e.hom ≫ ρ.boundaryComponentι k hΦ) p = (e.hom ≫ ρ.boundaryComponentι k hΦ) q := by
    simpa only [e, Ray.boundaryNormalizationComponentIso_hom_boundaryComponentι,
      Scheme.Hom.comp_apply] using hxy
  exact congrArg (U).ι ((e.hom ≫ ρ.boundaryComponentι k hΦ).injective he)

instance Ray.isOver_boundaryNormalizationComponentIso_hom :
    (ρ.boundaryNormalizationComponentIso k hΦ).hom.IsOver base := ⟨by
  have hbase : ρ.boundaryComponentι k hΦ ≫ (C ↘ base) = (R ↘ base) := by
    calc
      _ = (ρ.boundaryComponentι k hΦ ≫ (D).subschemeι) ≫ (X ↘ base) :=
        (congrArg (ρ.boundaryComponentι k hΦ ≫ ·) ((D).over_eq_subschemeι_comp (S := base))).trans
          (Category.assoc _ _ _).symm
      _ = _ := congrArg (· ≫ (X ↘ base)) (ρ.boundaryComponentι_subschemeι k hΦ)
  calc
    _ = (ρ.boundaryNormalizationComponentIso k hΦ).hom ≫ ρ.boundaryComponentι k hΦ ≫ (C ↘ base) :=
      congrArg ((ρ.boundaryNormalizationComponentIso k hΦ).hom ≫ ·) hbase.symm
    _ = _ := Ray.boundaryNormalizationComponentIso_hom_boundaryComponentι_assoc k hΦ ρ _⟩

/-- A ray divisor of a prestable toric boundary is proper because it is isomorphic to
a component of the normalization. -/
theorem Ray.isProper_boundaryComponent_of_prestableFamily : IsProper (R ↘ base) := by
  let e := ρ.boundaryNormalizationComponentIso k hΦ
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsProper e.hom, comp_over e.hom base]
  infer_instance

variable (b : Module.Basis (Fin 2) ℤ N) in
include hΦ b in
/-- Every component of the normalization of a prestable rank-two toric boundary
has genus zero. -/
theorem boundaryNormalizationComponent_genus_eq_zero (v : W) :
    ((C).blowupComponent v).toScheme.genus k = 0 := by
  obtain ⟨ρ, rfl⟩ := (Φ.boundaryNormalizationComponentEquiv k hΦ).surjective v
  let e := ρ.boundaryNormalizationComponentIso k hΦ
  let : IsProper ((Φ.rayDivisorIdeal k hΦ ρ).subscheme ↘ base) :=
    ρ.isProper_boundaryComponent_of_prestableFamily k hΦ
  have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  let p := ρ.boundaryIsoProjectiveLine k hΦ hdim (b.detDualEquiv_self _)
    (ρ.surjective_detCharacter b)
  let : e.hom.IsOver base := ρ.isOver_boundaryNormalizationComponentIso_hom k hΦ
  let : p.hom.IsOver base := ρ.isOver_boundaryIsoProjectiveLine_hom k hΦ hdim
    (b.detDualEquiv_self _) (ρ.surjective_detCharacter b)
  have h := (e.hom ≫ p.hom).finrank_cohomology_trivial_of_isIso k 1
  have hp := projectiveLine.genus_eq_zero k
  rw [Scheme.genus_def] at hp ⊢
  exact h.trans hp

end TauCeti.Toric.Fan

namespace TauCeti.Toric.FanEquiv

universe u

variable (k : Type u) [Field k] {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'} (e : FanEquiv Φ Ψ)

variable [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]
  (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)

local notation "base" => Spec (CommRingCat.of k)
local notation "D₁" => Fan.toricBoundaryIdeal k Φ hΦ₀
local notation "D₂" => Fan.toricBoundaryIdeal k Ψ hΨ₀
local notation "C₁" => Scheme.IdealSheafData.subscheme D₁
local notation "C₂" => Scheme.IdealSheafData.subscheme D₂
local notation "I₁" => Scheme.singularLocus k C₁
local notation "I₂" => Scheme.singularLocus k C₂
local notation "g" => e.boundaryIso k hΦ₀ hΨ₀
local notation "gν" => Iso.hom (Iso.singularLocusBlowupIso (R := k) g)

/-- The isomorphism of normalizations carries the component indexed by a ray
onto the component indexed by its image ray. -/
theorem image_singularLocusBlowupIso_boundaryNormalizationComponent
    [PrestableFamily (C₁ ↘ base)] [PrestableFamily (C₂ ↘ base)] (ρ : Φ.Ray) :
    (gν) '' ((Φ.boundaryNormalizationComponentEquiv k hΦ ρ) : Set (I₁).blowup) =
      ((Ψ.boundaryNormalizationComponentEquiv k hΨ (e.rayEquiv ρ)) : Set (I₂).blowup) := by
  let w := (Φ.boundaryNormalizationComponentEquiv k hΦ ρ)
  let F := (I₂).blowupToBase ≫ (D₂).subschemeι
  let G := (I₁).blowupToBase ≫ (D₁).subschemeι
  let I := gν
  have hI : I ≫ F = G ≫ e.toFanHom.finiteFanSchemeHom k := by
    simp only [I, F, G, Category.assoc, Iso.singularLocusBlowupIso_hom_blowupToBase_assoc,
      boundaryIso_hom_subschemeι k e]
  have him : I '' (w : Set _) ∈ irreducibleComponents (I₂).blowup := by
    apply image_mem_irreducibleComponents_of_isPreirreducible_fiber I I.continuous
      I.homeomorph.isOpenMap (fun _ ↦ (Set.subsingleton_singleton.preimage
        I.homeomorph.injective).isPreirreducible) I.homeomorph.surjective w.property
  let w' : irreducibleComponents (I₂).blowup := ⟨I '' w.val, him⟩
  have hG : G '' (w : Set _) = closure {(Φ.rayBoundaryChartPoint (R := k) hΦ ρ).val} := by
    rw [← Scheme.coe_blowupComponent (K := k) (C₁) w,
      ← Scheme.Opens.range_ι, ← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base]
    exact Fan.range_normalizationComponent_to_toric k hΦ ρ
  have hr :
      F '' (w' : Set _) = closure {(Ψ.rayBoundaryChartPoint (R := k) hΨ (e.rayEquiv ρ)).val} := by
    have hpoint (x : (I₁).blowup) :
        F (I x) = e.toFanHom.finiteFanSchemeHom k (G x) := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun f : _ ⟶ Ψ.finiteFanScheme k ↦ f x) hI
    rw [Subtype.coe_mk, Set.image_image, Set.image_congr (fun x _ ↦ hpoint x),
      ← Set.image_image, hG]
    rw [← (e.toFanHom.finiteFanSchemeHom k).isClosedMap.closure_image_eq_of_continuous
      (e.toFanHom.finiteFanSchemeHom k).continuous, Set.image_singleton,
      e.finiteFanSchemeHom_rayBoundaryChartPoint k]
  have hw' : w' = (Ψ.boundaryNormalizationComponentEquiv k hΨ (e.rayEquiv ρ)) := by
    apply (C₂).eq_of_range_blowupComponent_subset (k := k)
    rw [← Set.image_subset_image_iff (D₂).subschemeι.isClosedEmbedding.injective,
      ← Set.range_comp, ← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      ← TopCat.coe_comp, ← Scheme.Hom.comp_base, Category.assoc, Category.assoc,
      Fan.range_normalizationComponent_to_toric k, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, Scheme.Opens.range_ι, Scheme.coe_blowupComponent]
    exact hr.le
  exact congrArg Subtype.val hw'

end TauCeti.Toric.FanEquiv
