/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Isomorphism
public import QPainleve.AlgebraicGeometry.Curves.Node.NormalizationComponent
public import QPainleve.Geometry.Toric.Fan.Boundary.Component
public import QPainleve.Geometry.Toric.Fan.Boundary.Equiv
public import QPainleve.Geometry.Toric.Fan.Point
public import TauCeti.AlgebraicGeometry.Cohomology.Genus

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

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] (hΦ : Φ.IsRegular)

local notation "X" => Φ.algebraicRealization
local notation "D" => Φ.boundaryIdeal inferInstance
local notation "C" => Scheme.IdealSheafData.subscheme D
local notation "I" => Scheme.singularLocus ℂ C
local notation "ν" => Scheme.IdealSheafData.blowupToBase I
local notation "W" => irreducibleComponents (Scheme.IdealSheafData.blowup I)
local notation "base" => Spec (CommRingCat.of ℂ)

include hΦ in
private theorem comp_blowupToBase_mem_singularLocus_of_distinguishedPointHom
    (hn : AtWorstNodalOfRelativeDimensionOne (C ↘ base))
    (hdim : Module.finrank ℤ N = 2) {σ : Φ.cones} (hc : Nat.card (ToricRay σ.val) = 2) :
    letI := hn.syntomic
    ∀ (l : base ⟶ (I).blowup), l ≫ ν ≫ (D).subschemeι = Φ.distinguishedPointHom σ →
      ∀ x : base, (l ≫ ν) x ∈ ((I).support : Set C) := by
  let := hn.syntomic
  intro l hl x
  have : IsReduced C := hn.isReduced
  obtain ⟨z, hz, hnz⟩ := ((D).isNodeOfReducedBoundary_iff_of_isReduced
    Φ.algebraicRealizationStructureMap _).mp
    (Φ.isNodeOfReducedBoundary_distinguishedPointHom hΦ σ hdim hc)
  have hx : (l ≫ ν) x = z := by
    apply (D).subschemeι.isClosedEmbedding.injective
    have he := congrArg (fun f : base ⟶ X ↦ f x)
      ((Category.assoc l ν (D).subschemeι).trans hl)
    rw [Scheme.Hom.comp_apply] at he
    exact he.trans ((congrArg (Φ.distinguishedPointHom σ)
      (Subsingleton.elim x (IsLocalRing.closedPoint ℂ))).trans hz.symm)
  have hnz' : (C ↘ base).IsNodeAt z := hnz
  rw [hx]
  exact ((C).mem_support_singularLocus_iff_notMem_smoothLocus z).mpr
    (((C ↘ base).isNodeAt_iff_notMem_smoothLocus hn z).mp hnz')

include hΦ in
/-- A normalized point projecting to the distinguished point of a two-ray chart lifts
uniquely to the branch scheme. This applies to the projective zero and pole after
transporting them along the component isomorphism and using the ray endpoint formulas. -/
theorem existsUnique_branchScheme_point_of_comp_eq_distinguishedPointHom
    (hn : AtWorstNodalOfRelativeDimensionOne (C ↘ base))
    (hdim : Module.finrank ℤ N = 2) {σ : Φ.cones} (hc : Nat.card (ToricRay σ.val) = 2) :
    letI := hn.syntomic
    ∀ (l : base ⟶ (I).blowup), l ≫ ν ≫ (D).subschemeι = Φ.distinguishedPointHom σ →
      ∃! q : base ⟶ (C).branchScheme ℂ, q ≫ (C).branchSchemeToBlowup ℂ = l ∧
        q ≫ (C).branchSchemeToSingularLocus ℂ ≫ (I).subschemeι ≫ (C ↘ base) = 𝟙 _ := by
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
        exact comp_blowupToBase_mem_singularLocus_of_distinguishedPointHom hΦ hn hdim hc l hl x)
  let s := IsClosedImmersion.lift (I).subschemeι (l ≫ ν) (by rwa [ker_subschemeι])
  have hs : s ≫ (I).subschemeι = l ≫ ν := IsClosedImmersion.lift_fac _ _ _
  let sq := (C).isPullback_branchScheme ℂ
  have : IsClosedImmersion ((C).branchSchemeToBlowup ℂ) :=
    MorphismProperty.of_isPullback sq inferInstance
  let q := sq.lift s l hs
  have hq : q ≫ (C).branchSchemeToBlowup ℂ = l := sq.lift_snd _ _ _
  refine ⟨q, ⟨hq, ?_⟩, fun q' hq' ↦ (cancel_mono ((C).branchSchemeToBlowup ℂ)).mp
    (hq'.1.trans hq.symm)⟩
  calc
    _ = l ≫ ν ≫ (C ↘ base) := by
      rw [(C).branchSchemeToSingularLocus_subschemeι_assoc ℂ, ← Category.assoc, hq]
    _ = (l ≫ ν ≫ (D).subschemeι) ≫ (X ↘ base) :=
      (congrArg (fun a ↦ l ≫ ν ≫ a) ((D).over_eq_subschemeι_comp (S := base))).trans (by
        simp only [Category.assoc])
    _ = _ := by
      rw [hl, Φ.algebraicRealization_over,
        Φ.distinguishedPointHom_comp_algebraicRealizationStructureMap]

variable [PrestableFamily ((Φ.boundaryIdeal inferInstance).subscheme ↘ Spec (.of ℂ))]

private theorem range_blowupComponent_subset_ray (v : W) :
    ∃ ρ : Φ.Ray, Set.range (((C).blowupComponent (K := ℂ) v).ι ≫ ν ≫ (D).subschemeι) ⊆
      closure {((Φ.rayBoundaryPoint hΦ ρ).val)} := by
  have hx : (D).subschemeι (ν (genericPoints.ofComponent v)) ∈ ((D).support : Set X) :=
    (D).range_subschemeι.le (Set.mem_range_self _)
  rw [Φ.support_boundaryIdeal_eq_iUnion_closure hΦ, Set.mem_iUnion] at hx
  obtain ⟨ρ, hρ⟩ := hx
  rw [(C).range_blowupComponent_comp (k := ℂ) _ (D).subschemeι (D).subschemeι.isClosedMap]
  exact ⟨ρ, closure_minimal (Set.singleton_subset_iff.mpr hρ) isClosed_closure⟩

private theorem exists_normalizationComponent (ρ : Φ.Ray) :
    ∃ v : W, Set.range (((C).blowupComponent (K := ℂ) v).ι ≫ ν ≫ (D).subschemeι) =
      closure {((Φ.rayBoundaryPoint hΦ ρ).val)} := by
  have hx : (Φ.rayBoundaryPoint hΦ ρ).val ∈ ((D).support : Set X) := by
    rw [Φ.support_boundaryIdeal]
    exact Φ.rayBoundaryPoint_notMem_range_denseTorusι hΦ ρ
  obtain ⟨x, hx⟩ := (D).range_subschemeι.ge hx
  have : Surjective ν := (C).surjective_blowupToBase_singularLocus
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  obtain ⟨y, hy⟩ := (ν).surjective x
  let v := irreducibleComponentOf y
  have hyv : y ∈ ((C).blowupComponent (K := ℂ) v : Set (I).blowup) := by
    rw [(C).coe_blowupComponent]
    exact mem_irreducibleComponentOf y
  have hr : (Φ.rayBoundaryPoint hΦ ρ).val ∈
      Set.range (((C).blowupComponent (K := ℂ) v).ι ≫ ν ≫ (D).subschemeι) := by
    let z : ((C).blowupComponent (K := ℂ) v).toScheme := ⟨y, hyv⟩
    refine ⟨z, ?_⟩
    have hz : ((C).blowupComponent v).ι z = y := (rfl)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz, hy, hx]
  obtain ⟨τ, hτ⟩ := range_blowupComponent_subset_ray hΦ v
  have he : τ = ρ := Φ.rayBoundaryPoint_injective hΦ
    (CodimensionOnePoint.eq_of_specializes (specializes_iff_mem_closure.mpr (hτ hr)))
  subst τ
  refine ⟨v, hτ.antisymm ?_⟩
  rw [(C).range_blowupComponent_comp (k := ℂ) _ (D).subschemeι (D).subschemeι.isClosedMap] at hr ⊢
  exact closure_minimal (Set.singleton_subset_iff.mpr hr) isClosed_closure

private theorem normalizationComponent_bijective :
    Function.Bijective (fun ρ : Φ.Ray ↦ (exists_normalizationComponent hΦ ρ).choose) := by
  have hr (ρ : Φ.Ray) := (exists_normalizationComponent hΦ ρ).choose_spec
  constructor
  · intro ρ τ he
    dsimp only at he
    have h := (hr ρ).symm.trans (he ▸ hr τ)
    apply Φ.rayBoundaryPoint_injective hΦ
    apply CodimensionOnePoint.eq_of_specializes
    exact specializes_iff_mem_closure.mpr (h ▸ subset_closure (Set.mem_singleton _))
  · intro v
    obtain ⟨ρ, hρ⟩ := range_blowupComponent_subset_ray hΦ v
    refine ⟨ρ, ((C).eq_of_range_blowupComponent_subset (k := ℂ) ?_).symm⟩
    rw [← Set.image_subset_image_iff (D).subschemeι.isClosedEmbedding.injective,
      ← Set.range_comp, ← Set.range_comp]
    exact hρ.trans (hr ρ).ge

variable (Φ) in
/-- The rays index the irreducible components of the normalization of the reduced
toric boundary. -/
def boundaryNormalizationComponentEquiv : Φ.Ray ≃ W :=
  Equiv.ofBijective _ (normalizationComponent_bijective hΦ)

variable (Φ) in
/-- The component indexed by a ray maps onto the corresponding reduced ray divisor. -/
theorem range_boundaryNormalizationComponentEquiv (ρ : Φ.Ray) :
    Set.range (((C).blowupComponent (K := ℂ) (Φ.boundaryNormalizationComponentEquiv hΦ ρ)).ι ≫ ν) =
      Set.range (ρ.boundaryComponentι hΦ) := by
  apply (D).subschemeι.isClosedEmbedding.injective.image_injective
  rw [← Set.range_comp, ← Set.range_comp]
  have hrange := (exists_normalizationComponent hΦ ρ).choose_spec
  have hR : Set.range ((Φ.rayBoundaryIdeal hΦ ρ).subschemeι) =
      closure {((Φ.rayBoundaryPoint hΦ ρ).val)} := by
    rw [range_subschemeι, Φ.coe_support_rayBoundaryIdeal]
  refine hrange.trans (hR.symm.trans ?_)
  exact congrArg (fun f : _ ⟶ X ↦ Set.range f) (ρ.boundaryComponentι_subschemeι hΦ).symm

variable (ρ : Φ.Ray)

local notation "R" => Scheme.IdealSheafData.subscheme (Φ.rayBoundaryIdeal hΦ ρ)
local notation "U" => Scheme.blowupComponent (K := ℂ) C (Φ.boundaryNormalizationComponentEquiv hΦ ρ)

private theorem exists_boundaryNormalizationComponentIso :
    ∃ e : (U).toScheme ≅ R, e.hom ≫ ρ.boundaryComponentι hΦ = (U).ι ≫ ν := by
  have : TauCeti.AlgebraicGeometry.IsRegular R := Φ.isRegular_rayBoundary hΦ ρ
  exact ((C).existsUnique_blowupComponentIso_of_range_eq (k := ℂ) (ρ.boundaryComponentι hΦ) _
    (Φ.range_boundaryNormalizationComponentEquiv hΦ ρ)).exists

/-- The normalized component indexed by a ray is isomorphic to the reduced ray
divisor, with its projection given by the closed immersion into the boundary. -/
def Ray.boundaryNormalizationComponentIso : (U).toScheme ≅ R :=
  (exists_boundaryNormalizationComponentIso hΦ ρ).choose

@[reassoc (attr := simp)]
theorem Ray.boundaryNormalizationComponentIso_hom_boundaryComponentι :
    (ρ.boundaryNormalizationComponentIso hΦ).hom ≫ ρ.boundaryComponentι hΦ = (U).ι ≫ ν :=
  (exists_boundaryNormalizationComponentIso hΦ ρ).choose_spec

@[reassoc (attr := simp)]
theorem Ray.boundaryNormalizationComponentIso_inv_ι_blowupToBase :
    (ρ.boundaryNormalizationComponentIso hΦ).inv ≫ (U).ι ≫ ν = ρ.boundaryComponentι hΦ := by
  rw [← Ray.boundaryNormalizationComponentIso_hom_boundaryComponentι, Iso.inv_hom_id_assoc]

/-- A point on the normalized ray component is determined by its image in the boundary. -/
theorem Ray.injOn_blowupToBase_boundaryNormalizationComponent :
    Set.InjOn ν (Φ.boundaryNormalizationComponentEquiv hΦ ρ : Set (I).blowup) := by
  intro x hx y hy hxy
  have hx' : x ∈ Set.range (U).ι := by
    rwa [Scheme.Opens.range_ι, Scheme.coe_blowupComponent]
  have hy' : y ∈ Set.range (U).ι := by
    rwa [Scheme.Opens.range_ι, Scheme.coe_blowupComponent]
  obtain ⟨p, rfl⟩ := hx'
  obtain ⟨q, rfl⟩ := hy'
  let e := ρ.boundaryNormalizationComponentIso hΦ
  have he : (e.hom ≫ ρ.boundaryComponentι hΦ) p = (e.hom ≫ ρ.boundaryComponentι hΦ) q := by
    simpa only [e, Ray.boundaryNormalizationComponentIso_hom_boundaryComponentι,
      Scheme.Hom.comp_apply] using hxy
  exact congrArg (U).ι ((e.hom ≫ ρ.boundaryComponentι hΦ).injective he)

instance Ray.isOver_boundaryNormalizationComponentIso_hom :
    (ρ.boundaryNormalizationComponentIso hΦ).hom.IsOver base := ⟨by
  have hbase : ρ.boundaryComponentι hΦ ≫ (C ↘ base) = (R ↘ base) := by
    calc
      _ = (ρ.boundaryComponentι hΦ ≫ (D).subschemeι) ≫ (X ↘ base) :=
        (congrArg (ρ.boundaryComponentι hΦ ≫ ·) ((D).over_eq_subschemeι_comp (S := base))).trans
          (Category.assoc _ _ _).symm
      _ = _ := congrArg (· ≫ (X ↘ base)) (ρ.boundaryComponentι_subschemeι hΦ)
  calc
    _ = (ρ.boundaryNormalizationComponentIso hΦ).hom ≫ ρ.boundaryComponentι hΦ ≫ (C ↘ base) :=
      congrArg ((ρ.boundaryNormalizationComponentIso hΦ).hom ≫ ·) hbase.symm
    _ = _ := Ray.boundaryNormalizationComponentIso_hom_boundaryComponentι_assoc hΦ ρ _⟩

/-- A ray divisor of a prestable toric boundary is proper because it is isomorphic to
a component of the normalization. -/
theorem Ray.isProper_boundaryComponent_of_prestableFamily : IsProper (R ↘ base) := by
  let e := ρ.boundaryNormalizationComponentIso hΦ
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsProper e.hom, comp_over e.hom base]
  infer_instance

variable (b : Module.Basis (Fin 2) ℤ N) in
include hΦ b in
/-- Every component of the normalization of a prestable rank-two toric boundary
has genus zero. -/
theorem boundaryNormalizationComponent_genus_eq_zero (v : W) :
    ((C).blowupComponent v).toScheme.genus ℂ = 0 := by
  obtain ⟨ρ, rfl⟩ := (Φ.boundaryNormalizationComponentEquiv hΦ).surjective v
  let e := ρ.boundaryNormalizationComponentIso hΦ
  let : IsProper ((Φ.rayBoundaryIdeal hΦ ρ).subscheme ↘ base) :=
    ρ.isProper_boundaryComponent_of_prestableFamily hΦ
  have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  let p := ρ.boundaryIsoProjectiveLine hΦ hdim (b.detDualEquiv_self _)
    (ρ.surjective_detCharacter b)
  let : e.hom.IsOver base := ρ.isOver_boundaryNormalizationComponentIso_hom hΦ
  let : p.hom.IsOver base := ρ.isOver_boundaryIsoProjectiveLine_hom hΦ hdim
    (b.detDualEquiv_self _) (ρ.surjective_detCharacter b)
  have h := (e.hom ≫ p.hom).finrank_cohomology_trivial_of_isIso ℂ 1
  have hp := projectiveLine.genus_eq_zero ℂ
  rw [Scheme.genus_def] at hp ⊢
  exact h.trans hp

end TauCeti.Toric.Fan

namespace TauCeti.Toric.FanEquiv

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'} (e : FanEquiv Φ Ψ)

variable [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]
  (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)

local notation "base" => Spec (CommRingCat.of ℂ)
local notation "D[" Φ "]" => Fan.boundaryIdeal Φ inferInstance
local notation "C[" Φ "]" => Scheme.IdealSheafData.subscheme (D[Φ])
local notation "ν[" Φ "]" => Scheme.IdealSheafData.blowupToBase (Scheme.singularLocus ℂ (C[Φ]))
local notation "g" => e.boundaryIso hΦ₀ hΨ₀
local notation "gν" => Iso.hom (Iso.singularLocusBlowupIso (R := ℂ) g)

variable [PrestableFamily (C[Φ] ↘ base)] [PrestableFamily (C[Ψ] ↘ base)]

local notation "U[" Φ "," h "," ρ "]" =>
  Fan.boundaryNormalizationComponentEquiv Φ h ρ

private theorem range_normalizationComponent_to_toric
    {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
    {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
    [PrestableFamily (C[Φ] ↘ base)] (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    Set.range (((C[Φ]).blowupComponent (K := ℂ) (U[Φ,hΦ,ρ])).ι ≫
      ν[Φ] ≫ (D[Φ]).subschemeι) = closure {(Φ.rayBoundaryPoint hΦ ρ).val} := by
  rw [← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Φ.range_boundaryNormalizationComponentEquiv hΦ ρ, ← Set.range_comp, ← TopCat.coe_comp,
    ← Scheme.Hom.comp_base, ρ.boundaryComponentι_subschemeι hΦ,
    Scheme.IdealSheafData.range_subschemeι,
    Φ.coe_support_rayBoundaryIdeal]

/-- The isomorphism of normalizations carries the component indexed by a ray
onto the component indexed by its image ray. -/
theorem image_singularLocusBlowupIso_boundaryNormalizationComponent (ρ : Φ.Ray) :
    (gν) '' (U[Φ,hΦ,ρ] : Set (Scheme.singularLocus ℂ (C[Φ])).blowup) =
      (U[Ψ,hΨ,e.rayEquiv ρ] : Set (Scheme.singularLocus ℂ (C[Ψ])).blowup) := by
  let w := U[Φ,hΦ,ρ]
  let F := ν[Ψ] ≫ (D[Ψ]).subschemeι
  let G := ν[Φ] ≫ (D[Φ]).subschemeι
  let I := gν
  have hI : I ≫ F = G ≫ e.toFanHom.algebraicMap := by
    simp only [I, F, G, Category.assoc, Iso.singularLocusBlowupIso_hom_blowupToBase_assoc,
      boundaryIso_hom_subschemeι]
  have him : I '' (w : Set _) ∈ irreducibleComponents (Scheme.singularLocus ℂ (C[Ψ])).blowup := by
    apply image_mem_irreducibleComponents_of_isPreirreducible_fiber I I.continuous
      I.homeomorph.isOpenMap (fun _ ↦ (Set.subsingleton_singleton.preimage
        I.homeomorph.injective).isPreirreducible) I.homeomorph.surjective w.property
  let w' : irreducibleComponents (Scheme.singularLocus ℂ (C[Ψ])).blowup := ⟨I '' w.val, him⟩
  have hG : G '' (w : Set _) = closure {(Φ.rayBoundaryPoint hΦ ρ).val} := by
    rw [← Scheme.coe_blowupComponent (K := ℂ) (C[Φ]) w,
      ← Scheme.Opens.range_ι, ← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base]
    exact range_normalizationComponent_to_toric hΦ ρ
  have hr :
      F '' (w' : Set _) = closure {(Ψ.rayBoundaryPoint hΨ (e.rayEquiv ρ)).val} := by
    have hpoint (x : (Scheme.singularLocus ℂ (C[Φ])).blowup) :
        F (I x) = e.toFanHom.algebraicMap (G x) := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun f : _ ⟶ Ψ.algebraicRealization ↦ f x) hI
    rw [Subtype.coe_mk, Set.image_image, Set.image_congr (fun x _ ↦ hpoint x),
      ← Set.image_image, hG]
    rw [← e.toFanHom.algebraicMap.isClosedMap.closure_image_eq_of_continuous
      e.toFanHom.algebraicMap.continuous, Set.image_singleton, e.algebraicMap_rayBoundaryPoint]
  have hw' : w' = U[Ψ,hΨ,e.rayEquiv ρ] := by
    apply (C[Ψ]).eq_of_range_blowupComponent_subset (k := ℂ)
    rw [← Set.image_subset_image_iff (D[Ψ]).subschemeι.isClosedEmbedding.injective,
      ← Set.range_comp, ← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      ← TopCat.coe_comp, ← Scheme.Hom.comp_base, Category.assoc, Category.assoc,
      range_normalizationComponent_to_toric, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι, Scheme.coe_blowupComponent]
    exact hr.le
  exact congrArg Subtype.val hw'

end TauCeti.Toric.FanEquiv
