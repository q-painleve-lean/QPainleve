/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
public import QPainleve.Geometry.Toric.Fan.Mutation.Indeterminacy

import QPainleve.AlgebraicGeometry.Blowup.Tower.IsoLocus
import QPainleve.AlgebraicGeometry.Blowup.Tower.Reorder
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Modules.Differentials.PoleIdeal
import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.Mutation.PoleIdeal
import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# Toric elementary transformations on specified point towers

A point-blowup tower resolves a toric elementary transformation exactly when one of
its centers projects to the pivot. The resulting morphism and the original tower
projection have the same pole factorization on the resolving surface. This compares
the regular partial composites in the factorization of [Lutz, Theorem 8.4][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable (K : Type) [Field K] {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : Kˣ)

local notation "S" => Spec (CommRingCat.of K)
local notation "X[" A "]" => Fan.finiteFanScheme K A
local notation "s[" A "]" => (X[A] ↘ S)
local notation "v" => Ray.primitiveGenerator ρ
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "U" => Ray.mutationSourceCenterIdeal b ρ c
local notation "U'" => Ray.mutationTargetCenterIdeal b ρ hOpp c
local notation "π" => Scheme.IdealSheafData.blowupToBase U
local notation "π'" =>
  CategoryTheory.Iso.hom (ρ.mutationBlowupIso b hOpp c) ≫ Scheme.IdealSheafData.blowupToBase U'
local notation "hΦ₀" => Nonempty.intro (Ray.toCone Φ ρ)
local notation "hΨ₀" => Nonempty.intro (Φ.mutationFanConeEquiv b hv hp hOpp ρ.toCone)
local notation "q" => Scheme.PartialMap.toRationalMap (Φ.mutationPartialMap K b (c : K) hv hp hOpp)
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "center" => ρ.binomialCenter K rankTwo (b.detDualEquiv_self v)
  (ρ.surjective_detCharacter b) c
local notation "p" => (center) (IsLocalRing.closedPoint K)

variable {n : ℕ} {W : Scheme} {T : BlowupTower (Φ.finiteFanScheme K) n W}
  (hT : IsClosedPointTower (Φ.finiteFanScheme K) T)

private theorem exists_mutation_pivot_lift (h : p ∈ Set.range hT.baseCenter) :
    ∃ f : W ⟶ (U).blowup, f ≫ π = T.toBase := by
  cases T with
  | nil =>
    obtain ⟨j, -⟩ := h
    exact j.elim0
  | @snoc n Z T J =>
    let A : Set (Fin (n + 1)) := {j | hT.baseCenter j = p}
    obtain ⟨j, hj, hjmin⟩ := Set.exists_min_image A id (Set.toFinite A) h
    have hpClosed : IsClosed ({p} : Set X[Φ]) := isClosed_singleton_of_section
      (ρ.binomialCenter_comp_structureMap K rankTwo (b.detDualEquiv_self v)
        (ρ.surjective_detCharacter b) c)
    have hI : U = (X[Φ].fromSpecResidueField p).ker :=
      (ρ.mutationSourceCenterIdeal_eq b c).trans (center).ker_eq_ker_fromSpecResidueField
    have hsplit := hT.exists_move_closed_point_blowup_to_front j hpClosed hj
      (fun l hl he ↦ (not_le_of_gt hl) (hjmin l he))
    rw [← hI] at hsplit
    obtain ⟨_, L, e, _, he, -⟩ := hsplit
    exact ⟨e.hom ≫ L.toBase, (Category.assoc _ _ _).trans he⟩

variable [PerfectField K]

include hOpp in
private theorem pivot_mem_range_baseCenter_of_resolves [Nonempty Φ.cones]
    [SmoothOfRelativeDimension 2 s[Φ]] [IsIntegral W] [IsDominant T.toBase]
    (r : W ⟶ X[Ψ]) (hr : T.toBase.toRationalMap.comp q = r.toRationalMap) :
    p ∈ Set.range hT.baseCenter := by
  rw [← hT.centre_toBase_eq_range_baseCenter s[Φ]]
  exact ρ.mutationSourceCenter_mem_centre_of_resolves K b hOpp c T.toBase r hr

include hOpp hT in
private theorem exists_mutation_pivot_lift_of_resolves [Nonempty Φ.cones]
    [SmoothOfRelativeDimension 2 s[Φ]] [IsIntegral W] [IsDominant T.toBase]
    (r : W ⟶ X[Ψ]) (hr : T.toBase.toRationalMap.comp q = r.toRationalMap) :
    ∃ f : W ⟶ (U).blowup, f ≫ π = T.toBase ∧ f ≫ π' = r := by
  let : Nonempty (Ψ).cones := hΨ₀
  let : Scheme.IsSeparated X[Ψ] := inferInstance
  have hm := pivot_mem_range_baseCenter_of_resolves K b ρ hOpp c hT r hr
  obtain ⟨f, hf⟩ := exists_mutation_pivot_lift K b ρ c hT hm
  have hq := ρ.mutationPartialMap_resolved_of_comp_eq K b hOpp c f T.toBase hf
  exact ⟨f, hf, Scheme.Hom.toRationalMap_injective (hq.symm.trans hr)⟩

include hOpp in
/-- A specified closed point tower resolves the elementary transformation if and only if
some center projects to the source pivot. The regular representative is unique. -/
theorem Ray.existsUnique_mutation_resolution_of_closedPointTower_iff (hΦ : Φ.IsRegular) :
    letI : Nonempty Φ.cones := hΦ₀
    letI : SmoothOfRelativeDimension 2 s[Φ] :=
      (Φ.finiteFanScheme_over K).symm ▸
        (rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ)
    letI : IsIntegral W := hT.isIntegral s[Φ]
    letI : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two s[Φ]
    (∃! r : W ⟶ X[Ψ], T.toBase.toRationalMap.comp q = r.toRationalMap) ↔
      p ∈ Set.range hT.baseCenter := by
  let : Nonempty Φ.cones := hΦ₀
  have : SmoothOfRelativeDimension 2 s[Φ] :=
    (Φ.finiteFanScheme_over K).symm ▸
      (rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ)
  have := hT.isIntegral s[Φ]
  have := hT.isModification_of_smoothOfRelativeDimension_two s[Φ]
  constructor
  · rintro ⟨r, hr, -⟩
    exact pivot_mem_range_baseCenter_of_resolves K b ρ hOpp c hT r hr
  · intro hm
    obtain ⟨f, hf⟩ := exists_mutation_pivot_lift K b ρ c hT hm
    have he := ρ.mutationPartialMap_resolved_of_comp_eq K b hOpp c f T.toBase hf
    refine ⟨f ≫ π', he, fun r hr ↦ ?_⟩
    let : Nonempty (Ψ).cones := hΨ₀
    let : Scheme.IsSeparated X[Ψ] := inferInstance
    exact Scheme.Hom.toRationalMap_injective (hr.symm.trans he)

include hOpp in
/-- On any specified closed point tower resolving the mutation, the two projections to
the toric surfaces have the same pole ideal after accounting for their ramification.
The regular representative of the mutated projection is over the ground field. -/
theorem Ray.mutation_resolution_poleIdeal_iff (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (r : W ⟶ X[Ψ]) (D : W.IdealSheafData) :
    letI : Nonempty Φ.cones := hΦ₀
    letI : SmoothOfRelativeDimension 2 s[Φ] :=
      (Φ.finiteFanScheme_over K).symm ▸
        (rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ)
    letI : IsIntegral W := hT.isIntegral s[Φ]
    letI : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two s[Φ]
    T.toBase.toRationalMap.comp q = r.toRationalMap →
    letI : W.Over S := ⟨T.toBase ≫ s[Φ]⟩
    letI : Smooth (W ↘ S) := (hT.smoothOfRelativeDimension s[Φ]).smooth
    ∃ hOver : r.IsOver S, letI := hOver
      (Φ.toricBoundaryIdeal K hΦ₀).comap T.toBase = D * hT.ramificationIdealSheafToBase K ↔
      (Fan.toricBoundaryIdeal K (Ψ) hΨ₀).comap r = D * ramificationIdealSheaf K r := by
  let : Nonempty Φ.cones := hΦ₀
  let : Nonempty (Ψ).cones := hΨ₀
  have : SmoothOfRelativeDimension 2 s[Φ] :=
    (Φ.finiteFanScheme_over K).symm ▸
      (rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ)
  have := hT.isIntegral s[Φ]
  have := hT.isModification_of_smoothOfRelativeDimension_two s[Φ]
  intro hr
  obtain ⟨f, hf, hproj⟩ := exists_mutation_pivot_lift_of_resolves K b ρ hOpp c hT r hr
  have hΨ := (Φ.isRegular_mutationFan_iff b hv hp hOpp).mpr hΦ
  have : SmoothOfRelativeDimension 2 s[Ψ] :=
    ((Ψ).finiteFanScheme_over K).symm ▸
      (rankTwo ▸ (Ψ).smoothOfRelativeDimension_finiteFanSchemeToSpec K hΨ)
  obtain ⟨hU, hU', -, hD, hD'⟩ := ρ.mutationBlowupIso_pole_ideal K b c hOpp hΦ hc
  let : (U).blowup.Over S := ⟨π ≫ s[Φ]⟩
  let : W.Over S := ⟨T.toBase ≫ s[Φ]⟩
  have hdimPivot : SmoothOfRelativeDimension 2 (π ≫ s[Φ]) := by
    simpa only [toBase_snoc, toBase_nil, Category.comp_id] using hU.smoothOfRelativeDimension s[Φ]
  have : SmoothOfRelativeDimension 2 ((U).blowup ↘ S) := hdimPivot
  have : SmoothOfRelativeDimension 2 (W ↘ S) := hT.smoothOfRelativeDimension s[Φ]
  have : Smooth (W ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : Smooth ((U).blowup ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : Scheme.Hom.IsOver π S := ⟨rfl⟩
  have hπ' : (π') ≫ s[Ψ] = π ≫ s[Φ] := by
    simpa only [Category.assoc, Fan.finiteFanScheme_over] using
      ρ.mutationBlowupIso_hom_comp_toBase b hOpp c
  have : (π').IsOver S := ⟨hπ'⟩
  have : f.IsOver S := ⟨(Category.assoc _ _ _).symm.trans ((reassoc_of% hf) _)⟩
  have : T.toBase.IsOver S := ⟨rfl⟩
  have : r.IsOver S := hproj ▸ inferInstanceAs ((f ≫ π').IsOver S)
  have hram : hU.ramificationIdealSheafToBase K = ramificationIdealSheaf K π := by
    refine (hU.ramificationIdealSheafToBase_def K).trans (ramificationIdealSheaf_congr K ?_)
    simp only [toBase_snoc, toBase_nil, Category.comp_id]
  have hram' : (hU'.ramificationIdealSheafToBase K).comap
      (ρ.mutationBlowupIso b hOpp c).hom = ramificationIdealSheaf K π' :=
    hU'.comap_ramificationIdealSheafToBase K (ρ.mutationBlowupIso b hOpp c)
      (by simp only [toBase_snoc, toBase_nil, Category.comp_id])
  have := ρ.isModification_mutationSourceBlowupToBase K b hOpp c
  have := ρ.isIntegral_mutationSourceBlowup K b hOpp c
  have : IsDominant (f ≫ π) := hf ▸ inferInstanceAs (IsDominant T.toBase)
  have : IsDominant f := IsModification.isDominant_of_comp f π
  have hCart := (hU.isEffectiveCartier_ramificationIdealSheafToBase K).comap_of_isDominant f
  rw [hram] at hD hCart
  rw [hram'] at hD'
  refine ⟨‹_›, ?_⟩
  have h₁ := comap_eq_mul_ramificationIdealSheaf_comp_iff K f π 2 hCart hD (Q := D)
  have h₂ := comap_eq_mul_ramificationIdealSheaf_comp_iff K f π' 2
    ((hram' ▸ (hU'.isEffectiveCartier_ramificationIdealSheafToBase K).comap
      (ρ.mutationBlowupIso b hOpp c).hom).comap_of_isDominant f) hD' (Q := D)
  simpa only [hf, hproj, hT.ramificationIdealSheafToBase_def K] using h₁.trans h₂.symm

include hOpp in
/-- Transport a pole factorization to a closed point tower whose projection represents the
mutation composite via an isomorphism of resolving surfaces. -/
theorem Ray.mutation_projection_poleIdeal (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    [Nonempty Φ.cones]
    [SmoothOfRelativeDimension 2 s[Φ]] [SmoothOfRelativeDimension 2 s[Ψ]]
    [IsIntegral W] [IsModification T.toBase]
    {m : ℕ} {Z : Scheme} {T' : BlowupTower X[Ψ] m Z} (hT' : IsClosedPointTower X[Ψ] T')
    (k : W ≅ Z)
    (hlink : T.toBase.toRationalMap.comp q = (k.hom ≫ T'.toBase).toRationalMap)
    (D : W.IdealSheafData)
    (hD : (Φ.toricBoundaryIdeal K hΦ₀).comap T.toBase = D * hT.ramificationIdealSheafToBase K) :
    (Fan.toricBoundaryIdeal K (Ψ) hΨ₀).comap T'.toBase =
      D.comap k.inv * hT'.ramificationIdealSheafToBase K := by
  let : W.Over S := ⟨T.toBase ≫ s[Φ]⟩
  let : SmoothOfRelativeDimension 2 (W ↘ S) := hT.smoothOfRelativeDimension s[Φ]
  let : Smooth (W ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  obtain ⟨hOver, hPole⟩ :=
    ρ.mutation_resolution_poleIdeal_iff K b hOpp c hT hΦ hc (k.hom ≫ T'.toBase) D hlink
  let := hOver
  have hram := hT'.comap_ramificationIdealSheafToBase K k (f := k.hom ≫ T'.toBase) rfl
  have h := congrArg (fun J : W.IdealSheafData ↦ J.comap k.inv) (hPole.mp hD)
  simpa only [hram.symm, comap_mul, ← comap_comp, k.inv_hom_id_assoc, k.inv_hom_id,
    comap_id] using h

end TauCeti.Toric.Fan
