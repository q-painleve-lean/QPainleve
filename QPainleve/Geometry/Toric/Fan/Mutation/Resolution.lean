/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.FunctionField
public import QPainleve.Geometry.Toric.Fan.Mutation.Blowup
public import QPainleve.Geometry.Toric.Fan.Mutation.Pullback
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic

import QPainleve.AlgebraicGeometry.Blowup.Integral
import QPainleve.AlgebraicGeometry.Blowup.Modification
import QPainleve.AlgebraicGeometry.Blowup.Pullback
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.AlgebraicGeometry.RationalMap.Restriction

/-!
# Resolving the toric mutation rational map

The partial map on the complement of the pivot fiber represents a dominant rational map.
The global pivot blowup isomorphism resolves this map. Its pullback on the function field,
and the pullback after any dominant refinement of the resolution, can thus be calculated
using the binomial twist on the toric complement.

The elementary transformation is that of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1](https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i) (b : Module.Basis (Fin 2) ℤ N) {v : N} (c : ℂ)
  (hv : v ≠ 0) (hpos : PointedCone.hull ℝ {i v} ∈ Φ.cones)
  (hneg : PointedCone.hull ℝ {i (-v)} ∈ Φ.cones)

local notation "Ψ" => Φ.mutationFan b hv hpos hneg
local notation "h₀" => Φ.detCharacter_nonneg_or_nonpos b hv hpos hneg
local notation "h₁" => Φ.mutationDetCharacter_nonneg_or_nonpos b hv hpos hneg
local notation "U₀" => Φ.mutationComplement b h₀ c
local notation "U₁" => mutationComplement (Ψ) b h₁ c
local notation "E" => Φ.mutationComplementIso b c hv hpos hneg
local notation "hΦ" => Nonempty.intro (Subtype.mk _ hpos : Φ.cones)
local notation "hΨ" => Nonempty.intro (Φ.mutationFanConeEquiv b hv hpos hneg (Subtype.mk _ hpos))

private theorem dense_mutationComplement : Dense (U₀ : Set Φ.algebraicRealization) := by
  let : Nonempty Φ.cones := hΦ
  have := Φ.isIntegral_mutationComplement_source b c hv hpos hneg
  exact (U₀).isOpen.dense (Set.nonempty_coe_sort.mp (inferInstance : Nonempty (U₀).toScheme))

/-- The elementary transformation on the complement of the pivot fiber, viewed as a
partial map from the original toric surface to the mutated one. -/
def mutationPartialMap : Φ.algebraicRealization.PartialMap (Ψ).algebraicRealization where
  domain := U₀
  dense_domain := Φ.dense_mutationComplement b c hv hpos hneg
  hom := (E).hom ≫ (U₁).ι

@[simp]
theorem mutationPartialMap_domain : (Φ.mutationPartialMap b c hv hpos hneg).domain = U₀ := (rfl)

@[simp]
theorem mutationPartialMap_hom :
    (Φ.mutationPartialMap b c hv hpos hneg).hom =
      (Φ.algebraicRealization.isoOfEq (Φ.mutationPartialMap_domain b c hv hpos hneg)).hom ≫
        (E).hom ≫ (U₁).ι := by
  unfold mutationPartialMap
  simp

instance : IsDominant (Φ.mutationPartialMap b c hv hpos hneg).hom := by
  let : Nonempty (Ψ).cones := hΨ
  have := Φ.isIntegral_mutationComplement_target b c hv hpos hneg
  unfold mutationPartialMap
  infer_instance

instance : (Φ.mutationPartialMap b c hv hpos hneg).toRationalMap.IsDominant :=
  (Φ.mutationPartialMap b c hv hpos hneg).isDominant_toRationalMap_iff.mpr inferInstance

/-- The dominant rational map of the elementary transformation induces the same function field
pullback as the isomorphism on the complements of its pivot fiber. -/
@[simp]
theorem functionFieldMap_mutationPartialMap_toRationalMap :
    letI : Nonempty Φ.cones := hΦ
    letI : Nonempty (Ψ).cones := hΨ
    (Φ.mutationPartialMap b c hv hpos hneg).toRationalMap.functionFieldMap =
      Φ.mutationComplementPullback b c hv hpos hneg := by
  let : Nonempty Φ.cones := hΦ
  let : Nonempty (Ψ).cones := hΨ
  have := Φ.isIntegral_mutationComplement_source b c hv hpos hneg
  have := Φ.isIntegral_mutationComplement_target b c hv hpos hneg
  let p := Φ.mutationPartialMap b c hv hpos hneg
  have : IsIntegral p.domain.toScheme := by
    simpa only [p, mutationPartialMap_domain] using
      Φ.isIntegral_mutationComplement_source b c hv hpos hneg
  have := Opens.isDominant_ι p.dense_domain
  have heq := (Scheme.RationalMap.functionFieldMap_eq_iff _ _).mpr
    p.hom_toRationalMap_eq_comp
  simp only [Scheme.Hom.functionFieldMap_toRationalMap, Scheme.RationalMap.functionFieldMap_comp]
    at heq
  apply (cancel_mono p.domain.ι.functionFieldMap).mp
  rw [← heq]
  simp only [p, mutationPartialMap, mutationComplementPullback_comp_functionFieldMap]

section Pivot

variable {Φ} (ρ : Φ.Ray)
  (hOpp : PointedCone.hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (a : ℂˣ)

local notation "vp" => Ray.primitiveGenerator ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "hnz" => Ray.primitiveGenerator_ne_zero ρ
local notation "Φ'" => Φ.mutationFan b hnz hp hOpp
local notation "hs" => Nonempty.intro (Ray.toCone Φ ρ)
local notation "ht" => Nonempty.intro (Φ.mutationFanConeEquiv b hnz hp hOpp (Ray.toCone Φ ρ))
local notation "Us" =>
  Φ.mutationComplement b (Φ.detCharacter_nonneg_or_nonpos b hnz hp hOpp) (a : ℂ)
local notation "Ut" =>
  mutationComplement (Φ') b (Φ.mutationDetCharacter_nonneg_or_nonpos b hnz hp hOpp) (a : ℂ)
local notation "C" => Φ.mutationComplementIso b (a : ℂ) hnz hp hOpp
local notation "I₀" => Ray.mutationSourceCenterIdeal b ρ a
local notation "I₁" => Ray.mutationTargetCenterIdeal b ρ hOpp a
local notation "e" => Ray.mutationBlowupIso b ρ hOpp a
local notation "q" => Scheme.PartialMap.toRationalMap (Φ.mutationPartialMap b (a : ℂ) hnz hp hOpp)

include hOpp in
private theorem dense_source_pivot_compl :
    Dense ((I₀).support.compl : Set Φ.algebraicRealization) := by
  let : Nonempty Φ.cones := hs
  have := Φ.isIntegral_mutationComplement_source b (a : ℂ) hnz hp hOpp
  exact (I₀).dense_compl_support_of_comap_eq_top (Us).ι
    (ρ.mutationSourceCenterIdeal_comap_complement b hOpp a)

private theorem dense_target_pivot_compl :
    Dense ((I₁).support.compl : Set (Φ').algebraicRealization) := by
  let : Nonempty (Φ').cones := ht
  have := Φ.isIntegral_mutationComplement_target b (a : ℂ) hnz hp hOpp
  exact (I₁).dense_compl_support_of_comap_eq_top (Ut).ι
    (ρ.mutationTargetCenterIdeal_comap_complement b hOpp a)

include hOpp in
/-- The blowup at the original pivot center is integral. -/
theorem Ray.isIntegral_mutationSourceBlowup : IsIntegral (I₀).blowup := by
  let : Nonempty Φ.cones := hs
  exact (I₀).isIntegral_blowup_of_nonempty_compl_support
    (Set.nonempty_coe_sort.mpr (dense_source_pivot_compl b ρ hOpp a).nonempty)

/-- The blowup at the opposite pivot center is integral. -/
theorem Ray.isIntegral_mutationTargetBlowup : IsIntegral (I₁).blowup := by
  have := ρ.isIntegral_mutationSourceBlowup b hOpp a
  exact IsIntegral.of_isIso (e).hom

include hOpp in
/-- The projection of the original pivot blowup is a modification. -/
theorem Ray.isModification_mutationSourceBlowupToBase : IsModification (I₀).blowupToBase :=
  (I₀).isModification_blowupToBase (dense_source_pivot_compl b ρ hOpp a)

/-- The projection of the opposite pivot blowup is a modification. -/
theorem Ray.isModification_mutationTargetBlowupToBase : IsModification (I₁).blowupToBase :=
  (I₁).isModification_blowupToBase (dense_target_pivot_compl b ρ hOpp a)

/-- The global pivot blowup isomorphism resolves the elementary transformation as an
equality of rational maps on the source blowup. -/
theorem Ray.mutationPartialMap_resolved :
    letI : Nonempty Φ.cones := hs
    letI := ρ.isIntegral_mutationSourceBlowup b hOpp a
    letI := ρ.isModification_mutationSourceBlowupToBase b hOpp a
    (I₀).blowupToBase.toRationalMap.comp (q) =
      ((e).hom ≫ (I₁).blowupToBase).toRationalMap := by
  let : Nonempty Φ.cones := hs
  let : Nonempty (Φ').cones := ht
  have := ρ.isIntegral_mutationSourceBlowup b hOpp a
  have := ρ.isModification_mutationSourceBlowupToBase b hOpp a
  have := Φ.isIntegral_mutationComplement_source b (a : ℂ) hnz hp hOpp
  let hI : ((I₀).comap (Us).ι).IsEffectiveCartier :=
    (ρ.mutationSourceCenterIdeal_comap_complement b hOpp a) ▸ isEffectiveCartier_top _
  let j := (I₀).blowupLift (Us).ι hI
  have hj : j ≫ (I₀).blowupToBase = (Us).ι := (I₀).blowupLift_blowupToBase _ _
  have : IsOpenImmersion j :=
    MorphismProperty.of_isPullback ((I₀).isPullback_blowupLift _ hI) inferInstance
  have : IsDominant j := inferInstance
  have hcomp : j ≫ (e).hom ≫ (I₁).blowupToBase = (C).hom ≫ (Ut).ι := by
    rw [← Category.assoc, ρ.mutationComplementBlowupι_comp_mutationBlowupIso_hom b hOpp a,
      Category.assoc, blowupLift_blowupToBase]
  apply Scheme.RationalMap.comp_left_injective j.toRationalMap
  dsimp only
  simp only [← Scheme.RationalMap.comp_assoc, Scheme.RationalMap.comp_toRationalMap,
    Scheme.Hom.toRationalMap_compHom, hj, hcomp]
  let p := Φ.mutationPartialMap b (a : ℂ) hnz hp hOpp
  simpa only [p, mutationPartialMap] using
    p.hom_toRationalMap_eq_comp.symm

/-- On a dominant refinement of the pivot blowup, the mutated rational map
is represented by the refined projection to the opposite pivot blowup. -/
theorem Ray.mutationPartialMap_resolved_of_comp_eq {W : Scheme} [IsIntegral W]
    (f : W ⟶ (I₀).blowup) (g : W ⟶ Φ.algebraicRealization) [IsDominant g]
    (hg : f ≫ (I₀).blowupToBase = g) :
    let : Nonempty Φ.cones := hs
    g.toRationalMap.comp q =
      (f ≫ (e).hom ≫ (I₁).blowupToBase).toRationalMap := by
  subst g
  intro hcones
  let := hcones
  have := ρ.isIntegral_mutationSourceBlowup b hOpp a
  have := ρ.isModification_mutationSourceBlowupToBase b hOpp a
  have : IsDominant f := IsModification.isDominant_of_comp f (I₀).blowupToBase
  calc
    _ = (f.toRationalMap.comp (I₀).blowupToBase.toRationalMap).comp q := by
      simp only [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom]
    _ = f.toRationalMap.comp ((I₀).blowupToBase.toRationalMap.comp q) :=
      Scheme.RationalMap.comp_assoc _ _ _
    _ = _ := by
      rw [ρ.mutationPartialMap_resolved b hOpp a, Scheme.RationalMap.comp_toRationalMap,
        Scheme.Hom.toRationalMap_compHom]

/-- The regular morphism from the pivot blowup to the mutated fan pulls back rational
functions by the toric mutation followed by the original blowup pullback. -/
theorem Ray.functionFieldMap_mutationBlowupIso :
    letI : Nonempty Φ.cones := hs
    letI : Nonempty (Φ').cones := ht
    letI := ρ.isIntegral_mutationSourceBlowup b hOpp a
    letI := ρ.isIntegral_mutationTargetBlowup b hOpp a
    letI := ρ.isModification_mutationSourceBlowupToBase b hOpp a
    letI := ρ.isModification_mutationTargetBlowupToBase b hOpp a
    (I₁).blowupToBase.functionFieldMap ≫ (e).hom.functionFieldMap =
      Φ.mutationComplementPullback b (a : ℂ) hnz hp hOpp ≫ (I₀).blowupToBase.functionFieldMap := by
  let : Nonempty Φ.cones := hs
  let : Nonempty (Φ').cones := ht
  have := ρ.isIntegral_mutationSourceBlowup b hOpp a
  have := ρ.isIntegral_mutationTargetBlowup b hOpp a
  have := ρ.isModification_mutationSourceBlowupToBase b hOpp a
  have := ρ.isModification_mutationTargetBlowupToBase b hOpp a
  rw [← Scheme.Hom.functionFieldMap_comp]
  have heq := (Scheme.RationalMap.functionFieldMap_eq_iff _ _).mpr
    (ρ.mutationPartialMap_resolved b hOpp a).symm
  simpa only [Scheme.RationalMap.functionFieldMap_comp, Scheme.Hom.functionFieldMap_toRationalMap,
    functionFieldMap_mutationPartialMap_toRationalMap] using heq

/-- The function field comparison persists after any dominant refinement of the
source pivot blowup, such as the remaining ordered internal blowups. -/
theorem Ray.functionFieldMap_comp_mutationBlowupIso {W : Scheme} [IrreducibleSpace W]
    (p : W ⟶ (I₀).blowup) [IsDominant p] :
    letI : Nonempty Φ.cones := hs
    letI : Nonempty (Φ').cones := ht
    letI := ρ.isIntegral_mutationSourceBlowup b hOpp a
    letI := ρ.isModification_mutationSourceBlowupToBase b hOpp a
    letI := ρ.isModification_mutationTargetBlowupToBase b hOpp a
    (p ≫ (e).hom ≫ (I₁).blowupToBase).functionFieldMap =
      Φ.mutationComplementPullback b (a : ℂ) hnz hp hOpp ≫
        (p ≫ (I₀).blowupToBase).functionFieldMap := by
  let : Nonempty Φ.cones := hs
  let : Nonempty (Φ').cones := ht
  have := ρ.isIntegral_mutationSourceBlowup b hOpp a
  have := ρ.isIntegral_mutationTargetBlowup b hOpp a
  have := ρ.isModification_mutationSourceBlowupToBase b hOpp a
  have := ρ.isModification_mutationTargetBlowupToBase b hOpp a
  rw [Scheme.Hom.functionFieldMap_comp p, Scheme.Hom.functionFieldMap_comp (e).hom,
    ρ.functionFieldMap_mutationBlowupIso b hOpp a,
    Scheme.Hom.functionFieldMap_comp p, Category.assoc]

/-- A character of the mutated model pulls back on a refined pivot blowup by the
binomial twist. All characters and the coefficient on the right are interpreted in
the function field of the refinement. -/
theorem Ray.functionFieldMap_comp_mutationBlowupIso_character {W : Scheme}
    [IsIntegral W] [W.Over (Spec (.of ℂ))]
    (p : W ⟶ (I₀).blowup) [IsDominant p]
    [(p ≫ (I₀).blowupToBase).IsOver (Spec (.of ℂ))] (m : N →+ ℤ) :
    letI : Nonempty Φ.cones := hs
    letI : Nonempty (Φ').cones := ht
    letI := ρ.isIntegral_mutationSourceBlowup b hOpp a
    letI := ρ.isModification_mutationSourceBlowupToBase b hOpp a
    letI := ρ.isModification_mutationTargetBlowupToBase b hOpp a
    let z (u : N →+ ℤ) := (p ≫ (I₀).blowupToBase).functionFieldMap (Φ.character (ofAdd u))
    (p ≫ (e).hom ≫ (I₁).blowupToBase).functionFieldMap ((Φ').character (ofAdd m)) =
      z m * (1 + algebraMap ℂ W.functionField (a : ℂ) * z (b.detDualEquiv vp).toAddMonoidHom) ^
        (-m vp) := by
  let : Nonempty Φ.cones := hs
  let : Nonempty (Φ').cones := ht
  have := ρ.isIntegral_mutationSourceBlowup b hOpp a
  have := ρ.isModification_mutationSourceBlowupToBase b hOpp a
  have := ρ.isModification_mutationTargetBlowupToBase b hOpp a
  dsimp only
  rw [ρ.functionFieldMap_comp_mutationBlowupIso b hOpp a]
  simp only [CommRingCat.comp_apply, mutationComplementPullback_character,
    map_mul, map_one, map_add, map_zpow₀, Scheme.Hom.functionFieldMap_algebraMap ℂ]

end Pivot

end TauCeti.Toric.Fan
