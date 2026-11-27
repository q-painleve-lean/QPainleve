/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Common
public import QPainleve.Geometry.Toric.Fan.Mutation.InternalBlowup
public import QPainleve.Geometry.Toric.Fan.Mutation.Transport
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic

import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# Global mutation of the ordered internal blowups

Blow up the pivot first, then blow up the remaining centers in the prescribed order
on the successive strict boundaries. The global elementary transformation lifts to
these models using the comparison of center ideals on the strict boundaries.
Repeated centers give ordered infinitely near lifts, also over the pivot fiber.

This extends the elementary transformation of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1](https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.IdealSheafData
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable (K : Type) [Field K] {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Module.Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
  (hOpp : PointedCone.hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : Kˣ)

local notation "v" => Ray.primitiveGenerator ρ
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "hΦ₀" => Nonempty.intro (Ray.toCone Φ ρ)
local notation "hΨ" => Nonempty.intro (Φ.mutationFanConeEquiv b hv hp hOpp (Subtype.mk _ hp))
local notation "D₀" => Φ.toricBoundaryIdeal K hΦ₀
local notation "D₁" => toricBoundaryIdeal K (Ψ) hΨ
local notation "I₀" => Ray.mutationSourceCenterIdeal b ρ c
local notation "I₁" => Ray.mutationTargetCenterIdeal b ρ hOpp c
local notation "eB" => Ray.mutationBlowupIso b ρ hOpp c
local notation "j₀" => Ray.mutationSourceBoundaryι b ρ c
local notation "j₁" => Ray.mutationTargetBoundaryι b ρ hOpp c

/-- An ordered lift of the global pivot isomorphism identifies the full strict-boundary
ideals. The tower may contain repeated centers. -/
theorem Ray.comap_strictBoundary_mutationBlowupIso_lift (hΦ : Φ.IsRegular) {n : ℕ}
    {J : Fin n → {K : (D₀).subscheme.IdealSheafData // K.IsEffectiveCartier}}
    {J' : Fin n → {K : (D₁).subscheme.IdealSheafData // K.IsEffectiveCartier}}
    {e : (alongBoundary (j₀) J).1 ≅ (alongBoundary (j₁) J').1}
    (he : IsLift (eB) (alongBoundary (j₀) J).2.toTower (alongBoundary (j₁) J').2.toTower e) :
    ((alongBoundary (j₁) J').2.boundaryι.ker).comap e.hom =
      (alongBoundary (j₀) J).2.boundaryι.ker := by
  let u := ρ.mutationBoundaryIso b hOpp c hΦ
  have h := (he.alongBoundary u (ρ.mutationBoundaryIso_hom_comp_boundaryι b hOpp c hΦ).symm).2
  rw [← Scheme.Hom.ker_comp_of_isIso u.hom, ← h,
    Scheme.Hom.comap_ker_comp_of_isClosedImmersion]

local notation "U₀" => mutationComplement Φ b (detCharacter_nonneg_or_nonpos Φ b hv hp hOpp)
  (Units.val c)
local notation "U₁" => mutationComplement (Ψ) b
  (mutationDetCharacter_nonneg_or_nonpos Φ b hv hp hOpp) (Units.val c)
local notation "eC" => Φ.mutationComplementIso b (Units.val c) hv hp hOpp
local notation "J" => comap (D₀) (Scheme.Opens.ι (U₀))
local notation "d₀" => subschemeMap (J) (D₀) (Scheme.Opens.ι (U₀))
  (le_map_comap (D₀) (Scheme.Opens.ι (U₀)))
local notation "d₁" => subschemeMap (J) (D₁) (Iso.hom (eC) ≫ Scheme.Opens.ι (U₁))
  (le_map_iff_comap_le.mpr (Eq.le
    (comap_boundaryIdeal_mutationComplementIso b hv hp hOpp c hΦ₀ hΨ)))

variable {n : ℕ} (s : Fin n → Φ.Ray) (d : Fin n → Kˣ)

local notation "r" => Φ.mutationFanRayEquiv b hv hp hOpp
local notation "δ" j:arg =>
  d j * c ^ max (Module.Basis.det b ![Ray.primitiveGenerator (s j), v]) 0

/-- The elementary transformation lifts through the remaining ordered blowups.
All remaining centers follow the sheared rays, including repeated centers on
either horizontal component over the pivot fiber. The lift identifies the final
strict boundaries and preserves the order of the centers. -/
theorem Ray.exists_isLift_mutation_alongBoundary (hΦ : Φ.IsRegular) :
    let A := alongBoundary (j₀) (fun j ↦ (s j).internalCenter (h₀ := hΦ₀) K b (d j))
    let B := alongBoundary (j₁) (fun j ↦ ((r) (s j)).internalCenter (h₀ := hΨ) K b (δ j))
    ∃ e : A.1 ≅ B.1, IsLift (eB) A.2.toTower B.2.toTower e ∧
      A.2.boundaryι ≫ e.hom = (ρ.mutationBoundaryIso b hOpp c hΦ).hom ≫ B.2.boundaryι :=
  exists_isLift_alongBoundary (eB) (ρ.mutationBoundaryIso b hOpp c hΦ)
    (ρ.mutationBoundaryIso_hom_comp_boundaryι b hOpp c hΦ).symm _ _
    (fun j ↦ ρ.mutationBoundaryIso_transports_internal_centers K b hOpp c hΦ (s j) (d j))

local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "hχ(" τ ")" => Module.Basis.detDualEquiv_self b (Ray.primitiveGenerator τ)
local notation "center(" τ ", " k ")" =>
  Ray.binomialCenterOnBoundary τ K rankTwo hχ(τ) (Ray.surjective_detCharacter τ b) k

/-- The global pivot isomorphism lifts through the ordered remaining blowups.
The resulting isomorphism identifies the strict boundaries on the pivot-fiber
complement. The remaining centers can repeat, and each must avoid the pivot fiber. -/
theorem exists_iso_mutation_internal_blowup_tower
    (hsame : ∀ j, (s j).primitiveGenerator = v → d j ≠ c)
    (hopp : ∀ j, (s j).primitiveGenerator = -v → d j * c ≠ 1) :
    let A := alongBoundary (ρ.mutationSourceBoundaryι b c)
      (fun j ↦ (s j).internalCenter (h₀ := hΦ₀) K b (d j))
    let B := alongBoundary (ρ.mutationTargetBoundaryι b hOpp c)
      (fun j ↦ ((r) (s j)).internalCenter (h₀ := hΨ) K b (δ j))
    ∃ e : A.1 ≅ B.1, IsLift (eB) A.2.toTower B.2.toTower e ∧
      (d₀) ≫ A.2.boundaryι ≫ e.hom = (d₁) ≫ B.2.boundaryι := by
  let : Nonempty Φ.cones := hΦ₀
  let : Nonempty (Ψ).cones := hΨ
  obtain ⟨t, h₀, _, ht₀, ht₁⟩ := exists_common_boundaryCenters_mutationComplement
    K b hv hp hOpp c s d ρ.isPrimitiveGenerator.isPrimitive hsame hopp
  have : IsOpenImmersion (d₀) := MorphismProperty.of_isPullback h₀ inferInstance
  let s₀ := fun j ↦ center(s j, d j)
  let s₁ := fun j ↦ center((r) (s j), δ j)
  have hC₀ (j : Fin n) : (s₀ j).ker.IsEffectiveCartier := by
    exact (s j).internalCenter_val K b (d j) ▸ ((s j).internalCenter K b (d j)).property
  have hC₁ (j : Fin n) : (s₁ j).ker.IsEffectiveCartier := by
    exact ((r) (s j)).internalCenter_val K b (δ j) ▸ (((r) (s j)).internalCenter K b (δ j)).property
  have h := exists_isLift_alongBoundary_of_common (eB) (d₀) (d₁)
    (ρ.commonBoundary_comp_mutationBlowupIso K b hOpp c)
    t s₀ s₁ ht₀ ht₁ hC₀ hC₁ (fun j ↦ (hC₀ j).comap (d₀))
  have hJ₀ : (fun j ↦ ⟨(s₀ j).ker, hC₀ j⟩) = fun j ↦ (s j).internalCenter K b (d j) :=
    funext fun j ↦ Subtype.ext ((s j).internalCenter_val K b (d j)).symm
  have hJ₁ : (fun j ↦ ⟨(s₁ j).ker, hC₁ j⟩) =
      fun j ↦ ((r) (s j)).internalCenter (h₀ := hΨ) K b (δ j) :=
    funext fun j ↦ Subtype.ext (((r) (s j)).internalCenter_val (h₀ := hΨ) K b (δ j)).symm
  dsimp only
  rw [← hJ₀, ← hJ₁]
  exact h

local notation "A" => internalBlowupTower (h₀ := hΦ₀) K b s d
local notation "targetModel(" t ", " e ")" => internalBlowupTower (h₀ := hΨ) K b t e

/-- A map of the ordered models restricts to the pivot boundary isomorphism
when its projections satisfy the elementary transformation square. The source and target
models can have arbitrary ordered internal centers. -/
@[reassoc]
theorem boundaryι_comp_of_ordered_mutation {m : ℕ}
    (targetRays : Fin m → (Ψ).Ray) (targetParams : Fin m → Kˣ) (hΦ : Φ.IsRegular)
    {g : (A).1 ⟶ (targetModel(targetRays, targetParams)).1} {f : (A).1 ⟶ (I₀).blowup}
    (hf : f ≫ (I₀).blowupToBase = (A).2.toTower.toBase)
    (hg : g ≫ (targetModel(targetRays, targetParams)).2.toTower.toBase =
      f ≫ (eB).hom ≫ (I₁).blowupToBase) :
    (A).2.boundaryι ≫ g =
      (ρ.mutationBoundaryIso b hOpp c hΦ).hom ≫
        (targetModel(targetRays, targetParams)).2.boundaryι := by
  let B := targetModel(targetRays, targetParams)
  let : Nonempty Φ.cones := hΦ₀
  let : Nonempty (Ψ).cones := hΨ
  let a := (ρ.mutationBoundaryIso b hOpp c hΦ).hom
  have hA : (A).2.boundaryι ≫ f = (j₀) := by
    apply (I₀).blowup_hom_ext
    · simp only [Category.assoc, hf, WithBoundary.boundaryι_toBase,
        Ray.mutationSourceBoundaryι_blowupToBase]
    · rw [Category.assoc, hf, WithBoundary.boundaryι_toBase, Ray.mutationSourceCenterIdeal_eq,
        ← Ray.map_internalCenter_subschemeι, comap_map_of_isClosedImmersion]
      exact (ρ.internalCenter (h₀ := hΦ₀) K b c).property
  let j := (D₁).subschemeι
  have hB : ((A).2.boundaryι ≫ g) ≫ (B).2.toTower.toBase = a ≫ j := by
    rw [Category.assoc, hg, ← Category.assoc (A).2.boundaryι f, hA,
      ← Ray.mutationBoundaryIso_hom_comp_boundaryι_assoc,
      Ray.mutationTargetBoundaryι_blowupToBase]
  let P (U : Σ Z, WithBoundary j m Z) :=
    ∀ p : (D₀).subscheme ⟶ U.1,
      p ≫ U.2.toTower.toBase = a ≫ j → p = a ≫ U.2.boundaryι
  suffices P (B) from this _ hB
  simp only [B, internalBlowupTower_eq_alongBoundary]
  intro p hproj
  exact eq_comp_boundaryι_of_comp_toBase_eq j _ a (fun l ↦
    ((targetRays l).internalCenter (h₀ := hΨ) K b (targetParams l)).property.comap a) p hproj

variable (rays : Fin n → Φ.Ray) (params : Fin n → Kˣ)

local notation "π₀" => Scheme.IdealSheafData.blowupToBase (I₀)

/-- The projection from the ordered source model to the pivot blowup is a
modification. In particular it can be used as a dominant refinement in the
fixed-center X-evaluation comparison. -/
theorem Ray.isModification_toBase_alongMutationSourceBoundary [PerfectField K] (hΦ : Φ.IsRegular) :
    IsModification (alongBoundary (j₀)
      (fun j ↦ Ray.internalCenter (h₀ := hΦ₀) K b (rays j) (params j))).2.toTower.toBase := by
  let : Nonempty Φ.cones := hΦ₀
  have hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  have : SmoothOfRelativeDimension 2 (Φ.finiteFanSchemeToSpec K) :=
    hdim ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ
  let pt := ρ.binomialCenter K hdim (b.detDualEquiv_self v) (ρ.surjective_detCharacter b) c
  let x := pt (IsLocalRing.closedPoint K)
  have hx : IsClosed ({x} : Set (Φ.finiteFanScheme K)) :=
    isClosed_singleton_of_section (ρ.binomialCenter_comp_structureMap K hdim
      (b.detDualEquiv_self v) (ρ.surjective_detCharacter b) c)
  have hxI : (I₀) = ((Φ.finiteFanScheme K).fromSpecResidueField x).ker :=
    (ρ.mutationSourceCenterIdeal_eq b c).trans pt.ker_eq_ker_fromSpecResidueField
  let T := (BlowupTower.nil (X := (Φ.finiteFanScheme K))).snoc (I₀)
  have hT : IsClosedPointTower (Φ.finiteFanScheme K) T := IsClosedPointTower.nil.snoc x hx hxI
  have : IsIntegral (I₀).blowup := hT.isIntegral (Φ.finiteFanSchemeToSpec K)
  have : SmoothOfRelativeDimension 2 ((π₀) ≫ (Φ.finiteFanSchemeToSpec K)) := by
    simpa only [T, toBase_snoc, toBase_nil, Category.comp_id] using
      hT.smoothOfRelativeDimension (Φ.finiteFanSchemeToSpec K)
  apply IsClosedPointTower.isModification_of_smoothOfRelativeDimension_two
    (f := (π₀) ≫ (Φ.finiteFanSchemeToSpec K))
  apply isClosedPointTower_alongBoundary
  intro j
  rw [Ray.internalCenter_val]
  exact (rays j).exists_closedPoint_ker_binomialCenterOnBoundary K hdim
    (b.detDualEquiv_self (rays j).primitiveGenerator) ((rays j).surjective_detCharacter b)
    (params j)

end TauCeti.Toric.Fan
