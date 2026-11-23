/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Common
public import QPainleve.Geometry.Toric.Fan.Mutation.Blowup
public import QPainleve.Geometry.Toric.Fan.Mutation.InternalBlowup

/-!
# Global mutation of the ordered internal blowups

Blow up the pivot first, then blow up the remaining centers in the prescribed order
on the successive strict boundaries. The global elementary transformation lifts to
these models because all the remaining centers match on the complement of the pivot
fiber. Repeated centers give the same ordered infinitely near lifts.

This extends the elementary transformation of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1](https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.IdealSheafData
open QPainleve.BlowupTower

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Module.Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
  (hOpp : PointedCone.hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : ℂˣ)

local notation "v" => Ray.primitiveGenerator ρ
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "hΦ" => Nonempty.intro (Ray.toCone Φ ρ)
local notation "hΨ" => Nonempty.intro (Φ.mutationFanConeEquiv b hv hp hOpp (Subtype.mk _ hp))
local notation "D₀" => Φ.boundaryIdeal hΦ
local notation "D₁" => boundaryIdeal (Ψ) hΨ
local notation "I₀" => Ray.mutationSourceCenterIdeal b ρ c
local notation "I₁" => Ray.mutationTargetCenterIdeal b ρ hOpp c

local notation "U₀" => mutationComplement Φ b (detCharacter_nonneg_or_nonpos Φ b hv hp hOpp)
  (Units.val c)
local notation "U₁" => mutationComplement (Ψ) b
  (mutationDetCharacter_nonneg_or_nonpos Φ b hv hp hOpp) (Units.val c)
local notation "eC" => Φ.mutationComplementIso b (Units.val c) hv hp hOpp
local notation "eB" => Ray.mutationBlowupIso b ρ hOpp c
local notation "J" => comap (D₀) (Scheme.Opens.ι (U₀))
local notation "d₀" => subschemeMap (J) (D₀) (Scheme.Opens.ι (U₀))
  (le_map_comap (D₀) (Scheme.Opens.ι (U₀)))
local notation "d₁" => subschemeMap (J) (D₁) (Iso.hom (eC) ≫ Scheme.Opens.ι (U₁))
  (le_map_iff_comap_le.mpr (Eq.le
    (comap_boundaryIdeal_mutationComplementIso b hv hp hOpp c hΦ hΨ)))

private theorem commonBoundary_comp_mutationBlowupIso
    (h₀ : (J).subschemeι ≫ (U₀).ι = (d₀) ≫ (D₀).subschemeι)
    (h₁ : (J).subschemeι ≫ (eC).hom ≫ (U₁).ι = (d₁) ≫ (D₁).subschemeι) :
    (d₀) ≫ ρ.mutationSourceBoundaryι b c ≫ (eB).hom =
      (d₁) ≫ ρ.mutationTargetBoundaryι b hOpp c := by
  let l₀ := (I₀).blowupLift (U₀).ι (by
    rw [ρ.mutationSourceCenterIdeal_comap_complement b hOpp c]
    exact isEffectiveCartier_top _)
  let l₁ := (I₁).blowupLift (U₁).ι (by
    rw [ρ.mutationTargetCenterIdeal_comap_complement b hOpp c]
    exact isEffectiveCartier_top _)
  have he₀ : (d₀) ≫ ρ.mutationSourceBoundaryι b c = (J).subschemeι ≫ l₀ := by
    apply (I₀).blowup_hom_ext
    · simpa only [Category.assoc, l₀, blowupLift_blowupToBase,
        Ray.mutationSourceBoundaryι_blowupToBase] using h₀.symm
    · simp only [Category.assoc, Ray.mutationSourceBoundaryι_blowupToBase, ← h₀, comap_comp,
        ρ.mutationSourceCenterIdeal_comap_complement b hOpp c, comap_top]
      exact isEffectiveCartier_top _
  have he₁ : (d₁) ≫ ρ.mutationTargetBoundaryι b hOpp c = (J).subschemeι ≫ (eC).hom ≫ l₁ := by
    apply (I₁).blowup_hom_ext
    · simpa only [Category.assoc, l₁, blowupLift_blowupToBase,
        Ray.mutationTargetBoundaryι_blowupToBase] using h₁.symm
    · simp only [Category.assoc, Ray.mutationTargetBoundaryι_blowupToBase, ← h₁, comap_comp,
        ρ.mutationTargetCenterIdeal_comap_complement b hOpp c, comap_top]
      exact isEffectiveCartier_top _
  rw [← Category.assoc, he₀, Category.assoc, he₁]
  exact congrArg ((J).subschemeι ≫ ·) (ρ.mutationComplementBlowupι_comp_mutationBlowupIso_hom
    b hOpp c)

variable {n : ℕ} (s : Fin n → Φ.Ray) (d : Fin n → ℂˣ)

local notation "r" => Φ.mutationFanRayEquiv b hv hp hOpp
local notation "δ" j:arg =>
  d j * c ^ max (Module.Basis.det b ![Ray.primitiveGenerator (s j), v]) 0
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "hχ(" τ ")" => Module.Basis.detDualEquiv_self b (Ray.primitiveGenerator τ)
local notation "center(" τ ", " k ")" =>
  Ray.binomialCenterOnBoundary τ rankTwo hχ(τ) (Ray.surjective_detCharacter τ b) k

/-- The global pivot isomorphism lifts through the ordered remaining blowups.
The resulting isomorphism identifies the strict boundaries on the pivot-fiber
complement. The remaining centers can repeat, and each must avoid the pivot fiber. -/
theorem exists_iso_mutation_internal_blowup_tower
    (hsame : ∀ j, (s j).primitiveGenerator = v → d j ≠ c)
    (hopp : ∀ j, (s j).primitiveGenerator = -v → d j * c ≠ 1) :
    let A := alongBoundary (ρ.mutationSourceBoundaryι b c)
      (fun j ↦ (s j).internalCenter (h₀ := hΦ) b (d j))
    let B := alongBoundary (ρ.mutationTargetBoundaryι b hOpp c)
      (fun j ↦ ((r) (s j)).internalCenter (h₀ := hΨ) b (δ j))
    ∃ e : A.1 ≅ B.1, IsLift (eB) A.2.toTower B.2.toTower e ∧
      (d₀) ≫ A.2.boundaryι ≫ e.hom = (d₁) ≫ B.2.boundaryι := by
  let : Nonempty Φ.cones := hΦ
  let : Nonempty (Ψ).cones := hΨ
  obtain ⟨t, h₀, h₁, ht₀, ht₁⟩ := exists_common_boundaryCenters_mutationComplement
    b hv hp hOpp c s d ρ.isPrimitiveGenerator.isPrimitive hsame hopp
  have : IsOpenImmersion (d₀) := MorphismProperty.of_isPullback h₀ inferInstance
  let s₀ := fun j ↦ center(s j, d j)
  let s₁ := fun j ↦ center((r) (s j), δ j)
  have hC₀ (j : Fin n) : (s₀ j).ker.IsEffectiveCartier := by
    exact (s j).internalCenter_val b (d j) ▸ ((s j).internalCenter b (d j)).property
  have hC₁ (j : Fin n) : (s₁ j).ker.IsEffectiveCartier := by
    exact ((r) (s j)).internalCenter_val b (δ j) ▸ (((r) (s j)).internalCenter b (δ j)).property
  have h := exists_isLift_alongBoundary_of_common (eB) (d₀) (d₁)
    (commonBoundary_comp_mutationBlowupIso b ρ hOpp c h₀.w h₁.w)
    t s₀ s₁ ht₀ ht₁ hC₀ hC₁ (fun j ↦ (hC₀ j).comap (d₀))
  have hJ₀ : (fun j ↦ ⟨(s₀ j).ker, hC₀ j⟩) = fun j ↦ (s j).internalCenter b (d j) :=
    funext fun j ↦ Subtype.ext ((s j).internalCenter_val b (d j)).symm
  have hJ₁ : (fun j ↦ ⟨(s₁ j).ker, hC₁ j⟩) =
      fun j ↦ ((r) (s j)).internalCenter (h₀ := hΨ) b (δ j) :=
    funext fun j ↦ Subtype.ext (((r) (s j)).internalCenter_val (h₀ := hΨ) b (δ j)).symm
  dsimp only
  rw [← hJ₀, ← hJ₁]
  exact h

end TauCeti.Toric.Fan
