/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Mutation.Boundary

import QPainleve.Geometry.Toric.Fan.Mutation.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Ruling.Boundary
import QPainleve.LinearAlgebra.Dual.Basis

/-!
# Transport of centers through toric mutation

The isomorphism of the strict boundaries of the two pivot blowups identifies
the binomial center ideals on corresponding ray components. On the two
horizontal components this follows from preservation of the ruling, including
at the points over the pivot fiber. On every other component the mutation is
already defined on the ruling complement.

The elementary transformation is that of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1](https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : ℂˣ)

local notation "v" => Ray.primitiveGenerator ρ
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "hΦ₀" => Nonempty.intro (Ray.toCone Φ ρ)
local notation "hΨ₀" => Nonempty.intro (Φ.mutationFanConeEquiv b hv hp hOpp (Subtype.mk _ hp))
local notation "D₀" => Φ.boundaryIdeal hΦ₀
local notation "D₁" => boundaryIdeal (Ψ) hΨ₀
local notation "I₀" => Ray.mutationSourceCenterIdeal b ρ c
local notation "I₁" => Ray.mutationTargetCenterIdeal b ρ hOpp c
local notation "eB" => Ray.mutationBlowupIso b ρ hOpp c
local notation "j₀" => Ray.mutationSourceBoundaryι b ρ c
local notation "j₁" => Ray.mutationTargetBoundaryι b ρ hOpp c

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
    (comap_boundaryIdeal_mutationComplementIso b hv hp hOpp c hΦ₀ hΨ₀)))

/-- The global pivot isomorphism and the complement isomorphism agree on the
common boundary open. -/
theorem Ray.commonBoundary_comp_mutationBlowupIso :
    (d₀) ≫ (j₀) ≫ (eB).hom = (d₁) ≫ (j₁) := by
  have h₀ : (J).subschemeι ≫ (U₀).ι = (d₀) ≫ (D₀).subschemeι :=
    (subschemeMap_subschemeι _ _ _ _).symm
  have h₁ : (J).subschemeι ≫ (eC).hom ≫ (U₁).ι = (d₁) ≫ (D₁).subschemeι :=
    (subschemeMap_subschemeι _ _ _ _).symm
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

variable (hΦ : Φ.IsRegular) (u : Φ.Ray) (d : ℂˣ)

local notation "a" => Ray.mutationBoundaryIso b ρ hOpp c hΦ
local notation "r" => Φ.mutationFanRayEquiv b hv hp hOpp
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hOpp) hΦ
local notation "char" => LinearMap.toAddMonoidHom (b.detDualEquiv v)
local notation "r₀" => Φ.characterRuling char (Φ.detCharacter_nonneg_or_nonpos b hv hp hOpp)
local notation "r₁" =>
  characterRuling (Ψ) char (Φ.mutationDetCharacter_nonneg_or_nonpos b hv hp hOpp)
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "χ(" τ ")" => LinearMap.toAddMonoidHom (b.detDualEquiv (Ray.primitiveGenerator τ))
local notation "hχ(" τ ")" => Eq.trans
  (congrFun (LinearMap.toAddMonoidHom_coe (b.detDualEquiv (Ray.primitiveGenerator τ)))
    (Ray.primitiveGenerator τ)) (b.detDualEquiv_self (Ray.primitiveGenerator τ))
local notation "center(" τ ", " k ")" =>
  Ray.binomialCenterOnBoundary τ rankTwo (m := χ(τ)) hχ(τ) (Ray.surjective_detCharacter τ b) k
local notation "δ" =>
  d * c ^ max (b.det ![Ray.primitiveGenerator u, v]) 0

private theorem binomialCenterOnBoundary_comp_mutationBoundaryIso_of_avoids_pivot
    (hsame : u.primitiveGenerator = v → d ≠ c)
    (hopp : u.primitiveGenerator = -v → d * c ≠ 1) :
    center(u, d) ≫ (a).hom = center((r u), δ) := by
  let : Nonempty Φ.cones := hΦ₀
  obtain ⟨t, _, _, h₀, h₁⟩ := exists_common_boundaryCenters_mutationComplement
    b hv hp hOpp c (fun _ : Fin 1 ↦ u) (fun _ ↦ d)
    ρ.isPrimitiveGenerator.isPrimitive (fun _ ↦ hsame) (fun _ ↦ hopp)
  have h := h₀ 0
  dsimp only at h
  have he : (d₀) ≫ (a).hom = d₁ := by
    rw [← cancel_mono (j₁), Category.assoc, Ray.mutationBoundaryIso_hom_comp_boundaryι]
    exact ρ.commonBoundary_comp_mutationBlowupIso b hOpp c
  rw [← h, Category.assoc, he]
  exact h₁ 0

private theorem mutationBoundaryIso_comp_ruling :
    (a).hom ≫ (D₁).subschemeι ≫ (r₁) = (D₀).subschemeι ≫ (r₀) := by
  rw [← Ray.mutationTargetBoundaryι_blowupToBase_assoc,
    Ray.mutationBoundaryIso_hom_comp_boundaryι_assoc,
    Ray.mutationBlowupIso_hom_comp_ruling,
    Ray.mutationSourceBoundaryι_blowupToBase_assoc]

private theorem binomialCenterOnBoundary_comp_mutationBoundaryIso_of_horizontal
    (j : Fin 2)
    (hu' : (r u).primitiveGenerator = if j = 0 then v else -v)
    (hm₀ : char u.primitiveGenerator = 0) (hm₁ : char (r u).primitiveGenerator = 0) :
    let p := u.binomialCenterOnBoundary rankTwo hm₀ (ρ.surjective_detCharacter b) d
    let q := (r u).binomialCenterOnBoundary rankTwo hm₁ (ρ.surjective_detCharacter b) d
    p ≫ (a).hom = q := by
  dsimp only
  let : Nonempty Φ.cones := hΦ₀
  let : Nonempty (Ψ).cones := hΨ₀
  let p := u.binomialCenterOnBoundary rankTwo hm₀ (ρ.surjective_detCharacter b) d
  let q := (r u).binomialCenterOnBoundary rankTwo hm₁ (ρ.surjective_detCharacter b) d
  have hp' : (u.boundaryComponentι hΦ).ker ≤ p.ker := by
    dsimp only [p]
    rw [← u.binomialCenterOnComponent_boundaryComponentι hΦ rankTwo hm₀
      (ρ.surjective_detCharacter b) d]
    exact Scheme.Hom.le_ker_comp _ _
  have hq' : ((r u).boundaryComponentι hΨ).ker ≤ q.ker := by
    dsimp only [q]
    rw [← (r u).binomialCenterOnComponent_boundaryComponentι hΨ rankTwo hm₁
      (ρ.surjective_detCharacter b) d]
    exact Scheme.Hom.le_ker_comp _ _
  have htransport : ((r u).boundaryComponentι hΨ).ker ≤ (p ≫ (a).hom).ker := by
    rw [Scheme.Hom.ker_comp, le_map_iff_comap_le,
      ρ.comap_ker_boundaryComponentι_mutationBoundaryIso b hOpp c hΦ u]
    exact hp'
  obtain ⟨B, hB, hcoord⟩ := b.exists_basis_zero_eq_coord_one_eq
    ρ.isPrimitiveGenerator.isPrimitive (b.detDualEquiv_self v) (ρ.surjective_detCharacter b)
  have hpos : hull ℝ {i (B 0)} ∈ (Ψ).cones := by
    rw [hB]
    simpa [← b.detDualEquiv_apply, b.detDualEquiv_self] using
      (Φ.hull_singleton_mem_mutationFan_iff b hv hp hOpp v).mpr hp
  have hneg : hull ℝ {-i (B 0)} ∈ (Ψ).cones := by
    rw [hB, ← map_neg]
    simpa [← b.detDualEquiv_apply, b.detDualEquiv_self] using
      (Φ.hull_singleton_mem_mutationFan_iff b hv hp hOpp (-v)).mpr hOpp
  apply (cancel_mono (D₁).subschemeι).mp
  rw [Category.assoc]
  refine (r u).eq_of_characterRuling_eq_of_le_ker
    (Φ.mutationDetCharacter_nonneg_or_nonpos b hv hp hOpp) B hcoord hpos hneg hΨ j
    (by simpa only [hB] using hu') ?_ ?_
    (projectiveLineTorusPoint ((-1 : ℂˣ) * d⁻¹)) ?_ ?_
  · simpa only [map_ker, Ray.boundaryComponentι_subschemeι, ker_subschemeι, Category.assoc]
      using map_mono (D₁).subschemeι htransport
  · simpa only [map_ker, Ray.boundaryComponentι_subschemeι, ker_subschemeι]
      using map_mono (D₁).subschemeι hq'
  · rw [Category.assoc, Category.assoc (a).hom, mutationBoundaryIso_comp_ruling,
      ← Category.assoc, Ray.binomialCenterOnBoundary_comp_subschemeι,
      Ray.binomialCenter_comp_characterRuling, projectiveLineTorusPoint_comp_projectiveLineTorusι]
    simp
  · rw [Ray.binomialCenterOnBoundary_comp_subschemeι, Ray.binomialCenter_comp_characterRuling,
      projectiveLineTorusPoint_comp_projectiveLineTorusι]
    simp

/-- The boundary isomorphism for an elementary transformation transports every
binomial center to the sheared ray with the mutation parameter. This includes both
horizontal centers on the pivot fiber. -/
theorem Ray.binomialCenterOnBoundary_comp_mutationBoundaryIso :
    center(u, d) ≫ (a).hom = center((r u), δ) := by
  by_cases hpos : u.primitiveGenerator = v
  · have hd : b.det ![u.primitiveGenerator, v] = 0 := by
      rw [← b.detDualEquiv_apply, hpos, b.detDualEquiv_self]
    have hpos' : (r u).primitiveGenerator = v := by
      rw [mutationFanRayEquiv_primitiveGenerator, hd, max_self, zero_smul, add_zero, hpos]
    have he := binomialCenterOnBoundary_comp_mutationBoundaryIso_of_horizontal b ρ hOpp c hΦ u d
      0 (by simpa using hpos')
      (by rw [hpos]; exact b.detDualEquiv_self v)
      (by rw [hpos']; exact b.detDualEquiv_self v)
    simp only [hd, max_self, zpow_zero, mul_one]
    dsimp only at he
    convert he using 2 <;> congr 1 <;> simp only [hpos, hpos']
  by_cases hneg : u.primitiveGenerator = -v
  · have hd : b.det ![u.primitiveGenerator, v] = 0 := by
      rw [← b.detDualEquiv_apply, b.detDualEquiv_swap, hneg, map_neg, b.detDualEquiv_self]
      simp
    have hneg' : (r u).primitiveGenerator = -v := by
      rw [mutationFanRayEquiv_primitiveGenerator, hd, max_self, zero_smul, add_zero, hneg]
    have hm₀ : char u.primitiveGenerator = 0 := by
      rw [hneg, map_neg, LinearMap.toAddMonoidHom_coe, b.detDualEquiv_self, neg_zero]
    have hm₁ : char (r u).primitiveGenerator = 0 := by
      rw [hneg', map_neg, LinearMap.toAddMonoidHom_coe, b.detDualEquiv_self, neg_zero]
    have he := binomialCenterOnBoundary_comp_mutationBoundaryIso_of_horizontal b ρ hOpp c hΦ u d⁻¹
      1 (by simpa using hneg') hm₀ hm₁
    dsimp only at he
    rw [← u.binomialCenterOnBoundary_neg_inv rankTwo hm₀ (ρ.surjective_detCharacter b) d⁻¹,
      ← (r u).binomialCenterOnBoundary_neg_inv rankTwo hm₁ (ρ.surjective_detCharacter b) d⁻¹] at he
    simp only [hd, max_self, zpow_zero, mul_one]
    simp only [inv_inv] at he
    convert he using 2 <;> congr 1 <;> ext x <;> simp [hneg, hneg']
  exact binomialCenterOnBoundary_comp_mutationBoundaryIso_of_avoids_pivot b ρ hOpp c hΦ u d
    (fun h ↦ (hpos h).elim) (fun h ↦ (hneg h).elim)

/-- The ideal of each transported binomial center pulls back to the original
center ideal on the entire strict boundary. -/
theorem Ray.mutationBoundaryIso_transports_internal_centers :
    (((r u).internalCenter (h₀ := hΨ₀) b δ).val).comap (a).hom =
      (u.internalCenter (h₀ := hΦ₀) b d).val := by
  let : Nonempty Φ.cones := hΦ₀
  let : Nonempty (Ψ).cones := hΨ₀
  rw [Ray.internalCenter_val, Ray.internalCenter_val,
    ← ρ.binomialCenterOnBoundary_comp_mutationBoundaryIso b hOpp c hΦ u d,
    Scheme.Hom.comap_ker_comp_of_isClosedImmersion]

end TauCeti.Toric.Fan
