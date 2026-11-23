/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Component
public import QPainleve.Geometry.Toric.Fan.Mutation.Blowup

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.Geometry.Toric.Fan.Boundary.StrictTransform
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.Geometry.Toric.Fan.Mutation.Valuation

/-!
# The strict boundary under toric mutation

The elementary transformation induces an isomorphism of the strict boundary curves
and carries each ray component to the component indexed by the sheared ray.
The strict boundaries are identified with the original reduced toric boundaries.

See Gross, Hacking and Keel, [*Birational geometry of cluster algebras*,
§3.1](https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : ℂˣ)
  (hΦ : Φ.IsRegular)

local notation "v" => Ray.primitiveGenerator ρ
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hOpp) hΦ
local notation "r" => Φ.mutationFanRayEquiv b hv hp hOpp
local notation "I₀" => Ray.mutationSourceCenterIdeal b ρ c
local notation "I₁" => Ray.mutationTargetCenterIdeal b ρ hOpp c
local notation "G" => Ray.mutationBlowupIso b ρ hOpp c
local notation "h₀" => Φ.detCharacter_nonneg_or_nonpos b hv hp hOpp
local notation "h₁" => Φ.mutationDetCharacter_nonneg_or_nonpos b hv hp hOpp
local notation "U₀" => Φ.mutationComplement b h₀ (c : ℂ)
local notation "U₁" => mutationComplement Ψ b h₁ (c : ℂ)
local notation "eC" => Φ.mutationComplementIso b (c : ℂ) hv hp hOpp

/-- The strict transform of each ray divisor pulls back to the strict transform of
the corresponding original ray divisor under the global pivot blowup isomorphism. -/
theorem Ray.comap_strictRayBoundary_mutationBlowupIso (u : Φ.Ray) :
    ((I₁).blowupMap ((Ψ).rayBoundaryIdeal (hΨ) ((r) u)).subschemeι).ker.comap (G).hom =
      ((I₀).blowupMap (Φ.rayBoundaryIdeal hΦ u).subschemeι).ker := by
  let x : (U₀).toScheme :=
    ⟨(Φ.rayBoundaryPoint hΦ u).val,
      Φ.rayBoundaryPoint_mem_mutationComplement b c hv h₀ hΦ u⟩
  let y := (eC).hom x
  let hI₀ := ρ.mutationSourceCenterIdeal_comap_complement b hOpp c
  let hI₁ := ρ.mutationTargetCenterIdeal_comap_complement b hOpp c
  let l₀ := (I₀).blowupLift (U₀).ι (hI₀.symm ▸ isEffectiveCartier_top _)
  let l₁ := (I₁).blowupLift (U₁).ι (hI₁.symm ▸ isEffectiveCartier_top _)
  have outsideExceptional {X U : Scheme} (I : X.IdealSheafData) (j : U ⟶ X)
      (h : I.comap j = ⊤) (z : U) :
      I.blowupLift j (h.symm ▸ isEffectiveCartier_top _) z ∉
        ((I.comap I.blowupToBase).support : Set I.blowup) := by
    have he := (I.comap I.blowupToBase).comap_eq_top_iff
      (I.blowupLift j (h.symm ▸ isEffectiveCartier_top _))
    rw [comap_blowupLift_exceptional] at he
    exact (Scheme.Hom.mem_preimage _).mp (by rw [he.mp h]; trivial)
  have hx : (I₀).blowupToBase (l₀ x) = (Φ.rayBoundaryPoint hΦ u).val := by
    rw [← Scheme.Hom.comp_apply, blowupLift_blowupToBase, Scheme.Opens.ι_apply]
  have hy : (I₁).blowupToBase (l₁ y) = ((Ψ).rayBoundaryPoint (hΨ) ((r) u)).val := by
    rw [← Scheme.Hom.comp_apply, blowupLift_blowupToBase]
    exact Φ.mutationComplementIso_hom_rayBoundaryPoint b c hv hp hOpp hΦ u
  have hl : (G).hom (l₀ x) = l₁ y := by
    rw [← Scheme.Hom.comp_apply, ρ.mutationComplementBlowupι_comp_mutationBlowupIso_hom,
      Scheme.Hom.comp_apply]
  rw [rayBoundaryIdeal_def, rayBoundaryIdeal_def, ← hx, ← hy,
    ker_blowupMap_vanishingIdeal_closure_singleton _ _ (outsideExceptional _ _ hI₀ x),
    ker_blowupMap_vanishingIdeal_closure_singleton _ _ (outsideExceptional _ _ hI₁ y),
    ← hl, comap_vanishingIdeal_closure_singleton_apply]

local notation "hΦ₀" => Nonempty.intro (Ray.toCone Φ ρ)
local notation "hΨ₀" => Nonempty.intro (Φ.mutationFanConeEquiv b hv hp hOpp (Subtype.mk _ hp))
local notation "D₀" => Φ.boundaryIdeal hΦ₀
local notation "D₁" => boundaryIdeal (Ψ) hΨ₀
local notation "j₀" => Ray.mutationSourceBoundaryι b ρ c
local notation "j₁" => Ray.mutationTargetBoundaryι b ρ hOpp c

include hΦ in
private theorem ker_mutationSourceBoundaryι_comp :
    ((j₀) ≫ (G).hom).ker = (j₁).ker := by
  have h := ρ.comap_strictBoundary_mutationBlowupIso b hOpp c hΦ
  rw [← Ray.ker_mutationSourceBoundaryι, ← Ray.ker_mutationTargetBoundaryι] at h
  rw [Scheme.Hom.ker_comp, ← h, map_comap_of_isClosedImmersion]
  simp

include hΦ in
/-- The isomorphism of the fixed reduced boundaries induced by the global pivot blowup
isomorphism. -/
def Ray.mutationBoundaryIso : (D₀).subscheme ≅ (D₁).subscheme := by
  have h := ker_mutationSourceBoundaryι_comp b ρ hOpp c hΦ
  let f := IsClosedImmersion.lift (j₁) ((j₀) ≫ (G).hom) h.ge
  letI : IsIso f := IsClosedImmersion.isIso_lift _ _ h.symm
  exact asIso f

/-- The boundary isomorphism agrees with the global elementary transformation on the
embedded strict boundaries. -/
@[reassoc (attr := simp)]
theorem Ray.mutationBoundaryIso_hom_comp_boundaryι :
    (ρ.mutationBoundaryIso b hOpp c hΦ).hom ≫ (j₁) = (j₀) ≫ (G).hom :=
  IsClosedImmersion.lift_fac _ _ _

instance Ray.isOver_mutationBoundaryIso_hom :
    (ρ.mutationBoundaryIso b hOpp c hΦ).hom.IsOver (Spec (.of ℂ)) := by
  constructor
  rw [over_eq_subschemeι_comp, over_eq_subschemeι_comp, Fan.algebraicRealization_over,
    Fan.algebraicRealization_over,
    ← ρ.mutationTargetBoundaryι_blowupToBase_assoc b hOpp c,
    ρ.mutationBoundaryIso_hom_comp_boundaryι_assoc,
    ρ.mutationBlowupIso_hom_comp_toBase, ρ.mutationSourceBoundaryι_blowupToBase_assoc]

/-- The boundary isomorphism pulls the closed subscheme of a sheared ray back to
the closed subscheme of the original ray. -/
theorem Ray.comap_ker_boundaryComponentι_mutationBoundaryIso (u : Φ.Ray) :
    letI : Nonempty Φ.cones := hΦ₀
    letI : Nonempty (Ψ).cones := hΨ₀
    ((r u).boundaryComponentι (hΨ)).ker.comap (ρ.mutationBoundaryIso b hOpp c hΦ).hom =
      (u.boundaryComponentι hΦ).ker := by
  let : Nonempty Φ.cones := hΦ₀
  let : Nonempty (Ψ).cones := hΨ₀
  have hI₀ : (I₀) = (ρ.internalCenter b c).val.map (D₀).subschemeι := by
    rw [Ray.mutationSourceCenterIdeal_eq, Ray.map_internalCenter_subschemeι]
  let w := Φ.mutationFanCenterRays b (fun _ : Unit ↦ ρ) () hOpp ()
  have hI₁ : (I₁) = (w.internalCenter b c⁻¹).val.map (D₁).subschemeι := by
    rw [Ray.mutationTargetCenterIdeal_eq, Ray.map_internalCenter_subschemeι]
  have h := ρ.comap_strictRayBoundary_mutationBlowupIso b hOpp c hΦ u
  rw [← ker_comp_boundaryι_eq_blowupMap b hΦ ρ u c (I₀) hI₀ (j₀)
    (ρ.mutationSourceBoundaryι_blowupToBase b c),
    ← ker_comp_boundaryι_eq_blowupMap b (hΨ) w (r u) c⁻¹ (I₁) hI₁ (j₁)
      (ρ.mutationTargetBoundaryι_blowupToBase b hOpp c)] at h
  have hc := congrArg (fun J ↦ J.comap (j₀)) h
  rw [← comap_comp, ← ρ.mutationBoundaryIso_hom_comp_boundaryι b hOpp c hΦ,
    comap_comp] at hc
  simpa only [Scheme.Hom.comap_ker_comp_of_isClosedImmersion] using hc

end TauCeti.Toric.Fan
