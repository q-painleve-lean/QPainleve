/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Incidence
public import QPainleve.Geometry.Toric.Fan.Mutation.Blowup

import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Reorder
import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Transport
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension
import QPainleve.Geometry.Toric.Fan.Mutation.Boundary
import QPainleve.Geometry.Toric.Fan.Smooth

/-!
# Transport of centers incident to a ray divisor through a mutation

In a resolved elementary link the two initial blowups share an isomorphic
model. The strict transform of a ray divisor corresponds to the strict transform
of the ray carried by the mutation. If the original pivot is moved to the front,
the retained centers on those successive strict transforms are identified in
their original relative order, even above the pivot itself.
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (ρ : Φ.Ray) (b : Basis (Fin 2) ℤ N)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : ℂˣ)
  (hΦ : Φ.IsRegular) (u : Φ.Ray)

local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hOpp) hΦ
local notation "r" => Φ.mutationFanRayEquiv b hv hp hOpp
local notation "I₀" => Ray.mutationSourceCenterIdeal b ρ c
local notation "I₁" => Ray.mutationTargetCenterIdeal b ρ hOpp c
local notation "G" => Ray.mutationBlowupIso b ρ hOpp c
local notation "C₀" => Φ.rayBoundaryIdeal hΦ u
local notation "C₁" => Fan.rayBoundaryIdeal Ψ hΨ (r u)
local notation "X" => Φ.algebraicRealization
local notation "X'" => Fan.algebraicRealization Ψ
local notation "P(" I ")" => BlowupTower.snoc BlowupTower.nil I
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "f" => (X ↘ S)

/-- In an elementary mutation link on a specified point resolution, a retained
center belongs to the successive strict transform of the new ray divisor if
and only if its original center belonged to the corresponding strict transform.
The selected pivot was moved to the front on the source, and the reverse
pivot comes first on the target. The formula includes infinitely near centers. -/
theorem Ray.mem_strictTransformCenterIndices_mutation_iff
    {W Y Z : Scheme} {n : ℕ} {T : BlowupTower X (n + 1) W}
    {U : BlowupTower (I₀).blowup n Y} {U' : BlowupTower (I₁).blowup n Z}
    (hT : IsClosedPointTower X T)
    (h₀ : IsClosedPointTower X (P(I₀))) (h₁ : IsClosedPointTower X' (P(I₁)))
    (hU : IsClosedPointTower (I₀).blowup U) (hU' : IsClosedPointTower (I₁).blowup U')
    (j : Fin (n + 1)) (e : W ≅ Y) (g : Y ≅ Z) (hg : IsLift (G) U U' g)
    (he : e.hom ≫ U.toBase ≫ (I₀).blowupToBase = T.toBase)
    (hE : pullback e.hom (pullback U.toBase (I₀).blowupExceptionalClass) = T.exceptionalClass j)
    (hTail : ∀ l, pullback e.hom (U.exceptionalClass l) = T.exceptionalClass (j.succAbove l))
    (l : Fin n) :
    l.natAdd 1 ∈ (h₁.append hU').strictTransformCenterIndices (C₁) ↔
      j.succAbove l ∈ hT.strictTransformCenterIndices (C₀) := by
  let : Nonempty Φ.cones := ⟨ρ.toCone⟩
  let : SmoothOfRelativeDimension 2 f := by
    rw [Fan.algebraicRealization_over]
    exact ((finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
      Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  let : IsNoetherian X := isNoetherian_of_finiteType f
  let : TauCeti.AlgebraicGeometry.IsRegular (C₀).subscheme := Φ.isRegular_rayBoundary hΦ u
  have hdim : topologicalKrullDim (C₀).subscheme = 1 := by
    rw [Φ.rayBoundaryIdeal_def hΦ u]
    exact QPainleve.topologicalKrullDim_vanishingIdeal_subscheme ℂ
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)) _
  have h := hT.strictTransformCoefficients_tail_move_to_front f h₀ hU e j he hE hTail
    (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ u) hdim
  have hsection := hg.strictTransformCoefficients_eq hU hU'
    ((I₁).blowupMap (C₁).subschemeι).ker
  rw [ρ.comap_strictRayBoundary_mutationBlowupIso b hOpp c hΦ u, h] at hsection
  have happend := IsClosedPointTower.strictTransformCoefficients_append_natAdd h₁ hU' (C₁) l
  rw [strictTransform_snoc, strictTransform_nil] at happend
  rw [IsClosedPointTower.mem_strictTransformCenterIndices,
    IsClosedPointTower.mem_strictTransformCenterIndices, happend, ← hsection, Function.comp_apply]

end TauCeti.Toric.Fan
