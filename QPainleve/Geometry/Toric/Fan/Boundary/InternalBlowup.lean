/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import TauCeti.AlgebraicGeometry.Curves.Node.Relative

import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Basic
import QPainleve.Geometry.Toric.Fan.Boundary.Node

/-!
# The strict boundary of ordered internal blowups

The toric boundary remains a nodal effective Cartier divisor after blowing up an
ordered sequence of smooth centers on its strict transform. This includes
sequences with repeated centers.
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

universe u

variable (k : Type u) [Field k] {N V : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  (b : Basis (Fin 2) ℤ N) {r : ℕ} (s : Fin r → Φ.Ray) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "S" => Spec (CommRingCat.of k)
local notation "Z" => (Φ.finiteFanScheme k)
local notation "D" => Φ.toricBoundaryIdeal k inferInstance
local notation "model[" c "]" => internalBlowupTower k b s c
local notation "T[" c "]" => WithBoundary.toTower (Sigma.snd (model[c]))
local notation "B[" c "]" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd (model[c])))
local notation "hT[" c "]" => isClosedPointTower_internalBlowupTower k b s c
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)

include hΦ in
/-- If the boundary of a regular toric surface is effective Cartier, its strict
transform in an ordered internal blowup is effective Cartier. The parameters can
include repeated centers. -/
theorem isEffectiveCartier_internalBlowupBoundary [PerfectField k] (c : Fin r → kˣ)
    (hD : (D).IsEffectiveCartier) : (B[c]).IsEffectiveCartier := by
  let : SmoothOfRelativeDimension 2 (Z ↘ S) :=
    (finiteFanScheme_over k Φ).symm ▸
      (rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ)
  let J (j : Fin r) := (s j).internalCenter k b (c j)
  have h := strictTransform_ker_comp_alongBoundary (D).subschemeι (𝟙 (D).subscheme) J
    (fun j ↦ by simpa only [comap_id] using (J j).property)
  simp only [Category.id_comp, ker_subschemeι] at h
  rw [← internalBlowupTower_eq_alongBoundary k b s c] at h
  exact h ▸ (hT[c]).isEffectiveCartier_strictTransform (Z ↘ S) hD

include hΦ hc in
/-- The strict boundary in the ordered internal model is nodal since its
closed immersion has the original toric boundary as its domain. -/
theorem atWorstNodalOfRelativeDimensionOne_internalBlowupBoundary (c : Fin r → kˣ) :
    AtWorstNodalOfRelativeDimensionOne ((B[c]).subschemeι ≫ (T[c]).toBase ≫ Z ↘ S) := by
  let j := (model[c]).2.boundaryι
  have hj : j ≫ (T[c]).toBase ≫ Z ↘ S =
      (D).subschemeι ≫ Φ.finiteFanSchemeToSpec k := by
    rw [← finiteFanScheme_over k]
    exact (model[c]).2.boundaryι_toBase_assoc _
  let e := asIso j.toImage
  apply (MorphismProperty.cancel_left_of_respectsIso
    (P := @AtWorstNodalOfRelativeDimensionOne) e.hom _).mp
  have he : e.hom ≫ (B[c]).subschemeι = j := Scheme.Hom.toImage_imageι j
  rw [← Category.assoc, he, hj]
  exact Φ.atWorstNodalOfRelativeDimensionOne_boundary k hΦ hc rankTwo

end TauCeti.Toric.Fan
