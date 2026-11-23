/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
public import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter

import QPainleve.Geometry.Toric.Fan.Smooth

/-!
# Ordered internal blowups of a toric surface

An oriented rank-two fan and an ordered list of rays with nonzero center parameters determine
an actual tower of point blowups. Each center is placed on the current strict transform of the
reduced toric boundary. The same ray and parameter can occur repeatedly, giving centers that
are infinitely near. The Picard marking uses full transforms of the exceptional classes.

The models follow Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
Definition 1.2. The construction uses `Ray.binomialCenterOnBoundary` and
`QPainleve.BlowupTower.alongBoundary`.
-/

public noncomputable section

open AlgebraicGeometry QPainleve.BlowupTower TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

variable [h₀ : Nonempty Φ.cones] (b : Module.Basis (Fin 2) ℤ N)

local notation "boundary" => Φ.boundaryIdeal h₀
local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))

variable {n : ℕ} (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ)

/-- The ordered internal blowups with the indicated boundary rays and parameters.
At each stage the center is the image of the original binomial point in the current boundary. -/
def internalBlowupTower : Σ Y, WithBoundary (boundary).subschemeι n Y :=
  alongBoundary (boundary).subschemeι fun j ↦ (s j).internalCenter b (c j)

/-- The empty list of internal centers leaves the toric model unchanged. -/
@[simp]
theorem internalBlowupTower_zero (s : Fin 0 → Φ.Ray) (c : Fin 0 → ℂˣ) :
    internalBlowupTower b s c = ⟨Φ.algebraicRealization, .nil (boundary).subschemeι⟩ :=
  alongBoundary_zero _ _

/-- The last center is mapped into the model already blown up at the preceding centers. -/
@[simp]
theorem internalBlowupTower_succ (s : Fin (n + 1) → Φ.Ray) (c : Fin (n + 1) → ℂˣ) :
    internalBlowupTower b s c =
      let P := internalBlowupTower b (s ∘ Fin.castSucc) (c ∘ Fin.castSucc)
      let J := (s (Fin.last n)).internalCenter b (c (Fin.last n))
      ⟨_, P.2.snoc J.val J.property⟩ :=
  alongBoundary_succ _ _

/-- All internal centers are reduced closed points of their successive ambient surfaces. -/
theorem isClosedPointTower_internalBlowupTower :
    IsClosedPointTower Φ.algebraicRealization (internalBlowupTower b s c).2.toTower := by
  apply isClosedPointTower_alongBoundary
  intro j
  rw [Ray.internalCenter_val]
  exact (s j).exists_closedPoint_ker_binomialCenterOnBoundary rankTwo (b.detDualEquiv_self _)
    ((s j).surjective_detCharacter b) (c j)

/-- The Picard group of the model is marked by the original toric classes and the full
transforms of the exceptional classes, with coordinates in the given center order. -/
def internalBlowupPicardMarking (hΦ : Φ.IsRegular) :
    (Pic(Φ.algebraicRealization) × (Fin n → ℤ)) ≃ₗ[ℤ]
      Pic((internalBlowupTower b s c).1) := by
  have : SmoothOfRelativeDimension 2 Φ.algebraicRealizationStructureMap :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  exact (internalBlowupTower b s c).2.toTower.picardMarking
    (isClosedPointTower_internalBlowupTower b s c) Φ.algebraicRealizationStructureMap

/-- The marking pulls back the toric class and adds the indicated total exceptional classes. -/
@[simp]
theorem internalBlowupPicardMarking_apply (hΦ : Φ.IsRegular)
    (a : Pic(Φ.algebraicRealization) × (Fin n → ℤ)) :
    internalBlowupPicardMarking b s c hΦ a = (internalBlowupTower b s c).2.toTower.picardHom a := by
  simp [internalBlowupPicardMarking]

end TauCeti.Toric.Fan
