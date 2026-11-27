/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.RationalMap
public import QPainleve.AlgebraicGeometry.RationalMap.Composition.Defined
public import QPainleve.Geometry.Toric.Fan.Evaluation
public import QPainleve.Geometry.Toric.Fan.ExchangeMatrix
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Presentation

/-!
# X evaluations of ordered toric models

The ordered rays and lattice frame determine the exchange matrix. The center
parameters scale the torus characters before pullback to the resolving surface.
-/

public noncomputable section

open AlgebraicGeometry Module
open QPainleve.Cluster TauCeti TauCeti.AlgebraicGeometry
open QPainleve.CharacterTorus (centerCharacter)

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {K : Type} [Field K]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

variable {Z : Scheme} [Z.Over (Spec (.of K))]
  [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of K))] [IsIntegral Z]
  {D : Z.IdealSheafData} {A B : LogarithmicProjection K i D} {m : ℕ}

namespace OrderedToricModel

/-- The exchange matrix determined by the rays and oriented lattice frame of an ordered model. -/
@[expose]
def exchangeMatrix (U : OrderedToricModel A m) : SkewExchangeMatrix (Fin m) :=
  rayExchangeMatrix U.basis U.rays

omit [IsIntegral Z] in
/-- The underlying matrix is the determinant pairing of the ordered ray charges. -/
@[simp]
theorem exchangeMatrix_matrix (U : OrderedToricModel A m) :
    U.exchangeMatrix.matrix =
      chargeExchangeMatrix U.basis.detDualEquiv.toLinearMap (rayChargeMap U.rays) :=
  rayExchangeMatrix_matrix _ _

/-- The fixed-center rational evaluation on the common resolving surface. -/
def xEvaluation (U : OrderedToricModel A m) :
    Z ⤏ Spec (.of (LaurentRing K (Fin m))) :=
  U.hom.toRationalMap.comp (U.fan.xEvaluation K U.basis U.rays (centerCharacter U.parameters))

/-- Evaluation pulls the scaled torus characters back along the ordered projection. -/
theorem xEvaluation_def (U : OrderedToricModel A m) :
    U.xEvaluation =
      U.hom.toRationalMap.comp
        (U.fan.xEvaluation K U.basis U.rays (centerCharacter U.parameters)) :=
  (rfl)

/-- Successive words carrying one fixed-center evaluation to the next compose
at the generic point of the same resolving surface. -/
theorem exists_compOfDefined_word_comp {C : LogarithmicProjection K i D}
    (U : OrderedToricModel A m) (M : OrderedToricModel B m) (W : OrderedToricModel C m)
    (u : Word U.exchangeMatrix M.exchangeMatrix) (v : Word M.exchangeMatrix W.exchangeMatrix)
    (h₀ : ∃ h, U.xEvaluation.compOfDefined (u.xRationalMap K) h = M.xEvaluation)
    (h₁ : ∃ h, M.xEvaluation.compOfDefined (v.xRationalMap K) h = W.xEvaluation) :
    ∃ h, U.xEvaluation.compOfDefined ((u.comp v).xRationalMap K) h = W.xEvaluation := by
  obtain ⟨hu, h₀⟩ := h₀
  obtain ⟨hv, h₁⟩ := h₁
  obtain ⟨h, he⟩ := U.xEvaluation.compOfDefined_comp (u.xRationalMap K) (v.xRationalMap K)
    hu (h₀.symm ▸ hv)
  refine ⟨(Quiver.Path.xRationalMap_comp K u v).symm ▸ h, ?_⟩
  simpa only [Quiver.Path.xRationalMap_comp, ← he, h₀] using h₁

end OrderedToricModel

end TauCeti.Toric.Fan.LogarithmicProjection
