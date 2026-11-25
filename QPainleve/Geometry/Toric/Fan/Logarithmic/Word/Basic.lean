/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.RationalMap
public import QPainleve.AlgebraicGeometry.RationalMap.Composition.Defined
public import QPainleve.Geometry.Toric.Fan.Evaluation
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Presentation
public import TauCeti.Algebra.Group.FreeAbelianCharacter

/-!
# X evaluations of ordered toric models

The ordered rays and lattice frame determine the exchange matrix. The center
parameters scale the torus characters before pullback to the resolving surface.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module Multiplicative
open QPainleve.CharacterTorus QPainleve.Cluster TauCeti TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)

variable {Z : Scheme} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)] [IsIntegral Z]
  {D : Z.IdealSheafData} {A B : LogarithmicProjection i D} {m : ℕ}

/-- Evaluate an exponent vector at the ordered tuple of nonzero center parameters. -/
abbrev centerCharacter (c : Fin m → ℂˣ) : Multiplicative (Fin m → ℤ) →* ℂˣ :=
  freeAbelianCharEquiv.symm c |>.comp
    ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin m)).symm.toAddEquiv.toMultiplicative.toMonoidHom)

/-- The basis values of a center character recover it on the full exponent lattice. -/
@[simp]
theorem centerCharacter_of_pi_single (c : Multiplicative (Fin m → ℤ) →* ℂˣ) :
    centerCharacter (fun j ↦ c (ofAdd (Pi.single j 1))) = c := by
  let e := (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin m)).toAddEquiv.toMultiplicative
  apply (MonoidHom.cancel_right (f := e.toMonoidHom) e.surjective).mp
  apply freeAbelianCharEquiv.injective
  funext j
  simp [e, centerCharacter, freeAbelianCharEquiv_apply, Finsupp.linearEquivFunOnFinite_single]

/-- The point of the center torus over `Spec ℂ` with the given ordered parameters. -/
abbrev centerPoint (c : Fin m → ℂˣ) : Over.mk (𝟙 S) ⟶ Over.mk (structureMap ℂ (Fin m → ℤ)) :=
  let z := (pointsEquiv ℂ (Fin m → ℤ)).symm (centerCharacter c)
  Over.homMk z.val z.property

/-- Evaluating the character of `centerPoint` on the coordinate basis recovers its parameters. -/
theorem centerPoint_parameters (c : Fin m → ℂˣ) :
    (fun j ↦ pointsEquiv ℂ (Fin m → ℤ) ⟨(centerPoint c).left, Over.w (centerPoint c)⟩
      (ofAdd (Pi.single j 1))) = c := by
  funext j
  simp [centerCharacter, Finsupp.linearEquivFunOnFinite_symm_single]

namespace OrderedToricModel

/-- The exchange matrix determined by the rays and oriented lattice frame of an ordered model. -/
@[expose]
def exchangeMatrix (U : OrderedToricModel A m) : SkewExchangeMatrix (Fin m) :=
  .ofMatrix (chargeExchangeMatrix U.basis.detDualEquiv.toLinearMap (rayChargeMap U.rays))
    (isSkewSymmetrizer_chargeExchangeMatrix _ (U.basis.detDualEquiv_self) _)

omit [IsIntegral Z] in
/-- The underlying matrix is the determinant pairing of the ordered ray charges. -/
@[simp]
theorem exchangeMatrix_matrix (U : OrderedToricModel A m) :
    U.exchangeMatrix.matrix =
      chargeExchangeMatrix U.basis.detDualEquiv.toLinearMap (rayChargeMap U.rays) :=
  SkewExchangeMatrix.matrix_ofMatrix _ _

/-- The fixed-center rational evaluation on the common resolving surface. -/
def xEvaluation (U : OrderedToricModel A m) :
    Z ⤏ Spec (.of (LaurentRing ℂ (Fin m))) :=
  U.hom.toRationalMap.comp (U.fan.xEvaluation U.basis U.rays (centerCharacter U.parameters))

/-- Evaluation pulls the scaled torus characters back along the ordered projection. -/
theorem xEvaluation_def (U : OrderedToricModel A m) :
    U.xEvaluation =
      U.hom.toRationalMap.comp (U.fan.xEvaluation U.basis U.rays (centerCharacter U.parameters)) :=
  (rfl)

/-- Successive words carrying one fixed-center evaluation to the next compose
at the generic point of the same resolving surface. -/
theorem exists_compOfDefined_word_comp {C : LogarithmicProjection i D}
    (U : OrderedToricModel A m) (M : OrderedToricModel B m) (W : OrderedToricModel C m)
    (u : Word U.exchangeMatrix M.exchangeMatrix) (v : Word M.exchangeMatrix W.exchangeMatrix)
    (h₀ : ∃ h, U.xEvaluation.compOfDefined (u.xRationalMap ℂ) h = M.xEvaluation)
    (h₁ : ∃ h, M.xEvaluation.compOfDefined (v.xRationalMap ℂ) h = W.xEvaluation) :
    ∃ h, U.xEvaluation.compOfDefined ((u.comp v).xRationalMap ℂ) h = W.xEvaluation := by
  obtain ⟨hu, h₀⟩ := h₀
  obtain ⟨hv, h₁⟩ := h₁
  obtain ⟨h, he⟩ := U.xEvaluation.compOfDefined_comp (u.xRationalMap ℂ) (v.xRationalMap ℂ)
    hu (h₀.symm ▸ hv)
  refine ⟨(Quiver.Path.xRationalMap_comp ℂ u v).symm ▸ h, ?_⟩
  simpa only [Quiver.Path.xRationalMap_comp, ← he, h₀] using h₁

end OrderedToricModel

end TauCeti.Toric.Fan.LogarithmicProjection
