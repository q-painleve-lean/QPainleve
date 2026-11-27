/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Basic

import QPainleve.Geometry.Toric.Fan.Logarithmic.InternalBlowup

/-!
# Ordered logarithmic models of internal blowups

An ordered tower of internal blowups defines a logarithmic projection with the
original binomial parameters and exchange matrix. This keeps the full fixed-center
evaluation when the tower is used as an endpoint in a resolved factorization,
as in [Lutz, Theorem 8.4](https://arxiv.org/pdf/2005.05010v3#page=68).
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative
open QPainleve.BlowupTower TauCeti TauCeti.AlgebraicGeometry
open QPainleve.CharacterTorus (centerCharacter_of_pi_single)
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (hc : Φ.IsComplete) (hΦ : Φ.IsRegular)
  (b : Module.Basis (Fin 2) ℤ N) {m : ℕ} (r : Fin m → Φ.Ray)
  (c : Multiplicative (Fin m → ℤ) →* k₀ˣ)

local notation "S" => Spec (CommRingCat.of k₀)
local notation "c₀" => fun j : Fin m ↦ c (ofAdd (Pi.single j 1))
local notation "M" => internalBlowupTower k₀ (h₀ := hc.nonempty_cones) b r c₀
local notation "π" => toBase (WithBoundary.toTower (Sigma.snd M))

open LogarithmicProjection

/-- An identification with the top of an ordered internal tower gives an ordered
logarithmic model of the specified blowdown. It has the original exchange matrix,
and evaluates the center-scaled torus characters along that blowdown. -/
theorem exists_orderedToricModel_of_internalBlowupTower
    {Z : Scheme} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)] [IsIntegral Z]
    {D : Z.IdealSheafData} (e : Z ≅ (M).1)
    (he : e.hom ≫ π ≫ (Φ.finiteFanSchemeToSpec k₀) = Z ↘ S)
    (hD : D.support = ((M).2.boundaryι.ker.comap e.hom).support) :
    letI : Nonempty Φ.cones := hc.nonempty_cones
    letI : IsModification π := isModification_internalBlowupTower_toBase k₀ b r c₀ hΦ
    ∃ (A : LogarithmicProjection k₀ i D.radical) (U : OrderedToricModel A m),
      A.fan = Φ ∧ A.hom ≍ e.hom ≫ π ∧ IsModification A.hom ∧
      U.exchangeMatrix.matrix = QPainleve.Cluster.chargeExchangeMatrix
        b.detDualEquiv.toLinearMap (rayChargeMap r) ∧
      U.xEvaluation = (e.hom ≫ π).toRationalMap.comp (Φ.xEvaluation k₀ b r c) := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  have hD' := radical_eq_comap_internalBlowupBoundary_of_support_eq k₀ b r c₀ e hD
  obtain ⟨A, hf, hA, hmod⟩ := exists_internalBlowupLogarithmicProjection k₀ b r c₀ hΦ hc e he hD
  -- The blowdown has the original fan, so its ordered model uses the identity subdivision.
  cases hf
  have hhom := eq_of_heq hA
  have hP := congrArg (fun I : Z.IdealSheafData ↦ I.comap e.inv) hD'
  simp only [← comap_comp, Iso.inv_hom_id, comap_id] at hP
  let U : OrderedToricModel A m :=
    ⟨A.fan, hΦ, IsSubdivision.refl A.fan, b, r, c₀, e.symm,
      by rw [hhom, Iso.symm_hom, Iso.inv_hom_id_assoc, IsSubdivision.toFanHom_refl,
        FanHom.finiteFanSchemeHom_id, Category.comp_id],
      hP⟩
  refine ⟨A, U, rfl, hA, hmod, U.exchangeMatrix_matrix, ?_⟩
  have hf : U.hom = e.hom ≫ (U.tower).2.toTower.toBase := U.hom_def
  simp only [U.xEvaluation_def, U, centerCharacter_of_pi_single]
  congr 1
  exact congrArg Scheme.Hom.toRationalMap hf

end TauCeti.Toric.Fan
