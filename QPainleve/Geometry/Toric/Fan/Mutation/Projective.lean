/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Mutation.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.Geometry.Toric.Algebraic.Fan.Over

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Blowup.Point.Projective
import QPainleve.AlgebraicGeometry.Blowup.Projective.Global
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Mutation.Blowup
import QPainleve.Geometry.Toric.Fan.Smooth
import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# Projectivity of a toric elementary transformation

The two pivot blowups are isomorphic over the field. If the source is
projective, so is its point blowup, and contracting the reverse pivot preserves
projectivity by `Scheme.IsProjectiveOver.of_pointBlowup`.
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (ρ : Φ.Ray)
  (b : Basis (Fin 2) ℤ N) (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "X" => Φ.algebraicRealization
local notation "X'" => Fan.algebraicRealization Ψ

/-- A toric elementary transformation of a projective regular toric surface
has projective target. -/
theorem Ray.isProjectiveOver_mutationFan [Φ.algebraicRealization.IsProjectiveOver ℂ]
    (hΦ : Φ.IsRegular) :
    let : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hp hOpp ρ.toCone⟩
    (X').IsProjectiveOver ℂ := by
  intro hcones
  let := hcones
  let I := ρ.mutationSourceCenterIdeal b (1 : ℂˣ)
  let J := ρ.mutationTargetCenterIdeal b hOpp (1 : ℂˣ)
  let a := ρ.mutationBlowupIso b hOpp (1 : ℂˣ)
  let : I.blowup.Over S := ⟨I.blowupToBase ≫ (X ↘ S)⟩
  let : J.blowup.Over S := ⟨J.blowupToBase ≫ (X' ↘ S)⟩
  let : I.blowup.IsProjectiveOver ℂ := I.isProjectiveOver_blowup_of_isNoetherianRing ℂ
  have ha : a.hom ≫ J.blowupToBase ≫ (X' ↘ S) = I.blowupToBase ≫ (X ↘ S) :=
    ρ.mutationBlowupIso_hom_comp_toBase b hOpp (1 : ℂˣ)
  have : a.hom.IsOver S := ⟨ha⟩
  have hJ : J.blowup.IsProjectiveOver ℂ := Scheme.IsProjectiveOver.of_isClosedImmersion ℂ a.inv
  let τ := Φ.mutationFanCenterRays b (fun _ : Unit ↦ ρ) () hOpp ()
  have hdim : finrank ℤ N = 2 := (finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let p := τ.binomialCenter hdim (b.detDualEquiv_self τ.primitiveGenerator)
    (τ.surjective_detCharacter b) (1 : ℂˣ)⁻¹
  have hpClosed : IsClosed ({p (IsLocalRing.closedPoint ℂ)} : Set X') :=
    isClosed_singleton_of_section (τ.binomialCenter_comp_structureMap hdim
      (b.detDualEquiv_self τ.primitiveGenerator) (τ.surjective_detCharacter b) (1 : ℂˣ)⁻¹)
  have hJp : J = ((X').fromSpecResidueField (p (IsLocalRing.closedPoint ℂ))).ker :=
    (ρ.mutationTargetCenterIdeal_eq b hOpp (1 : ℂˣ)).trans p.ker_eq_ker_fromSpecResidueField
  let : SmoothOfRelativeDimension 2 (X' ↘ S) :=
    hdim ▸ (Ψ).smoothOfRelativeDimension_algebraicRealizationStructureMap
      ((Φ.isRegular_mutationFan_iff b hv hp hOpp).mpr hΦ)
  apply Scheme.IsProjectiveOver.of_pointBlowup _ hpClosed
  exact (congrArg (fun K : (X').IdealSheafData ↦
    let : K.blowup.Over S := ⟨K.blowupToBase ≫ (X' ↘ S)⟩
    K.blowup.IsProjectiveOver ℂ) hJp).mp hJ

end TauCeti.Toric.Fan
