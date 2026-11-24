/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Basic

import QPainleve.Geometry.Toric.Fan.Logarithmic.OrderedStarPath

/-!
# The cluster word of a resolved toric star path

In a block of toric blowups and blowdowns in the resolved factorization of
[Lutz, Theorem 8.4](https://arxiv.org/pdf/2005.05010v3#page=68), the regular projections
all use one ordered internal model. The toric changes preserve the fixed-center
evaluation of that model on the common dense torus. They therefore contribute the
empty word, with the same ordered marking on both ends.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open QPainleve.Cluster QPainleve.BlowupTower TauCeti TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)
local notation "base[" T "]" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd T))

variable {Z : Scheme} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)] [IsIntegral Z]
  {D : Z.IdealSheafData} {A B : LogarithmicProjection i D} {m : ℕ}

private theorem comp_xEvaluation_denseTorusPartialIso (U : OrderedToricModel A m) :
    A.hom.toRationalMap.comp ((A.fan.denseTorusPartialIso U.fan).toRationalMap.comp
      (U.fan.xEvaluation U.basis U.rays (centerCharacter U.parameters))) =
    U.xEvaluation := by
  have h := U.subdivision.comp_denseTorusPartialIso (.refl U.fan) U.hom
  simp only [U.hom_comp_subdivision, IsSubdivision.toFanHom_refl, FanHom.algebraicMap_id,
    Category.comp_id] at h
  simp only [OrderedToricModel.xEvaluation_def, ← Scheme.RationalMap.comp_assoc, h]

/-- A resolved toric star path transports a supplied ordered internal model to its
specified endpoint, using the same fan, tower and resolving isomorphism. The
rational evaluations on the endpoint fans are read using their common dense torus.
The path commutes with the two subdivisions and intertwines these evaluations.
On the resolving surface the empty cluster word is defined at the generic value
and gives the terminal evaluation. -/
theorem exists_word_of_resolved_star_path [Z.IsProjectiveOver ℂ]
    (p : Quiver.Path A B) (U : OrderedToricModel A m) :
    ∃ (K : U.fan.IsSubdivision B.fan) (hK : U.iso.hom ≫ B.hom = base[U.tower] ≫ π[K]),
      let W : OrderedToricModel B m :=
        ⟨U.fan, U.regular, K, U.basis, U.rays, U.parameters, U.iso, hK, U.pole_eq⟩
      let x := U.fan.xEvaluation U.basis U.rays (centerCharacter U.parameters)
      let x' := W.fan.xEvaluation W.basis W.rays (centerCharacter W.parameters)
      let xA := (A.fan.denseTorusPartialIso U.fan).toRationalMap.comp x
      let xB := (B.fan.denseTorusPartialIso W.fan).toRationalMap.comp x'
      let w : Word U.exchangeMatrix W.exchangeMatrix := Quiver.Path.nil
      π[U.subdivision].toRationalMap.comp (pathRationalMap p) =
          π[W.subdivision].toRationalMap ∧
        (pathRationalMap p).comp xB = xA ∧
        A.hom.toRationalMap.comp xA = U.xEvaluation ∧
        B.hom.toRationalMap.comp xB = W.xEvaluation ∧
        ∃ hdom : U.xEvaluation.fromFunctionField
            (IsLocalRing.closedPoint Z.functionField) ∈ (w.xRationalMap ℂ).domain,
          U.xEvaluation.compOfDefined (w.xRationalMap ℂ) hdom =
            W.xEvaluation := by
  obtain ⟨-, K, hK⟩ := exists_subdivisions_of_toric_internal_factorization p
    U.basis U.regular U.subdivision U.rays U.parameters U.iso U.hom_eq U.pole_eq
    B p.end_mem_vertices
  refine ⟨K, hK, ?_⟩
  intro W x x' xA xB w
  have hpath : (pathRationalMap p).comp xB = xA := by
    simp only [xA, xB, x', W, x, ← Scheme.RationalMap.comp_assoc,
      pathRationalMap_eq_denseTorusPartialIso, denseTorusPartialIso_toRationalMap_comp]
  have hA : A.hom.toRationalMap.comp xA = U.xEvaluation :=
    comp_xEvaluation_denseTorusPartialIso U
  have hB : B.hom.toRationalMap.comp xB = W.xEvaluation :=
    comp_xEvaluation_denseTorusPartialIso W
  refine ⟨?_, hpath, hA, hB, ?_⟩
  · simp only [IsSubdivision.toRationalMap_algebraicMap, pathRationalMap_eq_denseTorusPartialIso,
      denseTorusPartialIso_toRationalMap_comp, W]
  have hEval : U.xEvaluation = W.xEvaluation := by
    calc
      _ = A.hom.toRationalMap.comp xA := hA.symm
      _ = B.hom.toRationalMap.comp xB := by
        simp only [← hpath, ← Scheme.RationalMap.comp_assoc, comp_pathRationalMap]
      _ = _ := hB
  have hw : w.xRationalMap ℂ = Scheme.RationalMap.id _ :=
    Quiver.Path.xRationalMap_nil (B := U.exchangeMatrix) ℂ
  simpa only [hw, Scheme.RationalMap.compHom_id, hEval] using
    U.xEvaluation.compOfDefined_toRationalMap (𝟙 _)

end TauCeti.Toric.Fan.LogarithmicProjection
