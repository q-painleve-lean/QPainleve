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

import QPainleve.Geometry.Toric.Fan.Logarithmic.OrderedStarPath
import TauCeti.Algebra.Group.FreeAbelianCharacter

/-!
# The cluster word of a resolved toric star path

In a block of toric blowups and blowdowns in the resolved factorization of
[Lutz, Theorem 8.4](https://arxiv.org/pdf/2005.05010v3#page=68), the regular projections
all use one ordered internal model. The toric changes preserve the fixed-center
evaluation of that model on the common dense torus. They therefore contribute the
empty word, with the same ordered marking on both ends.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open QPainleve.Cluster QPainleve.BlowupTower TauCeti TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)
local notation "base[" T "]" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd T))
local notation "χ[" c "]" => MonoidHom.comp (freeAbelianCharEquiv.symm c)
  (MulEquiv.toMonoidHom (AddEquiv.toMultiplicative (LinearEquiv.toAddEquiv
    (LinearEquiv.symm (Finsupp.linearEquivFunOnFinite ℤ ℤ _)))))
local notation "E[" b "," a "]" => chargeExchangeMatrix
  (LinearEquiv.toLinearMap (Module.Basis.detDualEquiv b)) (rayChargeMap a)
local notation "B[" b "," a "]" => SkewExchangeMatrix.ofMatrix E[b,a]
  (isSkewSymmetrizer_chargeExchangeMatrix _ (Module.Basis.detDualEquiv_self b) _)

variable {Z : Scheme} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)] [IsIntegral Z]
  {D : Z.IdealSheafData} {A B : LogarithmicProjection i D} {m : ℕ}

private theorem comp_xEvaluation_denseTorusPartialIso (U : OrderedToricModel A m) :
    A.hom.toRationalMap.comp ((A.fan.denseTorusPartialIso U.fan).toRationalMap.comp
      (U.fan.xEvaluation U.basis U.rays χ[U.parameters])) =
    U.hom.toRationalMap.comp (U.fan.xEvaluation U.basis U.rays χ[U.parameters]) := by
  have h := U.subdivision.comp_denseTorusPartialIso (.refl U.fan) U.hom
  simp only [U.hom_comp_subdivision, IsSubdivision.toFanHom_refl, FanHom.algebraicMap_id,
    Category.comp_id] at h
  simp only [← Scheme.RationalMap.comp_assoc, h]

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
      let x := U.fan.xEvaluation U.basis U.rays χ[U.parameters]
      let x' := W.fan.xEvaluation W.basis W.rays χ[W.parameters]
      let xA := (A.fan.denseTorusPartialIso U.fan).toRationalMap.comp x
      let xB := (B.fan.denseTorusPartialIso W.fan).toRationalMap.comp x'
      let w : Word B[U.basis,U.rays] B[W.basis,W.rays] := Quiver.Path.nil
      π[U.subdivision].toRationalMap.comp (pathRationalMap p) =
          π[W.subdivision].toRationalMap ∧
        (pathRationalMap p).comp xB = xA ∧
        A.hom.toRationalMap.comp xA = U.hom.toRationalMap.comp x ∧
        B.hom.toRationalMap.comp xB = W.hom.toRationalMap.comp x' ∧
        ∃ hdom : (U.hom.toRationalMap.comp x).fromFunctionField
            (IsLocalRing.closedPoint Z.functionField) ∈ (w.xRationalMap ℂ).domain,
          (U.hom.toRationalMap.comp x).compOfDefined (w.xRationalMap ℂ) hdom =
            W.hom.toRationalMap.comp x' := by
  obtain ⟨-, K, hK⟩ := exists_subdivisions_of_toric_internal_factorization p
    U.basis U.regular U.subdivision U.rays U.parameters U.iso U.hom_eq U.pole_eq
    B p.end_mem_vertices
  refine ⟨K, hK, ?_⟩
  intro W x x' xA xB w
  have hpath : (pathRationalMap p).comp xB = xA := by
    simp only [xA, xB, x', W, x, ← Scheme.RationalMap.comp_assoc,
      pathRationalMap_eq_denseTorusPartialIso, denseTorusPartialIso_toRationalMap_comp]
  have hA : A.hom.toRationalMap.comp xA = U.hom.toRationalMap.comp x :=
    comp_xEvaluation_denseTorusPartialIso U
  have hB : B.hom.toRationalMap.comp xB = W.hom.toRationalMap.comp x' :=
    comp_xEvaluation_denseTorusPartialIso W
  refine ⟨?_, hpath, hA, hB, ?_⟩
  · simp only [IsSubdivision.toRationalMap_algebraicMap, pathRationalMap_eq_denseTorusPartialIso,
      denseTorusPartialIso_toRationalMap_comp, W]
  simp only [w, Quiver.Path.xRationalMap_nil]
  obtain ⟨hdom, h⟩ := (U.hom.toRationalMap.comp x).compOfDefined_toRationalMap (𝟙 _)
  refine ⟨hdom, ?_⟩
  calc
    _ = U.hom.toRationalMap.comp x := by simpa only [Scheme.RationalMap.compHom_id] using h
    _ = A.hom.toRationalMap.comp xA := hA.symm
    _ = B.hom.toRationalMap.comp xB := by
      simp only [← hpath, ← Scheme.RationalMap.comp_assoc, comp_pathRationalMap]
    _ = W.hom.toRationalMap.comp x' := hB

end TauCeti.Toric.Fan.LogarithmicProjection
