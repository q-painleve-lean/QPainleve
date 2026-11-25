/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Endpoint

import QPainleve.Algebra.Cluster.Word.Inversion

/-!
# Orientation-preserving words for specified toric models

The determinant signs along a resolved Sarkisov path give the sign between the
branch orders of the prescribed endpoint models. When those orders agree, the
inversions cancel in pairs and the resulting word still intertwines the
fixed-center X evaluations on the common resolving surface.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.Cluster
open scoped Sarkisov

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)

variable {Z : Scheme} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)] [IsIntegral Z]
  {D : Z.IdealSheafData} {A B : LogarithmicProjection i D} {m : ℕ}

/-- A resolved Sarkisov path between prescribed models with the same boundary
orientation induces an inversion-free word in the prescribed frames and labels.
The word carries the source X evaluation to the target evaluation at the generic
point of the common resolving surface. -/
theorem exists_inversionFree_word_of_resolved_sarkisov_path_to_model [Z.IsProjectiveOver ℂ]
    (p : SarkisovPath A B) (U : OrderedToricModel A m) (T : OrderedToricModel B m)
    (hOrientation : U.HasBoundarySign T 1) :
    ∃ v : Word U.exchangeMatrix T.exchangeMatrix, v.inversionCount = 0 ∧
      ∃ h, U.xEvaluation.compOfDefined (v.xRationalMap ℂ) h = T.xEvaluation := by
  obtain ⟨_, _, _, w, _, _, -, -, -, -, -, -, -, -, -, hsign, -, heval⟩ :=
    exists_word_of_resolved_sarkisov_path_to_model p U T
  have heven : Even w.inversionCount :=
    (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp (hsign.unique hOrientation)
  obtain ⟨v, hv, hpull⟩ := w.exists_xPullback_eq_of_even_inversionCount ℂ heven
  refine ⟨v, hv, ?_⟩
  rw [← (Quiver.Path.xRationalMap_eq_iff ℂ w v).mpr hpull]
  exact heval

end TauCeti.Toric.Fan.LogarithmicProjection
