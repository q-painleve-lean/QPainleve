/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.FunctionField

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Open conditions for evaluations in families

If a dominant evaluation is regular on a chart open over the parameter scheme,
the parameters where the chart meets a nonempty open of the target contain
a dense open. A rational evaluation represented by the chart on a fiber
then takes its generic value in that target open.
-/

public section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- A regular family of evaluations with dominant total evaluation and an open projection
has a dense open of parameters where the generic fiber evaluations land in `U`.
A fiber may be represented on any integral dominant chart of the corresponding source. -/
theorem Hom.exists_dense_open_for_rational_evaluation {V T A : Scheme.{u}}
    [PreirreducibleSpace T] (π : V ⟶ T) (hπ : IsOpenMap π)
    (e : V ⟶ A) [IsDominant e] (U : A.Opens) (hU : (U : Set A).Nonempty) :
    ∃ W : T.Opens, Dense (W : Set T) ∧
      ∀ {S Y : Scheme.{u}} [IsIntegral Y] (c : S ⟶ T) (s : S), c s ∈ W →
        ∀ [IsIntegral (pullback π c)] (j : pullback π c ⟶ Y) [IsDominant j]
          (a : Y ⤏ A),
          j.toRationalMap.comp a = (pullback.fst π c ≫ e).toRationalMap →
          a.fromFunctionField (IsLocalRing.closedPoint Y.functionField) ∈ U := by
  let W : T.Opens := ⟨π '' (e ⁻¹ᵁ U : Set V), hπ _ (e ⁻¹ᵁ U).isOpen⟩
  have hW : (W : Set T).Nonempty := by
    obtain ⟨v, hv⟩ := e.denseRange.exists_mem_open U.isOpen hU
    exact ⟨π v, v, hv, rfl⟩
  refine ⟨W, W.isOpen.dense hW, ?_⟩
  intro S Y _ c s hs _ j _ a ha
  obtain ⟨v, hv, heq⟩ := hs
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback v s heq
  let E := pullback.fst π c ≫ e
  have hzU : z ∈ E ⁻¹ᵁ U := by
    simpa only [Hom.mem_preimage, E, Hom.comp_apply, hz] using e.mem_preimage.mp hv
  have hη := (genericPoint_specializes z).mem_open (E ⁻¹ᵁ U).isOpen hzU
  let x : Spec (pullback π c).functionField := IsLocalRing.closedPoint _
  have hvalue := congrArg (fun g : pullback π c ⤏ A ↦ g.fromFunctionField x) ha
  have : Subsingleton (Spec Y.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Y.functionField))
  have hx : Spec.map j.toRationalMap.functionFieldMap x =
      IsLocalRing.closedPoint Y.functionField := Subsingleton.elim _ _
  rw [RationalMap.fromFunctionField_comp, Hom.comp_apply, hx] at hvalue
  rw [hvalue]
  exact (E.fromFunctionField_toRationalMap_apply_closedPoint).symm ▸ E.mem_preimage.mp hη

end AlgebraicGeometry.Scheme
