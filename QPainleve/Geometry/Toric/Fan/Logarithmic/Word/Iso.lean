/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Basic

import QPainleve.AlgebraicGeometry.Modules.Differentials.Ramification
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# Ordered logarithmic models under isomorphisms of the resolving surface

An isomorphism of the resolving surfaces preserving the pole ideal transports
the ordered toric model and pulls back its fixed-center evaluation.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection.OrderedToricModel

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

local notation "S" => Spec (CommRingCat.of k₀)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Z W : Scheme} [Z.Over (Spec (.of k₀))] [W.Over (Spec (.of k₀))] [IsIntegral Z] [IsIntegral W]
  [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k₀))] [SmoothOfRelativeDimension 2 (W ↘ Spec
    (.of k₀))]
  {D : Z.IdealSheafData} {E : W.IdealSheafData} {A : LogarithmicProjection k₀ i D} {m : ℕ}

omit [IsAlgClosed k₀] in
/-- An isomorphism over the base identifies the resolving surfaces of two ordered
models of the same toric projection. The transported model uses the original
exchange matrix, and its X evaluation is pulled back along the isomorphism. -/
theorem exists_precomposeIso (U : OrderedToricModel A m) [IsModification A.hom]
    (e : W ≅ Z) [e.hom.IsOver S] (hE : D.comap e.hom = E) :
    ∃ (B : LogarithmicProjection k₀ i E) (T : OrderedToricModel B m),
      B.fan = A.fan ∧ B.hom ≍ e.hom ≫ A.hom ∧ IsModification B.hom ∧
      T.exchangeMatrix = U.exchangeMatrix ∧
      T.xEvaluation = e.hom.toRationalMap.comp U.xEvaluation := by
  have hN := (Module.finrank_eq_card_basis U.basis).trans (Fintype.card_fin 2)
  have hPole : letI : Smooth (W ↘ S) := SmoothOfRelativeDimension.smooth 2 _
      D.comap e.hom = E * ramificationIdealSheaf k₀ e.hom := by
    let : Smooth (W ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    rw [ramificationIdealSheaf_eq_top_of_isOpenImmersion k₀ e.hom, mul_top, hE]
  let B := precomposeProjection hN e.hom hPole A
  have hB : B.hom = e.hom ≫ A.hom := (rfl)
  have hcancel : (U.iso ≪≫ e.symm).hom ≫ B.hom = U.iso.hom ≫ A.hom := by
    simp only [hB, Iso.trans_hom, Iso.symm_hom]
    exact (Category.assoc ..).trans (congrArg (U.iso.hom ≫ ·) (e.inv_hom_id_assoc A.hom))
  let T : OrderedToricModel B m :=
    { fan := U.fan
      regular := U.regular
      subdivision := U.subdivision
      basis := U.basis
      rays := U.rays
      parameters := U.parameters
      iso := U.iso ≪≫ e.symm
      hom_eq := hcancel.trans U.hom_eq
      pole_eq := by
        calc
          E.comap (U.iso ≪≫ e.symm).hom = D.comap U.iso.hom := by
            simp only [← hE, Iso.trans_hom, Iso.symm_hom, ← comap_comp,
              Category.assoc, Iso.inv_hom_id, Category.comp_id]
          _ = _ := U.pole_eq }
  refine ⟨B, T, rfl, heq_of_eq hB, hB ▸ inferInstanceAs (IsModification (e.hom ≫ A.hom)), ?_, ?_⟩
  · exact QPainleve.Cluster.SkewExchangeMatrix.ext <| by
      rw [T.exchangeMatrix_matrix, U.exchangeMatrix_matrix]
  · have hf : T.hom = e.hom ≫ U.hom := by
      rw [T.hom_def, U.hom_def]
      exact Category.assoc _ _ _
    simp only [T.xEvaluation_def, U.xEvaluation_def, ← Scheme.RationalMap.comp_assoc,
      Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom]
    congr 1
    exact congrArg Scheme.Hom.toRationalMap hf

end TauCeti.Toric.Fan.LogarithmicProjection.OrderedToricModel
