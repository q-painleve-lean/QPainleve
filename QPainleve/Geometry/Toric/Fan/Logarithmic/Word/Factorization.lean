/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Endpoint

import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Orientation
import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Refinement

/-!
# Cluster words of specified toric factorizations

A resolved Sarkisov factorization gives a word in the frames and labels of the
two specified endpoint models. The fixed-center X evaluation and the sign on
ordered boundary branches both descend from the common nodal refinement.

The resolved paths are those of [Lutz, Theorem 8.4][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.Cluster QPainleve.BlowupTower
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry
open scoped Sarkisov

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)

variable {Z W : Scheme} [Z.Over S] [W.Over S]
  [SmoothOfRelativeDimension 2 (Z ↘ S)] [SmoothOfRelativeDimension 2 (W ↘ S)]
  [IsIntegral Z] [IsIntegral W] [W.IsProjectiveOver ℂ]
  {D : Z.IdealSheafData} {E : W.IdealSheafData}
  {A B : LogarithmicProjection i D} {A' B' : LogarithmicProjection i E} {m : ℕ}

namespace OrderedToricModel

private theorem exists_word_of_common_subdivision [Z.IsSeparated]
    (U : OrderedToricModel A m) (T : OrderedToricModel B m)
    (U' : OrderedToricModel A' m) (T' : OrderedToricModel B' m)
    (H : U'.fan.IsSubdivision U.fan) (K : T'.fan.IsSubdivision T.fan)
    (hU : U'.basis = U.basis) (hT : T'.basis = T.basis)
    (f : W ⟶ Z) [f.IsOver S] [IsDominant f] (hle : D.comap f ≤ E)
    (hfU : f ≫ U.hom = U'.hom ≫ π[H]) (hfT : f ≫ T.hom = T'.hom ≫ π[K])
    (hmatU : U'.exchangeMatrix = U.exchangeMatrix)
    (hmatT : T'.exchangeMatrix = T.exchangeMatrix)
    (hevalU : U'.xEvaluation = f.toRationalMap.comp U.xEvaluation)
    (hevalT : T'.xEvaluation = f.toRationalMap.comp T.xEvaluation)
    (p : SarkisovPath A' B') :
    ∃ w : Word U.exchangeMatrix T.exchangeMatrix,
      U.HasBoundarySign T ((-1 : ℤˣ) ^ w.inversionCount) ∧
      ∃ h, U.xEvaluation.compOfDefined (w.xRationalMap ℂ) h = T.xEvaluation := by
  obtain ⟨_, _, _, w, _, _, -, -, -, -, -, -, -, -, -, hsign, -, heval⟩ :=
    exists_word_of_resolved_sarkisov_path_to_model p U' T'
  have hsign := hsign.of_common_subdivision H K hU hT hle hfU hfT
  rw [hevalU, hevalT] at heval
  have heval := (f.toRationalMap.compOfDefined_eq_iff_of_dominant _ _ _).mp heval
  generalize U.exchangeMatrix = ε at hmatU ⊢
  generalize T.exchangeMatrix = ε' at hmatT ⊢
  subst ε ε'
  exact ⟨w, hsign, heval⟩

end OrderedToricModel

variable [IsNoetherian Z] [Z.IsProjectiveOver ℂ] in
/-- A resolved factorization of the change between two prescribed ordered toric
models produces a word in their original labels and frames. Its X evaluation
intertwines the two models at the given centers on the original common source.
The parity of its inversions gives the sign on the ordered branches there. -/
theorem exists_word_of_resolved_sarkisov_factorization
    (h : HasResolvedSarkisovFactorization A B)
    (U : OrderedToricModel A m) (T : OrderedToricModel B m)
    (hD : D.IsEffectiveCartier) :
    ∃ w : Word U.exchangeMatrix T.exchangeMatrix,
      U.HasBoundarySign T ((-1 : ℤˣ) ^ w.inversionCount) ∧
      ∃ h, U.xEvaluation.compOfDefined (w.xRationalMap ℂ) h = T.xEvaluation := by
  obtain ⟨_, Y, L, hL, A₁, B₁, hAf, hAh, hBf, hBh, ⟨p⟩⟩ :=
    hasResolvedSarkisovFactorization_iff.mp h
  let : Y.Over S := ⟨L.toBase ≫ Z ↘ S⟩
  let : IsIntegral Y := hL.isClosedPointTower.isIntegral (Z ↘ S)
  let : SmoothOfRelativeDimension 2 (Y ↘ S) :=
    hL.isClosedPointTower.smoothOfRelativeDimension (Z ↘ S)
  let : Y.IsProjectiveOver ℂ := L.isProjectiveOver ℂ
  let : Z.IsSeparated := Scheme.IsSeparated.of_isSeparated (Z ↘ S)
  let : IsModification L.toBase :=
    hL.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Z ↘ S)
  let : L.toBase.IsOver S := ⟨rfl⟩
  let := U.prestableFamily_resolvingBoundary
  have hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ Z ↘ S) := by
    rw [← D.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have hN := (Module.finrank_eq_card_basis U.basis).trans (Fintype.card_fin 2)
  have hPole := hL.comap_eq_radical_mul_ramificationIdealSheaf_of_iso hD hNode
    (Iso.refl Y) L.toBase (Category.id_comp _)
  let A₂ := precomposeProjection hN L.toBase hPole A
  let B₂ := precomposeProjection hN L.toBase hPole B
  obtain ⟨Ψ, hΨ, H, e, he, hE, hfU, hu, hevalU, -⟩ :=
    U.exists_refinement_on_nodalTower hD hNode hL
  obtain ⟨Θ, hΘ, K, d, hd, hE', hfT, ht, hevalT, -⟩ :=
    T.exists_refinement_on_nodalTower hD hNode hL
  let U' : OrderedToricModel A₂ m :=
    ⟨Ψ, hΨ, H.trans U.subdivision, U.basis, H.liftRay ∘ U.rays, U.parameters, e, he, hE⟩
  let T' : OrderedToricModel B₂ m :=
    ⟨Θ, hΘ, K.trans T.subdivision, T.basis, K.liftRay ∘ T.rays, T.parameters, d, hd, hE'⟩
  have hA₁ : A₁ = A₂ := LogarithmicProjection.ext hAf hAh
  have hB₁ : B₁ = B₂ := LogarithmicProjection.ext hBf hBh
  exact U.exists_word_of_common_subdivision T U' T' H K rfl rfl L.toBase (le_radical _) hfU hfT
    hu ht hevalU hevalT (hA₁ ▸ hB₁ ▸ p)

variable [IsNoetherian Z] [Z.IsProjectiveOver ℂ] in
/-- A resolved factorization between prescribed models with the same boundary
orientation produces an inversion-free word on their original exchange
matrices, intertwining the two fixed-center X evaluations. -/
theorem exists_inversionFree_word_of_resolved_sarkisov_factorization
    (h : HasResolvedSarkisovFactorization A B)
    (U : OrderedToricModel A m) (T : OrderedToricModel B m)
    (hD : D.IsEffectiveCartier) (hOrientation : U.HasBoundarySign T 1) :
    ∃ v : Word U.exchangeMatrix T.exchangeMatrix, v.inversionCount = 0 ∧
      ∃ h, U.xEvaluation.compOfDefined (v.xRationalMap ℂ) h = T.xEvaluation := by
  obtain ⟨w, hw, heval⟩ := exists_word_of_resolved_sarkisov_factorization h U T hD
  exact U.exists_inversionFree_word_of_boundarySign_eq_one T w hw hOrientation heval

end TauCeti.Toric.Fan.LogarithmicProjection
