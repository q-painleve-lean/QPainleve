/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.PairIso

import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Factorization
import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Reframe
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.MarkedFactorization

/-!
# Connecting words for specified pair isomorphisms

A pair isomorphism between fibers of ordered toric presentations gives a cluster
word that intertwines their fixed-center evaluations. The endpoint projections
are the original projections pulled back to a common nodal refinement. The
construction uses the resolved form of [Lutz, Theorem 8.4][Lutz].

[Lutz]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open AlgebraicGeometry CategoryTheory Module
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData Fan.LogarithmicProjection

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))

variable {N₀ V₀ N₁ V₁ : Type} [AddCommGroup N₀] [AddCommGroup V₀] [Module ℝ V₀]
  [AddCommGroup N₁] [AddCommGroup V₁] [Module ℝ V₁] {i₀ : N₀ →+ V₀} {i₁ : N₁ →+ V₁}
  {b₀ : Basis (Fin 2) ℤ N₀} {b₁ : Basis (Fin 2) ℤ N₁} {r n : ℕ} [NeZero n]
  {L₀ L₁ γ₀ γ₁ : Type} [AddCommGroup L₀] [AddCommGroup L₁]
  {H₀ : LinearMap.BilinForm ℤ L₀} {H₁ : LinearMap.BilinForm ℤ L₁}

/-- A specified pair isomorphism between two ordered toric fibers is represented
on their fixed-center X evaluations by a word in their original seed frames and
labelings. The evaluation lies in the domain of the word at the generic point
of the source surface. -/
theorem exists_connecting_word_of_pair_iso
    (Q₀ : CompleteToricPresentation i₀ b₀ r L₀ γ₀)
    (Q₁ : CompleteToricPresentation i₁ b₁ r L₁ γ₁)
    {c₀ c₁ : GeometricRealization.Point Centers[r]}
    {M₀ : MarkedSurface ℂ n H₀ XTor[r]} {M₁ : MarkedSurface ℂ n H₁ XTor[r]}
    (h₀ : Q₀.HasNodalModel c₀ M₀) (h₁ : Q₁.HasNodalModel c₁ M₁)
    (e : M₀.pair ≅ M₁.pair) (hD₀ : D[M₀].IsEffectiveCartier) (hD₁ : D[M₁].IsEffectiveCartier) :
    letI : IsIntegral M₀.surface := M₀.integral
    ∃ w : Word (Fan.rayExchangeMatrix b₀ Q₀.rays) (Fan.rayExchangeMatrix b₁ Q₁.rays),
      ∃ h, M₀.evaluation.compOfDefined (w.xRationalMap ℂ) h =
        (MarkedSurface.surfaceIso e).hom.toRationalMap.comp M₁.evaluation := by
  let : IsIntegral M₀.surface := M₀.integral
  let : IsIntegral M₁.surface := M₁.integral
  let : M₀.surface.IsProjectiveOver ℂ := M₀.projective
  let : SmoothOfRelativeDimension 2 (M₀.surface ↘ S) := M₀.smooth
  let : Smooth (M₀.surface ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian M₀.surface := isNoetherian_of_finiteType (M₀.surface ↘ S)
  obtain ⟨_, W, T, hT, π, s, hSm, hmod, rfl, rfl, A, B, U, W', hCartier, -, -,
    hA, -, hm₀, hm₁, hEval₀, hEval₁⟩ :=
    Q₀.exists_common_ordered_models_of_pair_iso Q₁ h₀ h₁ e hD₀ hD₁
  let : W.Over S := ⟨T.toBase ≫ M₀.surface ↘ S⟩
  let : SmoothOfRelativeDimension 2 (W ↘ S) := hSm
  let : W.IsProjectiveOver ℂ := T.isProjectiveOver ℂ
  let : IsIntegral W := hT.isClosedPointTower.isIntegral (M₀.surface ↘ S)
  let : IsNoetherian W := isNoetherian_of_finiteType (W ↘ S)
  let : IsModification T.toBase := hmod
  let : IsModification A.hom := hA
  let latticeEquiv := (b₁.equiv b₀ (Equiv.refl _)).toAddEquiv
  obtain ⟨B', U', _, -, -, -, -, -, hB', hmatrix, hEval⟩ :=
    W'.exists_reframe_of_latticeEquiv Q₀.fan.lattice latticeEquiv
  let : IsModification B'.hom := hB'
  have hN := (hT.radical_comap_toBase hD₀ M₀.boundaryIdeal_nodal).2
  have hfactor := exists_resolved_sarkisov_factorization b₀ Q₀.fan.lattice A B' hCartier hN
  obtain ⟨w, -, hw⟩ := exists_word_of_resolved_sarkisov_factorization hfactor U U' hCartier
  rw [hEval₀, hEval, hEval₁] at hw
  have he : (T.toBase ≫ (MarkedSurface.surfaceIso e).hom).toRationalMap.comp M₁.evaluation =
      T.toBase.toRationalMap.comp
        ((MarkedSurface.surfaceIso e).hom.toRationalMap.comp M₁.evaluation) := by
    simp only [← RationalMap.comp_assoc, RationalMap.comp_toRationalMap, Hom.toRationalMap_compHom]
  rw [he] at hw
  have hw' := (T.toBase.toRationalMap.compOfDefined_eq_iff_of_dominant _ _ _).mp hw
  have hm₀' : U.exchangeMatrix = Fan.rayExchangeMatrix b₀ Q₀.rays :=
    SkewExchangeMatrix.ext (hm₀.trans (Fan.rayExchangeMatrix_matrix _ _).symm)
  have hm₁' : U'.exchangeMatrix = Fan.rayExchangeMatrix b₁ Q₁.rays :=
    hmatrix.trans (SkewExchangeMatrix.ext (hm₁.trans (Fan.rayExchangeMatrix_matrix _ _).symm))
  generalize Fan.rayExchangeMatrix b₀ Q₀.rays = E₀ at hm₀' ⊢
  generalize Fan.rayExchangeMatrix b₁ Q₁.rays = E₁ at hm₁' ⊢
  subst E₀ E₁
  exact ⟨w, hw'⟩

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
