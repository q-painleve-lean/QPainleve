/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Complexity
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import QPainleve.Geometry.Toric.Fan.Boundary.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.MinimalModel
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import QPainleve.Geometry.Toric.Fan.Hirzebruch.BoundarySplit
import QPainleve.Geometry.Toric.Fan.Hirzebruch.Classification
import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.ZeroComplexityTower
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Toric recognition at boundary complexity zero

A complexity-zero anticanonical cycle on a smooth projective rational surface
descends to a complexity-zero cycle on its minimal model. Recognition on the
projective plane and Hirzebruch surfaces and toric realization of the intervening
nodal tower identify the original pair with a complete regular toric pair.

This supplies the toric recognition of the contracted model in the proof of
[Gross, Hacking and Keel, Theorem 1.8][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve TauCeti.AlgebraicGeometry TauCeti.Toric
open QPainleve.BlowupTower LineBundleClass

namespace AlgebraicGeometry.Scheme.IdealSheafData

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "g(" X ")" => (X ↘ S)
local notation "K(" X ")" => LineBundleClass.mk (canonicalBundle ℂ X 2)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (b : Module.Basis (Fin 2) ℤ N)

private theorem exists_toric_iso_of_hirzebruch_model
    {Φ : Fan i} (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (k : ℕ) (r : Fin 4 ≃ Φ.Ray)
    (hr : (fun j ↦ (r j).primitiveGenerator) =
      ![b 0, b 1, -b 0, (k : ℤ) • b 0 - b 1])
    {Y : Scheme} [Y.Over S] [SmoothOfRelativeDimension 2 g(Y)]
    (e : Φ.algebraicRealization ≅ Y) (he : e.hom ≫ g(Y) = Φ.algebraicRealizationStructureMap)
    {D : Y.IdealSheafData} [PrestableFamily g(D.subscheme)] (hD : D.IsEffectiveCartier)
    (hcan : LineBundleClass.mk hD.toInvertibleSheaf = K(Y)) (hzero : D.boundaryComplexity = 0) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (hcΨ : Ψ.IsComplete) (a : Ψ.algebraicRealization ≅ Y),
      a.hom ≫ g(Y) = Ψ.algebraicRealizationStructureMap ∧
        D.comap a.hom = Ψ.boundaryIdeal hcΨ.nonempty_cones := by
  let : e.hom.IsOver S := ⟨he.trans (Fan.algebraicRealization_over (Φ := Φ)).symm⟩
  let : SmoothOfRelativeDimension 2 g(Φ.algebraicRealization) := by
    rw [Fan.algebraicRealization_over]
    exact ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
      Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let E := D.comap e.hom
  let hE : E.IsEffectiveCartier := hD.comap e.hom
  have hcanE : LineBundleClass.mk hE.toInvertibleSheaf = K(Φ.algebraicRealization) := by
    rw [← hD.pullback_mk_toInvertibleSheaf hE, hcan, pullback_mk, mk_pullback_canonicalBundle]
  have hzeroE : E.boundaryComplexity = 0 := (boundaryComplexity_comap_iso e D).trans hzero
  let : IsReduced D.subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := g(D.subscheme))).isReduced
  let : IsReduced E.subscheme := (isReduced_subscheme_iff_radical_eq _).mpr (by
    simp only [E, radical_comap_of_isOpenImmersion,
      (isReduced_subscheme_iff_radical_eq D).mp inferInstance])
  obtain ⟨Ψ, hΨ, hcΨ, a, ha, hBa⟩ := Fan.exists_toric_of_hirzebruch_boundaryComplexity_zero
    b k hΦ hc r hr (Int.natCast_nonneg k) hE hzeroE hcanE
  refine ⟨Ψ, hΨ, hcΨ, a ≪≫ e, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, he, ← Fan.algebraicRealization_over, ha,
      Fan.algebraicRealization_over]
  · simpa only [Iso.trans_hom, comap_comp, E] using hBa

variable {b}

/-- A numbered anticanonical cycle of complexity zero on a smooth projective rational
complex surface is a toric pair. The isomorphism identifies the boundary ideal itself. -/
theorem exists_toric_iso_of_boundaryComplexity_zero
    {X : Scheme} [X.Over S] [X.IsProjectiveOver ℂ] [SmoothOfRelativeDimension 2 g(X)]
    [Scheme.IsRationalOver g(X)] (D : X.IdealSheafData)
    [PrestableFamily g(D.subscheme)] {n : ℕ} [NeZero n] {ι : Type*}
    {p : ι → g(D.subscheme).smoothLocus} (A : Scheme.NodalCycleNumbering p n)
    (b : Module.Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    (hD : D.IsEffectiveCartier)
    (hcan : LineBundleClass.mk hD.toInvertibleSheaf = LineBundleClass.mk (canonicalBundle ℂ X 2))
    (hzero : D.boundaryComplexity = 0) :
    ∃ (Φ : Fan i) (_ : Φ.IsRegular) (hc : Φ.IsComplete) (e : Φ.algebraicRealization ≅ X),
      e.hom ≫ X ↘ S = Φ.algebraicRealizationStructureMap ∧
        D.comap e.hom = Φ.boundaryIdeal hc.nonempty_cones := by
  obtain ⟨Y, s, _, W, T, e, hProj, hSmooth, hRat, hmin, hT, he, -⟩ :=
    X.exists_isClosedPointTower_of_minimal_model ℂ
  let : Y.Over S := ⟨s⟩
  let : Y.IsProjectiveOver ℂ := hProj
  let : SmoothOfRelativeDimension 2 g(Y) := hSmooth
  let : Scheme.IsRationalOver g(Y) := hRat
  let f := e.hom ≫ T.toBase
  let : f.IsOver S := ⟨he⟩
  rcases Y.exists_iso_projectivePlane_or_hirzebruch b hi hmin with
    ⟨a, ha⟩ | ⟨Φ, hΦ, hc, k, r, a, -, hr, ha⟩
  · obtain ⟨Ψ, hΨ, hcΨ, -, -, u, -, -, -, hu, hU⟩ :=
      Fan.exists_toric_of_projectivePlane_tower_boundaryComplexity_zero
        b hi a ha hT e (f := f) rfl hD A hcan hzero
    exact ⟨Ψ, hΨ, hcΨ, u, hu, hU⟩
  let : Smooth s := hSmooth.smooth 2 s
  let : IsIntegral Y := hRat.isIntegral_of_smooth
  let : Module.Finite ℤ (Additive (LineBundleClass Y)) := Y.finite_picard_of_isRationalOver ℂ
  obtain ⟨hU, htotal, hzeroF, hF, hpre, hcanF, -⟩ :=
    hT.exists_numbering_of_boundaryComplexity_eq_zero_of_iso e (f := f) rfl hD A hcan hzero
  let : PrestableFamily g((D.map f).subscheme) := hpre
  obtain ⟨Ω, hΩ, hcΩ, w, hw, hBw⟩ :=
    exists_toric_iso_of_hirzebruch_model b hΦ hc k r hr a ha hF hcanF hzeroF
  obtain ⟨Ψ, hΨ, hcΨ, H, v, hv, hV⟩ :=
    Fan.exists_toric_subdivision_of_nodal_boundary_tower_of_iso hΩ hcΩ
      ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)) hU w hw (congrArg support hBw)
  let u := v ≪≫ e.symm
  have hu : u.hom ≫ f = v.hom ≫ T.toBase := by
    simp only [u, Iso.trans_hom, Iso.symm_hom, f, Category.assoc, Iso.inv_hom_id_assoc]
  refine ⟨Ψ, hΨ, hcΨ, u, ?_, ?_⟩
  · rw [← comp_over f S, ← Category.assoc, hu, hv, Category.assoc, hw,
      FanHom.algebraicMap_comp_algebraicRealizationStructureMap]
  · rw [← htotal, ← radical_comap_of_isOpenImmersion, ← comap_comp, hu, comap_comp,
      radical_comap_of_isOpenImmersion]
    exact hV

end AlgebraicGeometry.Scheme.IdealSheafData
