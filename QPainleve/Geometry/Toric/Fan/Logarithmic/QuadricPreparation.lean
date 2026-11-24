/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.ToricChange
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.QuadricPreparation

import QPainleve.AlgebraicGeometry.Morphisms.Pullback.IsoLocus
import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision

/-!
# Resolving the toric preparation of a Hirzebruch presentation

For a specified logarithmic morphism to a Hirzebruch surface, one tower of
boundary-node blowups makes the projections along the entire toric preparation
to the quadric regular. The projections agree with the specified rational
composites and pull back the logarithmic poles to the same reduced boundary.

This is the toric preparation in Case C of Proposition 8.11 in
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

local notation "X[" A "]" => Fan.algebraicRealization A
local notation "s[" A "]" => Fan.algebraicRealizationStructureMap A
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "s(" X ")" => (X ↘ S)

/-- A binomial center in the interior of the retained fiber has a common lift to the
preparation fan. This lift is the scheme-theoretic inverse image of the binomial
center with the same parameter on every intermediate Hirzebruch surface. -/
theorem HirzebruchQuadricPreparation.exists_binomialCenter_on_retained_fiber
    {b : Module.Basis (Fin 2) ℤ N} {e : ℕ} (P : HirzebruchQuadricPreparation b e Φ) (c : ℂˣ) :
    ∃ (ρ : ∀ j, (P.model j).Ray) (x : S ⟶ X[P.common]),
      (∀ j, (ρ j).primitiveGenerator = b 1) ∧
      ∀ j, IsPullback x (𝟙 S) π[P.common_model j]
        ((ρ j).binomialCenter ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2))
          (b.detDualEquiv_self _) ((ρ j).surjective_detCharacter b) c) := by
  classical
  have hr (j : Fin (e + 1)) :
      b 1 ∈ Set.range (Ray.primitiveGenerator (Phi := P.model j)) := by
    rw [P.model_rays]
    exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  choose ρ hρ using hr
  let τ := (P.common_model 0).liftRay (ρ 0)
  let hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  refine ⟨ρ, τ.binomialCenter hdim (b.detDualEquiv_self _) (τ.surjective_detCharacter b) c,
    hρ, fun j ↦ ?_⟩
  have hτ : τ = (P.common_model j).liftRay (ρ j) := by
    apply Ray.primitiveGenerator_injective
    rw [(P.common_model 0).primitiveGenerator_liftRay,
      (P.common_model j).primitiveGenerator_liftRay, hρ 0, hρ j]
  rw [hτ]
  apply π[P.common_model j].isPullback_of_isIso_of_range_subset_isoLocus
  · simpa only [Category.id_comp] using
      (P.common_model j).binomialCenter_liftRay_comp_algebraicMap (ρ j) b c
  · exact (P.common_model j).range_binomialCenter_subset_isoLocus (ρ j) hdim
      (b.detDualEquiv_self _) ((ρ j).surjective_detCharacter b) c

variable {X : Scheme} [X.Over S] [IsIntegral X] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 s(X)] {f : X ⟶ X[Φ]} [f.IsOver S]
  {D : X.IdealSheafData}

/-- A specified logarithmic birational morphism to a Hirzebruch surface remains
resolved along the entire sequence of elementary transformations to the quadric
after one tower of boundary-node blowups. In particular, each intermediate
Hirzebruch model and each common blowup is a regular coarsening of the preparation
fan, with a regular projection representing the prescribed rational composite.
The pole ideal of each projection is the reduced total transform of the original
boundary. All links take place on the fiber opposite the ray of `b 1`. -/
theorem exists_nodal_resolution_of_hirzebruch_quadric_preparation
    (b : Module.Basis (Fin 2) ℤ N) (e : ℕ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hrays : Set.range (Ray.primitiveGenerator (Phi := Φ)) =
      {b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1})
    (hf : Scheme.BirationalOver f (𝟙 X[Φ])) (hD : D.IsEffectiveCartier) :
    let _ : Nonempty Φ.cones := hc.nonempty_cones
    let _ : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) :=
      ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let B := Φ.boundaryIdeal hc.nonempty_cones
    let hB := Φ.isEffectiveCartier_boundaryIdeal hΦ hc
      ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2))
    ∀ (ω : hB.toInvertibleSheaf ≅ canonicalBundle ℂ X[Φ] 2)
      (hTotal : (B.comap f).IsEffectiveCartier)
      (hRam : let _ := SmoothOfRelativeDimension.smooth 2 s(X)
        (ramificationIdealSheaf ℂ f).IsEffectiveCartier),
      pullbackTopFormDivisor ℂ f 2 hB ω hTotal hRam = -hD.toCartierDivisor →
      ∃ (P : HirzebruchQuadricPreparation b e Φ) (m : ℕ) (Z : Scheme)
        (T : BlowupTower X m Z) (g : Z ⟶ X[P.common])
        (_ : IsIntegral Z) (_ : IsDominant g) (_ : IsDominant (T.toBase ≫ f))
        (hT : IsNodalBoundaryTower D s(X) (𝟙 X) T),
        g ≫ π[P.common_source] = T.toBase ≫ f ∧
        ∀ (Δ : Fan i) [Nonempty Δ.cones] (L : P.common.IsSubdivision Δ),
          (T.toBase ≫ f).toRationalMap.comp (Φ.denseTorusPartialIso Δ).toRationalMap =
            (g ≫ π[L]).toRationalMap ∧
          ∃ hOver : g ≫ π[L] ≫ s[Δ] = T.toBase ≫ s(X),
            let : Z.Over S := ⟨T.toBase ≫ s(X)⟩
            let : (g ≫ π[L]).IsOver S := ⟨hOver⟩
            let : Smooth s(Z) :=
              (hT.isClosedPointTower.smoothOfRelativeDimension s(X)).smooth
            Δ.IsRegular →
            (Δ.boundaryIdeal inferInstance).comap (g ≫ π[L]) =
              (D.comap T.toBase).radical * ramificationIdealSheaf ℂ (g ≫ π[L]) := by
  intro _ _ B hB ω hTotal hRam hdiv
  obtain ⟨P⟩ := Φ.exists_hirzebruch_quadric_preparation b e hΦ hc hrays
  have hcP : P.common.IsComplete := P.common_source.isComplete_iff.mpr hc
  obtain ⟨Ω, u, v, _, _, _, m, Z, T, q, hZ, hq, hdom, hT, hproj, hregular⟩ :=
    Φ.exists_nodal_resolution_of_toric_change_of_pullbackTopFormDivisor
      b hΦ hc P.common_regular hcP hf hD ω hTotal hRam hdiv
  let g := q ≫ π[v]
  let : Nonempty P.common.cones := hcP.nonempty_cones
  let : Nonempty Ω.cones := v.nonempty_cones_of_nonempty inferInstance
  have hg : IsDominant g := inferInstanceAs (IsDominant (q ≫ π[v]))
  refine ⟨P, m, Z, T, g, hZ, hg, hdom, hT, ?_, ?_⟩
  · simpa only [g, Category.assoc, ← FanHom.algebraicMap_comp, ← IsSubdivision.toFanHom_trans]
      using hproj
  · intro Δ _ L
    have hcomp : g ≫ π[L] = q ≫ π[v.trans L] := by
      dsimp only [g]
      rw [Category.assoc, ← FanHom.algebraicMap_comp, ← IsSubdivision.toFanHom_trans]
    simpa only [hcomp, reassoc_of% hcomp]
      using hregular Δ (v.trans L)

end TauCeti.Toric.Fan
