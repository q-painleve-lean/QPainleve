/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.HirzebruchPath
public import QPainleve.Geometry.Toric.Fan.Logarithmic.ToricChange

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
  convert (P.common_model j).isPullback_binomialCenter (ρ j)
    (m := (b.detDualEquiv (ρ j).primitiveGenerator).toAddMonoidHom)
    hdim (b.detDualEquiv_self _) ((ρ j).surjective_detCharacter b) c using 2
  congr 1
  rw [(P.common_model j).primitiveGenerator_liftRay]

variable {X : Scheme} [X.Over S] [IsIntegral X] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 s(X)] {f : X ⟶ X[Φ]} [f.IsOver S]
  {D : X.IdealSheafData}

open LogarithmicProjection
open scoped Sarkisov

/-- A specified logarithmic birational morphism to a Hirzebruch surface remains
resolved along the entire sequence of elementary transformations to the quadric
after one tower of boundary-node blowups. In particular, each intermediate
Hirzebruch model and each common blowup is a regular coarsening of the preparation
fan, with a regular projection representing the prescribed rational composite.
The pole ideal of each projection is the reduced total transform of the original
boundary. The resolved path records the prescribed blowup and blowdown on the
fiber opposite the ray of `b 1` at each step. -/
theorem exists_nodal_resolution_of_hirzebruch_quadric_preparation
    (b : Module.Basis (Fin 2) ℤ N) (e : ℕ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hrays : Set.range (Ray.primitiveGenerator (Phi := Φ)) =
      {b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1})
    (hf : Scheme.BirationalOver f (𝟙 X[Φ])) (hD : D.IsEffectiveCartier) :
    let _ : Nonempty Φ.cones := hc.nonempty_cones
    let B := Φ.boundaryIdeal hc.nonempty_cones
    (B.comap f).IsEffectiveCartier →
      (let _ := SmoothOfRelativeDimension.smooth 2 s(X)
       (ramificationIdealSheaf ℂ f).IsEffectiveCartier) →
      (let _ := SmoothOfRelativeDimension.smooth 2 s(X)
       B.comap f = D * ramificationIdealSheaf ℂ f) →
      ∃ (P : HirzebruchQuadricPreparation b e Φ) (m : ℕ) (Z : Scheme)
        (T : BlowupTower X m Z) (g : Z ⟶ X[P.common])
        (_ : IsIntegral Z) (_ : IsDominant g) (_ : IsDominant (T.toBase ≫ f))
        (hT : IsNodalBoundaryTower D s(X) (𝟙 X) T),
        g ≫ π[P.common_source] = T.toBase ≫ f ∧
        (∀ (Δ : Fan i) [Nonempty Δ.cones] (L : P.common.IsSubdivision Δ),
          (T.toBase ≫ f).toRationalMap.comp (Scheme.PartialIso.ofDenseOpenImmersions
            (Fan.denseTorusι Φ inferInstance) (Fan.denseTorusι Δ inferInstance)).toRationalMap =
            (g ≫ π[L]).toRationalMap ∧
          ∃ hOver : g ≫ π[L] ≫ s[Δ] = T.toBase ≫ s(X),
            let : Z.Over S := ⟨T.toBase ≫ s(X)⟩
            let : (g ≫ π[L]).IsOver S := ⟨hOver⟩
            let : Smooth s(Z) :=
              (hT.isClosedPointTower.smoothOfRelativeDimension s(X)).smooth
            Δ.IsRegular →
              (Δ.boundaryIdeal inferInstance).comap (g ≫ π[L]) =
                (D.comap T.toBase).radical * ramificationIdealSheaf ℂ (g ≫ π[L])) ∧
        letI : Z.Over S := ⟨T.toBase ≫ s(X)⟩
        letI : SmoothOfRelativeDimension 2 s(Z) :=
          hT.isClosedPointTower.smoothOfRelativeDimension s(X)
        ∃ (A B : LogarithmicProjection i (D.comap T.toBase).radical) (p : SarkisovPath A B),
          A.fan = Φ ∧ A.hom ≍ T.toBase ≫ f ∧
          B.fan = P.model 0 ∧ B.hom ≍ g ≫ π[P.common_model 0] ∧
          p.length = 2 * e ∧
            p.rationalMap = (Scheme.PartialIso.ofDenseOpenImmersions
              (Fan.denseTorusι A.fan inferInstance)
              (Fan.denseTorusι B.fan inferInstance)).toRationalMap := by
  intro _ B hTotal hRam hpole
  obtain ⟨P⟩ := Φ.exists_hirzebruch_quadric_preparation b e hΦ hc hrays
  have hcP : P.common.IsComplete := P.common_source.isComplete_iff.mpr hc
  obtain ⟨Ω, u, v, _, _, _, m, Z, T, q, hZ, hq, hdom, hT, hproj, hregular⟩ :=
    Φ.exists_nodal_resolution_of_toric_change_of_boundary_comap_eq
      b hΦ hc P.common_regular hcP hf hD hTotal hRam hpole
  let g := q ≫ π[v]
  let : Nonempty P.common.cones := hcP.nonempty_cones
  let : Nonempty Ω.cones := v.nonempty_cones_of_nonempty inferInstance
  have hg : IsDominant g := inferInstanceAs (IsDominant (q ≫ π[v]))
  have hcomp {Δ : Fan i} (L : P.common.IsSubdivision Δ) :
      g ≫ π[L] = q ≫ π[v.trans L] := by
    dsimp only [g]
    rw [Category.assoc, IsSubdivision.toFanHom_trans v L, FanHom.algebraicMap_comp]
  have hsource : g ≫ π[P.common_source] = T.toBase ≫ f :=
    (hcomp P.common_source).trans hproj
  refine ⟨P, m, Z, T, g, hZ, hg, hdom, hT, hsource, ?_, ?_⟩
  · intro Δ _ L
    simpa only [hcomp L, reassoc_of% hcomp L]
      using hregular Δ (v.trans L)
  · obtain ⟨_, hover, hpole⟩ := hregular P.common v
    let : IsIntegral Z := hZ
    let : Z.Over S := ⟨T.toBase ≫ s(X)⟩
    let : SmoothOfRelativeDimension 2 s(Z) :=
      hT.isClosedPointTower.smoothOfRelativeDimension s(X)
    let C : LogarithmicProjection i (D.comap T.toBase).radical :=
      { fan := P.common
        isRegular := P.common_regular
        isComplete := hcP
        hom := g
        isOver := ⟨by rwa [P.common.algebraicRealization_over]⟩
        isDominant := hg
        comap_boundaryIdeal := hpole P.common_regular }
    obtain ⟨A, B, p, hA, hAh, hB, hBh, hlen, hmap⟩ :=
      P.exists_sarkisov_path_of_quadric_preparation C rfl
    exact ⟨A, B, p, hA, hAh.trans (heq_of_eq hsource), hB, hBh, hlen, hmap⟩

end TauCeti.Toric.Fan
