/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Birational
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Morphism
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Factorization

import QPainleve.Geometry.Toric.Fan.CommonRefinement
import QPainleve.Geometry.Toric.Fan.Subdivision.NodalRefinement

/-!
# Nodal resolution of toric changes of target

A toric change of target factors through a common regular fan. For a specified
logarithmic morphism to the initial toric surface, a single tower of blowups
of boundary nodes makes every partial composite of this factorization regular.
The resulting morphisms agree with the prescribed birational maps on their
rational domains. The cartesian comparison of the internal blowup models is
`IsSubdivision.exists_nodal_refinement_internalBlowupTower`.

This is the toric change of target in the proof of Theorem 8.4 of [Lutz's appendix
to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i}

local notation "X[" A "]" => Fan.algebraicRealization A
local notation "s[" A "]" => Fan.algebraicRealizationStructureMap A
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)
local notation "S" => Spec (CommRingCat.of ℂ)

section Ordered

variable {Ξ : Fan i} [Nonempty Φ.cones]

/-- A toric change of target of an ordered internal blowup model, with a specified
identification of its surface and boundary, admits a single nodal resolution.
The two chains of star subdivisions give the forward blowups and the reverse
blowdowns of the toric change. For every coarsening of the common fan, including
every intermediate fan of either chain, the regular projection equals the
corresponding rational composite with the original morphism and is over `ℂ`. -/
theorem exists_nodal_resolution_of_toric_change
    (b : Module.Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (hs : Φ.support = Ψ.support) (hΞ : Ξ.IsRegular) (H : Ξ.IsSubdivision Φ)
    {m : ℕ} (ρ : Fin m → Ξ.Ray) (c : Fin m → ℂˣ)
    {X : Scheme} (f : X ⟶ X[Φ]) (D : X.IdealSheafData) :
    letI : Nonempty Ξ.cones := H.nonempty_cones_of_nonempty inferInstance
    let A := Ξ.internalBlowupTower b ρ c
    ∀ (e : A.1 ≅ X), e.hom ≫ f = A.2.toTower.toBase ≫ π[H] →
      D.comap e.hom = A.2.boundaryι.ker →
      ∃ (Ω : Fan i) (J : Ω.IsSubdivision Φ) (_ : Ω.IsSubdivision Ψ),
        Ω.IsRegular ∧
        Relation.ReflTransGen IsTwoRayStarSubdivision Φ Ω ∧
        Relation.ReflTransGen IsTwoRayStarSubdivision Ψ Ω ∧
        ∃ (n : ℕ) (Z : Scheme) (T : BlowupTower X n Z) (g : Z ⟶ X[Ω])
          (_ : IsIntegral Z) (_ : IsDominant g) (_ : IsDominant (T.toBase ≫ f)),
          IsNodalBoundaryTower D (f ≫ s[Φ]) (𝟙 X) T ∧
          g ≫ π[J] = T.toBase ≫ f ∧
          ∀ (Δ : Fan i) [Nonempty Δ.cones] (L : Ω.IsSubdivision Δ),
            (T.toBase ≫ f).toRationalMap.comp (Φ.denseTorusPartialIso Δ).toRationalMap =
              (g ≫ π[L]).toRationalMap ∧
            g ≫ π[L] ≫ s[Δ] = T.toBase ≫ f ≫ s[Φ] := by
  intro A e he hD
  let : Nonempty Ξ.cones := H.nonempty_cones_of_nonempty inferInstance
  have hN : Module.finrank ℤ N = 2 := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  obtain ⟨Ω, L, K, hΩ⟩ := Ξ.exists_regular_common_subdivision Ψ hΞ hΨ hN (H.support_eq.trans hs)
  let : Nonempty Ω.cones := L.nonempty_cones_of_nonempty inferInstance
  let J := L.trans H
  obtain ⟨n, W, U, a, hU, hcart, -⟩ :=
    L.exists_nodal_refinement_internalBlowupTower b hΩ hΞ ρ c
  let B := Ω.internalBlowupTower b (L.liftRay ∘ ρ) c
  have hstructure : e.inv ≫ A.2.toTower.toBase ≫ s[Ξ] =
      (BlowupTower.nil (X := X)).toBase ≫ (f ≫ s[Φ]) := by
    simp only [toBase_nil, Category.id_comp,
      ← H.toFanHom.algebraicMap_comp_algebraicRealizationStructureMap,
      ← Category.assoc, ← he, Iso.inv_hom_id]
  have hsupport : (A.2.boundaryι.ker.comap e.inv).support =
      (D.comap (BlowupTower.nil (X := X)).toBase).support := by
    rw [← hD, ← comap_comp, Iso.inv_hom_id, toBase_nil]
  have hnil : IsNodalBoundaryTower D (f ≫ s[Φ]) (𝟙 X) .nil := .nil
  obtain ⟨Z, T, d, hT, hbase, -⟩ := hnil.exists_append_of_iso hU e.symm hstructure hsupport
  let g := d.hom ≫ a.inv ≫ B.2.toTower.toBase
  have hsquare : a.hom ≫ U.toBase ≫ A.2.toTower.toBase = B.2.toTower.toBase ≫ π[L] :=
    (Category.assoc _ _ _).symm.trans hcart.w
  have hrefinement : g ≫ π[L] = d.hom ≫ U.toBase ≫ A.2.toTower.toBase := by
    simp only [g, Category.assoc, ← hsquare, Iso.inv_hom_id_assoc]
  have hproj : g ≫ π[J] = T.toBase ≫ f := by
    rw [IsSubdivision.toFanHom_trans L H, FanHom.algebraicMap_comp, ← Category.assoc,
      hrefinement, hbase]
    simp only [toBase_nil, Iso.symm_inv, Category.comp_id, Category.assoc, he]
  have : IsIntegral B.1 := isIntegral_internalBlowupTower b _ c hΩ
  have : IsIntegral Z := IsIntegral.of_isIso (a ≪≫ d.symm).hom
  have := isModification_internalBlowupTower_toBase b (L.liftRay ∘ ρ) c hΩ
  have : IsDominant g := inferInstanceAs (IsDominant (d.hom ≫ a.inv ≫ B.2.toTower.toBase))
  have : IsDominant (T.toBase ≫ f) :=
    hproj ▸ inferInstanceAs (IsDominant (g ≫ π[J]))
  refine ⟨Ω, J, K, hΩ, J.exists_starSubdivision_factorization hΦ hΩ hN,
    K.exists_starSubdivision_factorization hΨ hΩ hN, _, Z, T, g, ‹_›, ‹_›, ‹_›, hT, hproj, ?_⟩
  intro Δ _ M
  refine ⟨?_, ?_⟩
  · simpa only [hproj] using J.comp_denseTorusPartialIso M g
  · simpa only [Category.assoc, FanHom.algebraicMap_comp_algebraicRealizationStructureMap]
      using congrArg (· ≫ s[Φ]) hproj

end Ordered

section Logarithmic

variable {X : Scheme} [X.Over S] [IsIntegral X] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)]
  {f : X ⟶ X[Φ]} [f.IsOver S] {D : X.IdealSheafData}

/-- If a specified birational morphism to a complete regular toric surface pulls back
a toric logarithmic top form with divisor `-D`, then a single nodal blowup tower of
`(X, D)` resolves the change to another complete regular toric surface on the
same lattice. The resolution works for the entire factorization by star subdivisions
and their inverses and preserves the given morphism to the starting surface. -/
theorem exists_nodal_resolution_of_toric_change_of_pullbackTopFormDivisor
    (b : Module.Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hcΦ : Φ.IsComplete)
    (hΨ : Ψ.IsRegular) (hcΨ : Ψ.IsComplete)
    (hf : Scheme.BirationalOver f (𝟙 X[Φ])) (hD : D.IsEffectiveCartier) :
    let _ : Nonempty Φ.cones := hcΦ.nonempty_cones
    let _ : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) :=
      ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let B := Φ.boundaryIdeal hcΦ.nonempty_cones
    let hB := Φ.isEffectiveCartier_boundaryIdeal hΦ hcΦ
      ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2))
    ∀ (ω : hB.toInvertibleSheaf ≅ canonicalBundle ℂ X[Φ] 2)
      (hTotal : (B.comap f).IsEffectiveCartier)
      (hRam : let _ := SmoothOfRelativeDimension.smooth 2 (X ↘ S)
        (ramificationIdealSheaf ℂ f).IsEffectiveCartier),
      pullbackTopFormDivisor ℂ f 2 hB ω hTotal hRam = -hD.toCartierDivisor →
      ∃ (Ω : Fan i) (J : Ω.IsSubdivision Φ) (_ : Ω.IsSubdivision Ψ),
        Ω.IsRegular ∧
        Relation.ReflTransGen IsTwoRayStarSubdivision Φ Ω ∧
        Relation.ReflTransGen IsTwoRayStarSubdivision Ψ Ω ∧
        ∃ (n : ℕ) (Z : Scheme) (T : BlowupTower X n Z) (g : Z ⟶ X[Ω])
          (_ : IsIntegral Z) (_ : IsDominant g) (_ : IsDominant (T.toBase ≫ f)),
          IsNodalBoundaryTower D (f ≫ s[Φ]) (𝟙 X) T ∧
          g ≫ π[J] = T.toBase ≫ f ∧
          ∀ (Δ : Fan i) [Nonempty Δ.cones] (L : Ω.IsSubdivision Δ),
            (T.toBase ≫ f).toRationalMap.comp (Φ.denseTorusPartialIso Δ).toRationalMap =
              (g ≫ π[L]).toRationalMap ∧
            g ≫ π[L] ≫ s[Δ] = T.toBase ≫ f ≫ s[Φ] := by
  intro _ _ B hB ω hTotal hRam hdiv
  obtain ⟨Ξ, hΞ, H, m, ρ, c, e, he, hboundary⟩ :=
    Φ.exists_toric_internal_factorization_of_pullbackTopFormDivisor
      b hΦ hcΦ hf hD ω hTotal hRam hdiv
  have hs : Φ.support = Ψ.support := by
    ext x
    exact ⟨fun _ ↦ Ψ.mem_support.mpr (Ψ.isComplete_iff.mp hcΨ x),
      fun _ ↦ Φ.mem_support.mpr (Φ.isComplete_iff.mp hcΦ x)⟩
  exact exists_nodal_resolution_of_toric_change b hΦ hΨ hs hΞ H ρ c f D e he hboundary

end Logarithmic

end TauCeti.Toric.Fan
