/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.Geometry.Toric.Fan.Ruling.Quadric

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic

/-!
# Resolved Sarkisov paths through a toric quadric

A resolved mutation to the index-zero Hirzebruch fan can be followed by the ruling exchange
on that fan. Both steps are resolved on the same surface.
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData
open scoped Sarkisov

namespace TauCeti.Toric.Fan.LogarithmicProjection

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Φ "]" => Fan.algebraicRealization Φ
local notation "f[" Φ "]" => (X[Φ] ↘ S)
local notation "B[" Φ "," hc "]" => Fan.boundaryIdeal Φ (Fan.IsComplete.nonempty_cones hc)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {W : Scheme} [W.Over S] [SmoothOfRelativeDimension 2 (W ↘ S)] [PreirreducibleSpace W]
  {D : W.IdealSheafData}

local instance : Smooth (W ↘ S) := SmoothOfRelativeDimension.smooth 2 _

/-- A resolved binomial mutation to a toric quadric followed by its ruling exchange
gives a two-step Sarkisov path with the same pole ideal. The endpoint projection is
the resolved mutation composed with the ruling exchange. -/
theorem exists_mutation_rulingExchange_path (A : LogarithmicProjection i D)
    (b : Basis (Fin 2) ℤ N) (ρ : A.fan.Ray) (c : ℂˣ)
    (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ A.fan.cones) :
    let Ψ := A.fan.mutationFan b ρ.primitiveGenerator_ne_zero ρ.hull_primitiveGenerator_mem hOpp
    ∀ (hΨ : Ψ.IsRegular) (hcΨ : Ψ.IsComplete)
      (b' : Basis (Fin 2) ℤ N) (r : Fin 4 ≃ Ψ.Ray)
      (hr : (fun l ↦ (r l).primitiveGenerator) = ![b' 0, b' 1, -b' 0, (0 : ℤ) • b' 0 - b' 1])
      (p : W ⟶ X[Ψ]) [p.IsOver S],
    A.hom.toRationalMap.comp
        (A.fan.mutationPartialMap b (c : ℂ) ρ.primitiveGenerator_ne_zero
          ρ.hull_primitiveGenerator_mem hOpp).toRationalMap = p.toRationalMap →
    B[Ψ,hcΨ].comap p = D * ramificationIdealSheaf ℂ p →
    ∃ (C : LogarithmicProjection i D) (path : SarkisovPath A C),
      C.fan = Ψ ∧ C.hom ≍ p ≫ (Ψ.quadricRulingExchange b' hΨ hcΨ r hr).toFanHom.algebraicMap ∧
      path.length = 2 := by
  intro Ψ hΨ hcΨ b' r hr p hp hmap hpole
  let : Nonempty Ψ.cones := hcΨ.nonempty_cones
  let μ := (A.fan.mutationPartialMap b (c : ℂ) ρ.primitiveGenerator_ne_zero
    ρ.hull_primitiveGenerator_mem hOpp).toRationalMap
  have hdom : p.toRationalMap.IsDominant :=
    hmap ▸ inferInstanceAs ((A.hom.toRationalMap.comp μ).IsDominant)
  have hpdom : IsDominant p := by
    rw [Scheme.Hom.toRationalMap, Scheme.PartialMap.isDominant_toRationalMap_iff,
      Scheme.Hom.toPartialMap_hom] at hdom
    exact IsDominant.of_comp W.topIso.hom p (H := hdom)
  let B : LogarithmicProjection i D := ⟨Ψ, hΨ, hcΨ, p, hp, hpdom, hpole⟩
  let τ := Ψ.quadricRulingExchange b' hΨ hcΨ r hr
  let t := τ.toFanHom.algebraicMap
  let : IsIso t := inferInstanceAs (IsIso τ.toFanHom.algebraicMap)
  let : t.IsOver S := inferInstanceAs (τ.toFanHom.algebraicMap.IsOver S)
  let : SmoothOfRelativeDimension 2 f[Ψ] := by
    have hRank := (finrank_eq_card_basis b).trans (Fintype.card_fin 2)
    rw [Ψ.algebraicRealization_over, ← hRank]
    exact Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
  have htPole : B[Ψ,hcΨ].comap t = B[Ψ,hcΨ] * ramificationIdealSheaf ℂ t := by
    rw [ramificationIdealSheaf_eq_top_of_isOpenImmersion, mul_top]
    exact τ.comap_boundaryIdeal_algebraicMap _ _
  let C : LogarithmicProjection i D :=
    ⟨Ψ, hΨ, hcΨ, p ≫ t, inferInstance, inferInstance,
      comap_eq_mul_ramificationIdealSheaf_comp ℂ p t 2 htPole hpole⟩
  let m : SarkisovStep A B := ⟨μ, .mutation b ρ c hOpp, hmap⟩
  have ht : Fan.IsSarkisovLink t.toRationalMap := by
    simpa only [Fan.torusTranslation_one, Iso.refl_hom, Category.comp_id] using
      (Fan.IsSarkisovLink.toricIso τ 1)
  let e : SarkisovStep B C := ⟨t.toRationalMap, ht, by
    rw [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom]⟩
  exact ⟨C, (Quiver.Hom.toPath m).cons e, rfl, HEq.rfl, rfl⟩

end TauCeti.Toric.Fan.LogarithmicProjection
