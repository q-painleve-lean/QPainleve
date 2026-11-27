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

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "X[" Φ "]" => Fan.finiteFanScheme k₀ Φ
local notation "f[" Φ "]" => (X[Φ] ↘ S)
local notation "B[" Φ "," hc "]" => Fan.toricBoundaryIdeal k₀ Φ (Fan.IsComplete.nonempty_cones hc)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {W : Scheme} [W.Over (Spec (.of k₀))] [SmoothOfRelativeDimension 2 (W ↘ Spec (.of k₀))]
    [PreirreducibleSpace W]
  {D : W.IdealSheafData}

local instance : Smooth (W ↘ S) := SmoothOfRelativeDimension.smooth 2 _

omit [IsAlgClosed k₀] in
/-- A resolved binomial mutation to a toric quadric followed by its ruling exchange
gives a two-step Sarkisov path with the same pole ideal. The endpoint projection is
the resolved mutation composed with the ruling exchange. -/
theorem exists_mutation_rulingExchange_path (A : LogarithmicProjection k₀ i D)
    (b : Basis (Fin 2) ℤ N) (ρ : A.fan.Ray) (c : k₀ˣ)
    (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ A.fan.cones) :
    let Ψ := A.fan.mutationFan b ρ.primitiveGenerator_ne_zero ρ.hull_primitiveGenerator_mem hOpp
    ∀ (hΨ : Ψ.IsRegular) (hcΨ : Ψ.IsComplete)
      (b' : Basis (Fin 2) ℤ N) (r : Fin 4 ≃ Ψ.Ray)
      (hr : (fun l ↦ (r l).primitiveGenerator) = ![b' 0, b' 1, -b' 0, (0 : ℤ) • b' 0 - b' 1])
      (p : W ⟶ X[Ψ]) [p.IsOver S],
    A.hom.toRationalMap.comp
        (A.fan.mutationPartialMap k₀ b (c : k₀) ρ.primitiveGenerator_ne_zero
          ρ.hull_primitiveGenerator_mem hOpp).toRationalMap = p.toRationalMap →
    B[Ψ,hcΨ].comap p = D * ramificationIdealSheaf k₀ p →
    ∃ (C : LogarithmicProjection k₀ i D) (path : SarkisovPath A C),
      C.fan = Ψ ∧ C.hom ≍ p ≫ ((Ψ.quadricRulingExchange b' hΨ hcΨ r
        hr).toFanHom.finiteFanSchemeHom k₀) ∧
      path.length = 2 := by
  intro Ψ hΨ hcΨ b' r hr p hp hmap hpole
  let : Nonempty Ψ.cones := hcΨ.nonempty_cones
  let μ := (A.fan.mutationPartialMap k₀ b (c : k₀) ρ.primitiveGenerator_ne_zero
    ρ.hull_primitiveGenerator_mem hOpp).toRationalMap
  have hdom : p.toRationalMap.IsDominant :=
    hmap ▸ inferInstanceAs ((A.hom.toRationalMap.comp μ).IsDominant)
  have hpdom : IsDominant p := by
    rw [Scheme.Hom.toRationalMap, Scheme.PartialMap.isDominant_toRationalMap_iff,
      Scheme.Hom.toPartialMap_hom] at hdom
    exact IsDominant.of_comp W.topIso.hom p (H := hdom)
  let B : LogarithmicProjection k₀ i D := ⟨Ψ, hΨ, hcΨ, p, hp, hpdom, hpole⟩
  let τ := Ψ.quadricRulingExchange b' hΨ hcΨ r hr
  let t := (τ.toFanHom.finiteFanSchemeHom k₀)
  let : IsIso t := inferInstanceAs (IsIso (τ.toFanHom.finiteFanSchemeHom k₀))
  let : t.IsOver S := inferInstanceAs ((τ.toFanHom.finiteFanSchemeHom k₀).IsOver S)
  let : SmoothOfRelativeDimension 2 f[Ψ] := by
    have hRank := (finrank_eq_card_basis b).trans (Fintype.card_fin 2)
    rw [Ψ.finiteFanScheme_over k₀, ← hRank]
    exact Ψ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΨ
  have htPole : B[Ψ,hcΨ].comap t = B[Ψ,hcΨ] * ramificationIdealSheaf k₀ t := by
    rw [ramificationIdealSheaf_eq_top_of_isOpenImmersion, mul_top]
    exact τ.comap_toricBoundaryIdeal_finiteFanSchemeHom k₀ _ _
  let C : LogarithmicProjection k₀ i D :=
    ⟨Ψ, hΨ, hcΨ, p ≫ t, inferInstance, inferInstance,
      comap_eq_mul_ramificationIdealSheaf_comp k₀ p t 2 htPole hpole⟩
  let m : SarkisovStep A B := ⟨μ, .mutation b ρ c hOpp, hmap⟩
  have ht : Fan.IsSarkisovLink k₀ t.toRationalMap := by
    simpa only [Fan.torusTranslationIso_one, Iso.refl_hom, Category.comp_id] using
      (Fan.IsSarkisovLink.toricIso τ 1)
  let e : SarkisovStep B C := ⟨t.toRationalMap, ht, by
    rw [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom]⟩
  exact ⟨C, (Quiver.Hom.toPath m).cons e, rfl, HEq.rfl, rfl⟩

end TauCeti.Toric.Fan.LogarithmicProjection
