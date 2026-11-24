/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.TwoCenters

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.Mutation.Projective
import QPainleve.Geometry.Toric.Fan.Picard.Quadric

/-!
# The resolved Sarkisov path for two smooth quadric centers

Two high-order centers on opposite sections of a quadric give a resolved path
consisting of two elementary transformations and a ruling exchange. The path
joins the original projection to the projection of a strictly lower degree
quadric resolution on the same resolving surface. It uses
`BlowupTower.IsClosedPointTower.exists_quadric_resolution_of_two_smooth_high_centers`
to obtain the regular projections and their common pole ideal.

This is the two-smooth-center block of Proposition 8.11, Case B, in
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone TauCeti.Toric
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData TauCeti.SymmetricAlgebra
open Fan Fan.LogarithmicProjection
open scoped Sarkisov

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular)
  (hc : Φ.IsComplete) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "f[" Δ "]" => (X[Δ] ↘ S)
local notation "B[" Δ "," h "]" => Fan.boundaryIdeal Δ (Fan.IsComplete.nonempty_cones h)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "fP" => (P ↘ S)
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "center[" u "," c "]" =>
  (Fan.Ray.binomialCenter u rankTwo (b.detDualEquiv_self (Fan.Ray.primitiveGenerator u))
    (Fan.Ray.surjective_detCharacter u b) c) (IsLocalRing.closedPoint ℂ)

local notation "ρ" => r 0
local notation "hv" => Fan.Ray.primitiveGenerator_ne_zero (ρ)
local notation "hp" => Fan.Ray.hull_primitiveGenerator_mem (ρ)
local notation "opp₀" => Fan.hull_neg_primitiveGenerator_mem_of_hirzebruch b 0 r hr
local notation "Ψ" => Φ.mutationFan b hv hp opp₀
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp opp₀) hΦ
local notation "hcΨ" => Iff.mpr (Φ.isComplete_mutationFan_iff b hv hp opp₀) hc
local notation "s" => Equiv.trans r (Φ.mutationFanRayEquiv b hv hp opp₀)
local notation "hs" => Fan.Ray.mutationFan_hirzebruch_ray_generators_of_section_zero
  (ρ) b opp₀ 0 r hr rfl
local notation "σ" => s 2
local notation "hw" => Fan.Ray.primitiveGenerator_ne_zero (σ)
local notation "hwPos" => Fan.Ray.hull_primitiveGenerator_mem (σ)
local notation "opp₁" => Fan.hull_neg_primitiveGenerator_mem_of_hirzebruch_section_two b 1 s hs
local notation "Ω" => Fan.mutationFan (Ψ) b hw hwPos opp₁
local notation "hΩ" => Iff.mpr (Fan.isRegular_mutationFan_iff (Ψ) b hw hwPos opp₁) hΨ
local notation "hcΩ" => Iff.mpr (Fan.isComplete_mutationFan_iff (Ψ) b hw hwPos opp₁) hcΨ
local notation "t" => Equiv.trans s (Fan.mutationFanRayEquiv (Ψ) b hw hwPos opp₁)
local notation "μ₀[" c "]" =>
  Scheme.PartialMap.toRationalMap (Φ.mutationPartialMap b (c : ℂ) hv hp opp₀)
local notation "μ₁[" d "]" =>
  Scheme.PartialMap.toRationalMap (Fan.mutationPartialMap (Ψ) b (d : ℂ) hw hwPos opp₁)

variable {Y : Scheme}

include hΦ in
private theorem exists_two_smooth_center_path
    [Y.Over S] [SmoothOfRelativeDimension 2 (Y ↘ S)] [PreirreducibleSpace Y]
    [Nonempty Φ.cones] [Nonempty (Ψ).cones] [Nonempty (Ω).cones]
    {D : Y.IdealSheafData} (c d : ℂˣ) (τ : FanEquiv (Ω) (Ω))
    (p₀ : Y ⟶ X[Φ]) (p₁ : Y ⟶ X[Ψ]) (p₂ p₃ : Y ⟶ X[Ω])
    [p₀.IsOver S] [p₁.IsOver S] [p₂.IsOver S] [p₃.IsOver S]
    [IsDominant p₀] [IsDominant p₁] [IsDominant p₂] [IsDominant p₃]
    (h₁ : p₀.toRationalMap.comp μ₀[c] = p₁.toRationalMap)
    (h₂ : p₁.toRationalMap.comp μ₁[d] = p₂.toRationalMap)
    (h₃ : p₃ = p₂ ≫ τ.toFanHom.algebraicMap)
    (hpoles : letI : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
      B[Φ,hc].comap p₀ = D * ramificationIdealSheaf ℂ p₀ ∧
      B[Ψ,hcΨ].comap p₁ = D * ramificationIdealSheaf ℂ p₁ ∧
      B[Ω,hcΩ].comap p₂ = D * ramificationIdealSheaf ℂ p₂ ∧
      B[Ω,hcΩ].comap p₃ = D * ramificationIdealSheaf ℂ p₃) :
    ∃ (A A₁ A₂ C : LogarithmicProjection i D) (path : SarkisovPath A C),
      A.fan = Φ ∧ A.hom ≍ p₀ ∧ C.fan = Ω ∧ C.hom ≍ p₃ ∧
      path.vertices = [A, A₁, A₂, C] ∧
      A₁.hom.toRationalMap ≍ p₀.toRationalMap.comp μ₀[c] ∧
      A₂.hom.toRationalMap ≍ (p₀.toRationalMap.comp μ₀[c]).comp μ₁[d] ∧
      path.rationalMap ≍ (μ₀[c].comp μ₁[d]).comp τ.toFanHom.algebraicMap.toRationalMap := by
  obtain ⟨hp₀, hp₁, hp₂, hp₃⟩ := hpoles
  let A : LogarithmicProjection i D := ⟨Φ, hΦ, hc, p₀, inferInstance, inferInstance, hp₀⟩
  let A₁ : LogarithmicProjection i D := ⟨Ψ, hΨ, hcΨ, p₁, inferInstance, inferInstance, hp₁⟩
  let A₂ : LogarithmicProjection i D := ⟨Ω, hΩ, hcΩ, p₂, inferInstance, inferInstance, hp₂⟩
  let C : LogarithmicProjection i D := ⟨Ω, hΩ, hcΩ, p₃, inferInstance, inferInstance, hp₃⟩
  let e₁ : SarkisovStep A A₁ := ⟨μ₀[c], .mutation b (r 0) c opp₀, h₁⟩
  let e₂ : SarkisovStep A₁ A₂ := ⟨μ₁[d], .mutation b (s 2) d opp₁, h₂⟩
  have hτ : Fan.IsSarkisovLink τ.toFanHom.algebraicMap.toRationalMap := by
    simpa only [Fan.torusTranslation_one, Iso.refl_hom, Category.comp_id] using
      Fan.IsSarkisovLink.toricIso τ 1
  have hComp : p₂.toRationalMap.comp τ.toFanHom.algebraicMap.toRationalMap = p₃.toRationalMap := by
    rw [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom, h₃]
  let e₃ : SarkisovStep A₂ C := ⟨τ.toFanHom.algebraicMap.toRationalMap, hτ, hComp⟩
  have hSecond : p₂.toRationalMap = (p₀.toRationalMap.comp μ₀[c]).comp μ₁[d] := by
    simp only [h₁, h₂]
  refine ⟨A, A₁, A₂, C, ((Quiver.Hom.toPath e₁).cons e₂).cons e₃,
    rfl, HEq.rfl, rfl, HEq.rfl, ?_, heq_of_eq h₁.symm, heq_of_eq hSecond, ?_⟩
  · simp only [Quiver.Path.vertices_cons, Quiver.Path.vertices_toPath, List.concat_eq_append,
      List.cons_append, List.nil_append]
  · exact heq_of_eq (by
      simp only [Quiver.Hom.toPath, SarkisovPath.rationalMap_cons, SarkisovPath.rationalMap_nil,
        e₁, e₂, e₃, Scheme.RationalMap.id_comp])

/-- Two smooth high-order centers on opposite sections of a logarithmic
quadric-to-plane resolution give a resolved, degree-decreasing Sarkisov path.
Its intermediate projections are the two successive mutations at the specified
centers, and its composite ends with the ruling exchange. The terminal projection
is identified with a new quadric tower carrying the transported map to the plane
and pole ideal. The two selected orders are measured against the fiber degree
in the exchanged ruling. -/
theorem exists_sarkisov_path_decrease_of_quadric_two_smooth_centers
    [X[Φ].IsProjectiveOver ℂ] {n : ℕ} {T : BlowupTower X[Φ] (n + 2) Y}
    (hT : IsClosedPointTower X[Φ] T) (g : Y ⟶ P) (hg : g ≫ fP = T.toBase ≫ f[Φ])
    (hbir : Scheme.BirationalOver g (𝟙 P)) (c d : ℂˣ) (j : Fin (n + 2)) (l : Fin (n + 1))
    (hj : hT.baseCenter j = center[r 0,c]) (hl : hT.baseCenter (j.succAbove l) = center[r 2,d])
    (hjfirst : ∀ k < j, hT.baseCenter k ≠ center[r 0,c])
    (hlfirst : ∀ k < j.succAbove l, hT.baseCenter k ≠ center[r 2,d])
    (D : Y.IdealSheafData) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : Nonempty (Ψ).cones := Fan.IsComplete.nonempty_cones hcΨ
    let : Nonempty (Ω).cones := Fan.IsComplete.nonempty_cones hcΩ
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : SmoothOfRelativeDimension 2 f[Ω] :=
      rankTwo ▸ (Ω).smoothOfRelativeDimension_algebraicRealizationStructureMap hΩ
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : T.toBase.IsOver S := ⟨rfl⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : IsIntegral Y := hT.isIntegral f[Φ]
    let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f[Φ]
    let x := (T.picardMarking hT f[Φ]).symm (Additive.ofMul (pullback g H))
    let β := (Φ.hirzebruchPicardBasis b 0 hΦ r hr).repr x.1 0
    let orders := fun k ↦ -x.2 k
    B[Φ,hc].comap T.toBase = D * ramificationIdealSheaf ℂ T.toBase →
    β < 2 * orders j → β < 2 * orders (j.succAbove l) →
    (∀ k, k ≠ j → k ≠ j.succAbove l → 2 * orders k ≤ β) →
    ∃ (a : Basis (Fin 2) ℤ N)
      (ht : (fun k ↦ ((t) k).primitiveGenerator) = ![a 0, a 1, -a 0, (0 : ℤ) • a 0 - a 1])
      (Z : Scheme) (U : BlowupTower X[Ω] (1 + (1 + n)) Z) (hU : IsClosedPointTower X[Ω] U)
      (e : Y ≅ Z) (A A₁ A₂ C : LogarithmicProjection i D) (path : SarkisovPath A C),
      let τ := Fan.quadricRulingExchange a hΩ hcΩ t ht
      let g' := e.inv ≫ g
      let y := (U.picardMarking hU f[Ω]).symm (Additive.ofMul (pullback g' H))
      let β' := ((Ω).hirzebruchPicardBasis a 0 hΩ t ht).repr y.1 1
      A.fan = Φ ∧ A.hom ≍ T.toBase ∧ C.fan = Ω ∧ C.hom ≍ e.hom ≫ U.toBase ∧
      path.vertices = [A, A₁, A₂, C] ∧
      A₁.hom.toRationalMap ≍ T.toBase.toRationalMap.comp μ₀[c] ∧
      A₂.hom.toRationalMap ≍ (T.toBase.toRationalMap.comp μ₀[c]).comp μ₁[d] ∧
      path.rationalMap ≍ (μ₀[c].comp μ₁[d]).comp τ.toFanHom.algebraicMap.toRationalMap ∧
      X[Ω].IsProjectiveOver ℂ ∧
      g' ≫ fP = U.toBase ≫ f[Ω] ∧ Scheme.BirationalOver g' (𝟙 P) ∧
      B[Ω,hcΩ].comap U.toBase = D.comap e.inv * hU.ramificationIdealSheafToBase ℂ ∧
      0 < β' ∧
      hirzebruchSarkisovBidegree β'.toNat (∑ k, -y.2 k).toNat <
        hirzebruchSarkisovBidegree β.toNat (∑ k, orders k).toNat := by
  intro hcones₀ hcones₁ hcones₂ hdim₀ hdim₂ hY hOver hdimY hSmooth hIntegral hMod
    x β orders hpole hjhigh hlhigh hsmall
  let := hcones₀
  let := hcones₁
  let := hcones₂
  let := hdim₀
  let := hdim₂
  let := hY
  let := hOver
  let := hdimY
  let := hSmooth
  let := hIntegral
  let := hMod
  have hUpper := hT.base_order_le_quadric_exchanged_fiber_degree b hΦ hc r hr g hg
  have hNonneg := (hT.hirzebruch_resolution_degree_bounds b 0 hΦ hc r hr g hg hbir).2.2
  obtain ⟨a, ht, Z, U, hU, e, W, V₀, hV, k, h₁, h₂, h₃, hg', hbir', hpoles, hcoords⟩ :=
    hT.exists_quadric_resolution_of_two_smooth_high_centers b hΦ hc r hr g hg hbir c d j l
      hj hl hjfirst hlfirst hjhigh (hUpper j) hlhigh (hUpper (j.succAbove l))
      (fun u hu hu' ↦ ⟨hNonneg u, hsmall u hu hu'⟩)
  let τ := Fan.quadricRulingExchange a hΩ hcΩ t ht
  let q := V₀.transport (asIso τ.toFanHom.algebraicMap)
  let E := e ≪≫ k ≪≫ q.iso
  let : SmoothOfRelativeDimension 2 f[Ψ] :=
    rankTwo ▸ (Ψ).smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
  let : IsModification U.toBase := hU.isModification_of_smoothOfRelativeDimension_two f[Ψ]
  let : IsModification V₀.toBase := hV.isModification_of_smoothOfRelativeDimension_two f[Ω]
  let hQ := q.isLift.isClosedPointTower hV
  let : IsModification q.tower.toBase :=
    hQ.isModification_of_smoothOfRelativeDimension_two f[Ω]
  obtain ⟨hOver₁, hOver₂, hOver₃, hPole⟩ := hpoles D
  let := hOver₁
  let := hOver₂
  let := hOver₃
  obtain ⟨hp₁, hp₂, hp₃, hpQ⟩ := hPole hpole
  obtain ⟨A, A₁, A₂, C, path, hFan₀, hHom₀, hFan₃, hHom₃, hVertices, hFirst, hSecond, hMap⟩ :=
    exists_two_smooth_center_path b hΦ hc r hr c d τ T.toBase (e.hom ≫ U.toBase)
      (e.hom ≫ k.hom ≫ V₀.toBase) (E.hom ≫ q.tower.toBase) h₁ h₂ h₃ ⟨hpole, hp₁, hp₂, hp₃⟩
  let : X[Ψ].IsProjectiveOver ℂ := (r 0).isProjectiveOver_mutationFan b opp₀ hΦ
  have hProjective : X[Ω].IsProjectiveOver ℂ := (s 2).isProjectiveOver_mutationFan b opp₁ hΨ
  obtain ⟨-, -, -, -, -, hβ', hlt⟩ := hcoords
  exact ⟨a, ht, _, q.tower, hQ, E, A, A₁, A₂, C, path, hFan₀, hHom₀, hFan₃, hHom₃, hVertices,
    hFirst, hSecond, hMap, hProjective, hg', hbir', hpQ, hβ', hlt⟩

end QPainleve.BlowupTower.IsClosedPointTower
