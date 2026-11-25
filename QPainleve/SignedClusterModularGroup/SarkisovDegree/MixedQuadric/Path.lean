/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.MixedQuadric.Basic

import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower

/-!
# Resolved Sarkisov path for a quadric corner and smooth center

The mixed quadric block gives a path on the original resolving surface. Its
toric portion passes through the common subdivision, and its two remaining
links are the binomial mutation and the ruling exchange. The endpoint
projection and its Picard coordinates agree with the returned point tower,
so the degree induction can continue there. The geometric inputs are
`exists_quadric_resolution_of_corner_and_smooth_centers` and
`LogarithmicProjection.exists_resolved_toric_star_factorization`.

This is the mixed two-center case of [Lutz's Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra TauCeti.Toric
open Fan (LogarithmicProjection)
open Fan.LogarithmicProjection
open scoped Sarkisov

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Φ "]" => Fan.algebraicRealization Φ
local notation "f[" Φ "]" => (X[Φ] ↘ S)
local notation "B[" Φ "," hc "]" => Fan.boundaryIdeal Φ (Fan.IsComplete.nonempty_cones hc)
local notation "R[" p "]" => ramificationIdealSheaf ℂ p
local notation "π[" s "]" => FanHom.algebraicMap (Fan.IsSubdivision.toFanHom s)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "pt" => IsLocalRing.closedPoint ℂ
local notation "dim(" b ")" =>
  Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "center[" b "," ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ dim(b)
    (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c pt
local notation "C[" b "," e "," h "," r "," hr "]" => Fan.hirzebruchPicardBasis b e h r hr

section Path

variable {Y : Scheme} [Y.Over S] [SmoothOfRelativeDimension 2 (Y ↘ S)] [IsIntegral Y]
  {D : Y.IdealSheafData} (A : LogarithmicProjection i D)

private theorem exists_mixed_quadric_path {F Ψ : Fan i} (hF : F.IsRegular)
    (s : F.IsSubdivision A.fan) (t : F.IsSubdivision Ψ)
    (q : Y ⟶ X[F]) [IsDominant q] (hs : q ≫ π[s] = A.hom)
    (d : Basis (Fin 2) ℤ N) (ρ : Ψ.Ray) (c : ℂˣ)
    (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Ψ.cones)
    (hcΨ : Ψ.IsComplete)
    (L : LogarithmicProjection i D) (hL : L.fan = Ψ) (hLt : L.hom ≍ q ≫ π[t])
    (M B : LogarithmicProjection i D) :
    let : Nonempty Ψ.cones := hcΨ.nonempty_cones
    let : Nonempty F.cones := (t.isComplete_iff.mpr hcΨ).nonempty_cones
    let Θ := Ψ.mutationFan d ρ.primitiveGenerator_ne_zero ρ.hull_primitiveGenerator_mem hOpp
    M.fan = Θ → B.fan = Θ →
    ∀ (τ : FanEquiv Θ Θ) (p : Y ⟶ X[Θ]), M.hom ≍ p →
      (q ≫ π[t]).toRationalMap.comp
        ((Ψ.mutationPartialMap d (c : ℂ) ρ.primitiveGenerator_ne_zero
          ρ.hull_primitiveGenerator_mem hOpp).toRationalMap) ≍ M.hom.toRationalMap →
      p ≫ τ.toFanHom.algebraicMap ≍ B.hom →
      Nonempty (SarkisovPath A B) := by
  intro hconesΨ hconesF Θ hM hB τ p hMp hμ hτ
  let := hconesΨ
  let := hconesF
  obtain ⟨Λ, hΛreg, hΛcomp, f, hfOver, hfDom, hfPole⟩ := L
  obtain ⟨Ω, hΩreg, hΩcomp, g, hgOver, hgDom, hgPole⟩ := M
  obtain ⟨Ω', hΩ'reg, hΩ'comp, g', hg'Over, hg'Dom, hg'Pole⟩ := B
  dsimp only at hL hM hB hLt hMp hμ hτ
  subst Λ Ω Ω'
  obtain rfl : f = q ≫ π[t] := eq_of_heq hLt
  obtain rfl : g = p := eq_of_heq hMp
  let L : LogarithmicProjection i D := ⟨Ψ, hΛreg, hΛcomp, _, hfOver, hfDom, hfPole⟩
  let M : LogarithmicProjection i D := ⟨Θ, hΩreg, hΩcomp, g, hgOver, hgDom, hgPole⟩
  let B : LogarithmicProjection i D := ⟨Θ, hΩ'reg, hΩ'comp, g', hg'Over, hg'Dom, hg'Pole⟩
  let : Nonempty Θ.cones := hΩcomp.nonempty_cones
  let : Nonempty M.fan.cones := hΩcomp.nonempty_cones
  obtain ⟨path, -, -⟩ := A.exists_resolved_toric_star_factorization L dim(d) hF s t q hs rfl
  let mutation : SarkisovStep L M :=
    ⟨_, .mutation d ρ c hOpp, eq_of_heq hμ⟩
  have hIso : Fan.IsSarkisovLink τ.toFanHom.algebraicMap.toRationalMap := by
    simpa only [Fan.torusTranslation_one, Iso.refl_hom, Category.comp_id] using
      (Fan.IsSarkisovLink.toricIso τ 1)
  let exchange : SarkisovStep M B :=
    ⟨_, hIso, by
      rw [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom]
      exact congrArg Scheme.Hom.toRationalMap (eq_of_heq hτ)⟩
  exact ⟨((SarkisovPath.ofStar path).cons mutation).cons exchange⟩

end Path

variable {Φ : Fan i}
  (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun k ↦ (r k).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
  (σ : Φ.cones) (hσ : σ.val = hull ℝ (Set.range (i ∘ b)))
  {n : ℕ} {Y : Scheme} {T : BlowupTower X[Φ] (n + 2) Y} (hT : IsClosedPointTower X[Φ] T)
  (g : Y ⟶ P)

local notation "C₀" => C[b,0,hΦ,r,hr]

include hσ in
/-- The first centers over a corner and a smooth point of the opposite section
give a Sarkisov path on the specified resolution. The input quadric is marked in
the exchanged ruling. The returned quadric tower resolves the same map to the target plane
and its projection agrees with the last vertex of the path. The Picard
coordinates record the two reverse pivots and the order of the retained
centers, including infinitely near centers. The terminal fiber degree is the sum of
the original two ruling coefficients minus the two selected orders. -/
theorem exists_sarkisov_path_of_quadric_corner_and_smooth_centers
    (hg : g ≫ (P ↘ S) = T.toBase ≫ f[Φ]) (hbir : Scheme.BirationalOver g (𝟙 P))
    (j l : Fin (n + 2))
    (hj : hT.baseCenter j = Φ.distinguishedPointHom σ pt)
    (hjfirst : ∀ k < j, hT.baseCenter k ≠ Φ.distinguishedPointHom σ pt)
    (c : ℂˣ) (hl : hT.baseCenter l = center[b,r 2,c])
    (hlfirst : ∀ k < l, hT.baseCenter k ≠ center[b,r 2,c]) {D : Y.IdealSheafData} :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] := by
      rw [Φ.algebraicRealization_over, ← dim(b)]
      exact Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : IsIntegral Y := hT.isIntegral f[Φ]
    let x := (T.picardMarking hT f[Φ]).symm (Additive.ofMul (pullback g H))
    let β := (C₀).repr x.1 0
    let a := (C₀).repr x.1 1
    let m := fun k ↦ -x.2 k
    ∀ (A : LogarithmicProjection i D), A.fan = Φ → A.hom ≍ T.toBase →
    ∃ (B : LogarithmicProjection i D) (_ : SarkisovPath A B)
      (b' : Basis (Fin 2) ℤ N) (r' : Fin 4 ≃ B.fan.Ray)
      (hr' : (fun k ↦ (r' k).primitiveGenerator) = ![b' 0, b' 1, -b' 0, (0 : ℤ) • b' 0 - b' 1])
      (W : Scheme) (U : BlowupTower X[B.fan] (1 + (1 + n)) W)
      (hU : IsClosedPointTower X[B.fan] U) (e : Y ≅ W) (l' : Fin (n + 1)),
      j.succAbove l' = l ∧ B.hom = e.hom ≫ U.toBase ∧ X[B.fan].IsProjectiveOver ℂ ∧
      let g' := e.inv ≫ g
      g' ≫ (P ↘ S) = U.toBase ≫ f[B.fan] ∧ Scheme.BirationalOver g' (𝟙 P) ∧
      let : SmoothOfRelativeDimension 2 f[B.fan] := by
        rw [B.fan.algebraicRealization_over, ← dim(b)]
        exact B.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap B.isRegular
      B[B.fan,B.isComplete].comap U.toBase = D.comap e.inv * hU.ramificationIdealSheafToBase ℂ ∧
      let y := (U.picardMarking hU f[B.fan]).symm (Additive.ofMul (pullback g' H))
      let C' := C[b',0,B.isRegular,r',hr']
      let β' := C'.repr y.1 1
      C'.repr y.1 0 = a ∧ β' = β + a - m j - m l ∧
      y.2 = Fin.addCases (fun _ : Fin 1 ↦ -a - x.2 l)
        ((Fin.addCases (fun _ : Fin 1 ↦ -a - x.2 j) (x.2 ∘ j.succAbove) :
          Fin (1 + (n + 1)) → ℤ) ∘ (l'.natAdd 1).succAbove) ∧
      0 < β' := by
  intro hcones hdim hY hdimY hIntegral x β a m A hA hAt
  let := hcones
  let := hdim
  let := hY
  let := hdimY
  let := hIntegral
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  -- Keep the supplied starting projection, using the tower's fan and morphism.
  rcases A with ⟨Δ, hΔreg, hΔcomp, f, hfOver, hfDom, hfPole⟩
  dsimp only at hA hAt
  subst Δ
  obtain rfl : f = T.toBase := eq_of_heq hAt
  let A : LogarithmicProjection i D := ⟨Φ, hΔreg, hΔcomp, _, hfOver, hfDom, hfPole⟩
  obtain ⟨Ψ, F, hΨ, hcΨ, hF, s, t, _, _, _, d, r₁, hr₁, q, Z, U, hU, e, c', l',
      _, _, hq, hq', hidx, _, _, hreturn⟩ :=
    hT.exists_quadric_resolution_of_corner_and_smooth_centers b hΦ hc r hr σ hσ
      g hg hbir j l hj hjfirst c hl hlfirst
  let ρ := r₁ (2 : Fin 4)
  let hOpp := Fan.hull_neg_primitiveGenerator_mem_of_hirzebruch_section_two d 1 r₁ hr₁
  let Θ := Ψ.mutationFan d ρ.primitiveGenerator_ne_zero ρ.hull_primitiveGenerator_mem hOpp
  let hΘ := (Ψ.isRegular_mutationFan_iff d ρ.primitiveGenerator_ne_zero
    ρ.hull_primitiveGenerator_mem hOpp).mpr hΨ
  let hcΘ := (Ψ.isComplete_mutationFan_iff d ρ.primitiveGenerator_ne_zero
    ρ.hull_primitiveGenerator_mem hOpp).mpr hcΨ
  let r₂ := r₁.trans (Ψ.mutationFanRayEquiv d ρ.primitiveGenerator_ne_zero
    ρ.hull_primitiveGenerator_mem hOpp)
  let : Nonempty Ψ.cones := hcΨ.nonempty_cones
  let : Nonempty Θ.cones := hcΘ.nonempty_cones
  let : SmoothOfRelativeDimension 2 f[Ψ] := by
    rw [Ψ.algebraicRealization_over, ← dim(d)]
    exact Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
  let : SmoothOfRelativeDimension 2 f[Θ] := by
    rw [Θ.algebraicRealization_over, ← dim(d)]
    exact Θ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΘ
  let : IsIntegral Z := hU.isIntegral f[Ψ]
  let : IsModification U.toBase := hU.isModification_of_smoothOfRelativeDimension_two f[Ψ]
  obtain ⟨b', hr₂, _, U₀, k₀, W, U', hU', k₁, hμ, hτ, hg', hbir', ha', hβ', horders, hpos,
      _, hLOver, hMOver, hBOver, hpole⟩ := hreturn
  obtain ⟨_, hLpole, hMpole, hBpole, hUpole⟩ := hpole D hfPole
  -- Read the mutation and the ruling exchange on the original resolving surface.
  let τ := Θ.quadricRulingExchange b' hΘ hcΘ r₂ hr₂
  let p := e.hom ≫ k₀.hom ≫ U₀.toBase
  let e' := e ≪≫ k₁
  let p' := e'.hom ≫ U'.toBase
  have hp' : p ≫ τ.toFanHom.algebraicMap = p' := by
    simpa only [p, p', e', Iso.trans_hom, Category.assoc] using congrArg (e.hom ≫ ·) hτ
  let : IsModification U'.toBase := hU'.isModification_of_smoothOfRelativeDimension_two f[Θ]
  let : IsDominant (p ≫ τ.toFanHom.algebraicMap) :=
    hp'.symm ▸ inferInstanceAs (IsDominant p')
  have hpDom : IsDominant p := IsModification.isDominant_of_comp p τ.toFanHom.algebraicMap
  let L : LogarithmicProjection i D :=
    ⟨Ψ, hΨ, hcΨ, e.hom ≫ U.toBase, hLOver, inferInstance, hLpole⟩
  let M : LogarithmicProjection i D := ⟨Θ, hΘ, hcΘ, p, hMOver, hpDom, hMpole⟩
  let B : LogarithmicProjection i D :=
    ⟨Θ, hΘ, hcΘ, p', by simpa only [p', e', Iso.trans_hom, Category.assoc] using hBOver,
      inferInstance, by simpa only [p', e', Iso.trans_hom, Category.assoc] using hBpole⟩
  let : Nonempty F.cones := (s.isComplete_iff.mpr hc).nonempty_cones
  let : IsModification π[s] := s.isModification_algebraicMap hΦ hF hc.nonempty_cones dim(b)
  let : IsDominant (q ≫ π[s]) := hq.symm ▸ hfDom
  let : IsDominant q := IsModification.isDominant_of_comp q π[s]
  have hμ' : (q ≫ π[t]).toRationalMap.comp
      (Ψ.mutationPartialMap d (c' : ℂ) ρ.primitiveGenerator_ne_zero
        ρ.hull_primitiveGenerator_mem hOpp).toRationalMap ≍ M.hom.toRationalMap := by
    apply heq_of_eq
    have h := congrArg (fun f ↦ e.hom.toRationalMap.comp f) hμ
    rw [← Scheme.RationalMap.comp_assoc] at h
    simpa only [hq', Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom]
      using h
  obtain ⟨path⟩ := exists_mixed_quadric_path A hF s t q hq d ρ c' hOpp hcΨ L rfl
    (heq_of_eq hq'.symm) M B rfl rfl τ p HEq.rfl hμ' (heq_of_eq hp')
  -- The transported marking computes the degree at exactly the last vertex.
  refine ⟨B, path, b', r₂, hr₂, W, U', hU', e', l', hidx, rfl,
    Θ.isProjectiveOver_quadric b' hΘ hcΘ r₂ hr₂, ?_⟩
  simpa only [e', Iso.trans_inv, Category.assoc, Fan.algebraicRealization_over] using
    And.intro hg' (And.intro hbir' (And.intro hUpole ⟨ha', hβ', horders, hpos⟩))

end QPainleve.BlowupTower.IsClosedPointTower
