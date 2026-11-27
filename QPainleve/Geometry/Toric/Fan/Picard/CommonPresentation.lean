/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Transport
public import QPainleve.Geometry.Toric.Fan.Picard.Reconstruction

import QPainleve.Geometry.Toric.Fan.Equiv

/-!
# Comparing toric blowup models in a common presentation

A Picard isometry matching the total exceptional and ordered strict boundary classes
determines the correspondence of the center rays. Transporting the second ordered
blowup tower to the first fan then makes the isometry the identity in the common
Picard coordinates. The parameters are retained, so the two resulting models can be
compared using their periods.

This is the reduction to a common toric model in the proof of
[Theorem 1.8 of Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public section

open AlgebraicGeometry CategoryTheory
open QPainleve.BlowupTower TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "rankTwo(" b ")" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "model[" b ", " s ", " c "]" => internalBlowupTower b s c
local notation "tower[" b ", " s ", " c "]" =>
  WithBoundary.toTower (Sigma.snd (model[b, s, c]))
local notation "mark[" b ", " s ", " c ", " h "]" => internalBlowupPicardMarking b s c h
local notation "strict[" h ", " b ", " s ", " c "]" =>
  strictRayBoundaryClass h rankTwo(b) (tower[b, s, c])
    (isClosedPointTower_internalBlowupTower b s c)

variable [h₀ : Nonempty Φ.cones] [h₁ : Nonempty Ψ.cones]
  {n : ℕ} (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
  (s : Fin n → Φ.Ray) (s' : Fin n → Ψ.Ray) (c d : Fin n → ℂˣ)
  (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)

private theorem centerRays_of_matching_strictRayClasses
    (f : FanEquiv Φ Ψ) (e : Additive (LineBundleClass (model[b', s', d]).1) →
      Additive (LineBundleClass (model[b, s, c]).1))
    (hcoord : ∀ a t, e (tower[b', s', d].picardHom (a, t)) =
      tower[b, s, c].picardHom
        (Additive.ofMul (pullback f.toFanHom.algebraicMap a.toMul), t))
    (hboundary : ∀ r, e (strict[hΨ, b', s', d] (f.rayEquiv r)) = strict[hΦ, b, s, c] r) :
    f.rayEquiv ∘ s = s' := by
  classical
  funext j
  -- The coefficient at center j is minus one precisely for the ray carrying that center.
  let r := s j
  have h := hboundary r
  simp only [← picardHom_markedBoundaryMap_single_internalBlowupTower hΨ b' s' d,
    ← picardHom_markedBoundaryMap_single_internalBlowupTower hΦ b s c,
    markedBoundaryMap_apply, hcoord, ← internalBlowupPicardMarking_apply b s c hΦ] at h
  have hcoeff := congrArg
    (fun a : Additive (LineBundleClass Φ.algebraicRealization) × (Fin n → ℤ) ↦ a.2 j)
    ((mark[b, s, c, hΦ]).injective h)
  have : s' j = f.rayEquiv (s j) := by
    by_contra hn
    simp [r, hn] at hcoeff
  exact this.symm

variable [Φ.algebraicRealization.IsProjectiveOver ℂ] [Ψ.algebraicRealization.IsProjectiveOver ℂ]

local notation "X" => Sigma.fst (model[b, s, c])
local notation "Y" => Sigma.fst (model[b', s', d])

/-- A Picard isometry of ordered internal blowups that matches the total exceptional
classes and positively numbered strict ray classes identifies the two ordered ray lists
under a unique fan equivalence. Transporting the second model to the first fan retains
its center parameters and identifies the strict boundaries. In the common Picard
coordinates, the prescribed isometry is the identity. -/
theorem exists_common_toric_presentation_of_picard_isometry
    {m : ℕ} [NeZero m] (hc : Φ.IsComplete) (hd : Ψ.IsComplete)
    (u : ZMod m ≃ Φ.Ray) (v : ZMod m ≃ Ψ.Ray)
    (hu : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ)
    (hv : ∀ j, b'.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Ψ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ)
    (e :
      letI : (X).Over S := ⟨(tower[b, s, c]).toBase ≫ (Φ.algebraicRealization ↘ S)⟩
      letI : (Y).Over S := ⟨(tower[b', s', d]).toBase ≫ (Ψ.algebraicRealization ↘ S)⟩
      letI : (X).IsProjectiveOver ℂ := (tower[b, s, c]).isProjectiveOver ℂ
      letI : (Y).IsProjectiveOver ℂ := (tower[b', s', d]).isProjectiveOver ℂ
      letI := isIntegral_internalBlowupTower b s c hΦ
      letI := isIntegral_internalBlowupTower b' s' d hΨ
      letI : SmoothOfRelativeDimension 2 (X ↘ S) :=
        smoothOfRelativeDimension_internalBlowupTower b s c hΦ
      letI : SmoothOfRelativeDimension 2 (Y ↘ S) :=
        smoothOfRelativeDimension_internalBlowupTower b' s' d hΨ
      (Chow.intersectionBilinForm ℂ Y).IsometryEquiv (Chow.intersectionBilinForm ℂ X))
    (he : ∀ j, e (Additive.ofMul (tower[b', s', d].exceptionalClass j)) =
      Additive.ofMul (tower[b, s, c].exceptionalClass j))
    (hD : ∀ j, e (strict[hΨ, b', s', d] (v j)) = strict[hΦ, b, s, c] (u j)) :
    ∃! f : FanEquiv Φ Ψ, (∀ j, f.rayEquiv (u j) = v j) ∧ f.rayEquiv ∘ s = s' ∧
      ∃ g : (model[b, s, d]).1 ≅ (model[b', s', d]).1,
        IsLift (asIso f.toFanHom.algebraicMap) (tower[b, s, d]) (tower[b', s', d]) g ∧
        (model[b, s, d]).2.boundaryι ≫ g.hom =
          (f.boundaryIso h₀ h₁).hom ≫ (model[b', s', d]).2.boundaryι ∧
        ∀ L : LineBundleClass (model[b', s', d]).1,
          (mark[b, s, c, hΦ]).symm (e (Additive.ofMul L)) =
          (mark[b, s, d, hΦ]).symm (Additive.ofMul (pullback g.hom L)) := by
  obtain ⟨f, ⟨hf, hcoord⟩, huniq⟩ :=
    existsUnique_fanEquiv_of_strictRayBoundaryClasses b b' hΦ hΨ hc hd u v hu hv
      (isClosedPointTower_internalBlowupTower b s c)
      (isClosedPointTower_internalBlowupTower b' s' d) e he hD
  have hcenters := centerRays_of_matching_strictRayClasses b b' s s' c d hΦ hΨ f e hcoord
    (fun r ↦ by obtain ⟨j, rfl⟩ := u.surjective r; rw [hf]; exact hD j)
  have hdet := f.detDualEquiv_of_matching_adjacent_rays b b' hΦ (hf 0) (hf (0 + 1))
    (hu 0).1 (hv 0).1 (hu 0).2
  have hlift := f.existsUnique_isLift_internalBlowupTower b b' hdet s d
  rw [hcenters] at hlift
  obtain ⟨g, ⟨hg, hboundary⟩, -⟩ := hlift
  refine ⟨f, ⟨hf, hcenters, g, hg, hboundary, ?_⟩, ?_⟩
  · intro L
    obtain ⟨⟨a, t⟩, h⟩ := (mark[b', s', d, hΨ]).surjective (Additive.ofMul L)
    rw [internalBlowupPicardMarking_apply] at h
    have hL : (tower[b', s', d].picardHom (a, t)).toMul = L :=
      congrArg Additive.toMul h
    rw [← h, hcoord, ← hL, hg.pullback_picardHom, ofMul_toMul,
      ← internalBlowupPicardMarking_apply b s c hΦ,
      ← internalBlowupPicardMarking_apply b s d hΦ]
    simp only [LinearEquiv.symm_apply_apply, asIso_hom]
  · intro f' hf'
    obtain ⟨hray, -, g', hg', -, hmark⟩ := hf'
    refine huniq f' ⟨hray, fun a t ↦ ?_⟩
    apply (mark[b, s, c, hΦ]).symm.injective
    have h := hmark (tower[b', s', d].picardHom (a, t)).toMul
    rw [ofMul_toMul, hg'.pullback_picardHom, ofMul_toMul, asIso_hom,
      ← internalBlowupPicardMarking_apply b s d hΦ, LinearEquiv.symm_apply_apply] at h
    rwa [← internalBlowupPicardMarking_apply b s c hΦ, LinearEquiv.symm_apply_apply]

end TauCeti.Toric.Fan
