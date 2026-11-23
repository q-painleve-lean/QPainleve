/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Transport
public import QPainleve.Geometry.Toric.Fan.Evaluation

import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Reorder
import QPainleve.AlgebraicGeometry.RationalMap.Composition

/-!
# Marked reindexing of toric blowups

Changing the toric lattice frame and reindexing the ordered centers gives an
isomorphism identifying the strict boundaries, the total exceptional classes, and
fixed-center X evaluation. Repeated centers give chains of infinitely near centers.
The noncollision condition applies to pairs whose order is reversed.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module Multiplicative
open QPainleve.BlowupTower TauCeti.AlgebraicGeometry TauCeti.LaurentRing LineBundleClass

namespace TauCeti.Toric.FanEquiv

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  [h₀ : Nonempty Φ.cones] {n : ℕ}
  (e : FanEquiv Φ Ψ) (b : Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)
  (χ : Multiplicative (Fin n → ℤ) →* ℂˣ) (σ : Equiv.Perm (Fin n))

local notation "b′" => b.map e.latticeEquiv.toIntLinearEquiv
local notation "t" => e.rayEquiv ∘ s ∘ σ
local notation "χ′" => MonoidHom.comp χ (AddMonoidHom.toMultiplicative
  (LinearMap.toAddMonoidHom (LinearEquiv.toLinearMap (LinearEquiv.funCongrLeft ℤ ℤ σ.symm))))
local notation "d" => fun j : Fin n ↦ χ (ofAdd (Pi.single j 1))
local notation "A" => Fan.internalBlowupTower b s (d)
local notation "B" => Fan.internalBlowupTower (b′) (t) ((d) ∘ σ)
local notation "πA" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd (A)))
local notation "πB" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd (B)))
local notation "φ" => e.toFanHom.algebraicMap

/-- A fan equivalence transports the ordered blowups in the carried lattice frame.
If every pair of centers whose order is reversed has distinct ray-parameter pairs,
the same isomorphism identifies the strict boundaries, the full Picard markings,
and fixed-center X evaluation after renaming the independent X coordinates. -/
theorem exists_iso_reindex_internalBlowupPicardMarking (hΦ : Φ.IsRegular)
    (h : ∀ a b, a < b → σ b < σ a → (s (σ a), (d) (σ a)) ≠ (s (σ b), (d) (σ b))) :
    letI : Nonempty Ψ.cones := h₀.map e.coneEquiv
    let hΨ := e.isRegular_iff.mpr hΦ
    letI := Fan.isIntegral_internalBlowupTower b s (d) hΦ
    letI := Fan.isModification_internalBlowupTower_toBase b s (d) hΦ
    letI := Fan.isModification_internalBlowupTower_toBase (b′) (t) ((d) ∘ σ) hΨ
    ∃ g : (A).1 ≅ (B).1,
      g.hom ≫ πB = πA ≫ φ ∧
      (A).2.boundaryι ≫ g.hom = (e.boundaryIso h₀ inferInstance).hom ≫ (B).2.boundaryι ∧
      (∀ (a : Additive (LineBundleClass Ψ.algebraicRealization)) (x : Fin n → ℤ),
        pullback g.hom (Fan.internalBlowupPicardMarking (b′) (t) ((d) ∘ σ) hΨ (a, x)).toMul =
        (Fan.internalBlowupPicardMarking b s (d) hΦ
          (Additive.ofMul (pullback φ a.toMul), x ∘ σ.symm)).toMul) ∧
      (g.hom ≫ πB).toRationalMap.comp (Ψ.xEvaluation (b′) (t) (χ′)) =
        ((πA).toRationalMap.comp (Φ.xEvaluation b s χ)).compHom
          (Spec.map (CommRingCat.ofHom (rename (R := ℂ) σ).toRingHom)) := by
  let : Nonempty Ψ.cones := h₀.map e.coneEquiv
  let hΨ := e.isRegular_iff.mpr hΦ
  let := Fan.isIntegral_internalBlowupTower b s (d) hΦ
  let := Fan.isModification_internalBlowupTower_toBase b s (d) hΦ
  let := Fan.isModification_internalBlowupTower_toBase (b′) (t) ((d) ∘ σ) hΨ
  let J (j : Fin n) := (s j).internalCenter b ((d) j)
  have hd (a b : Fin n) (hab : a < b) (hba : σ b < σ a) :
      Disjoint ((J (σ a)).val.support : Set (Φ.boundaryIdeal h₀).subscheme)
        ((J (σ b)).val.support : Set _) := by
    simpa only [J, Scheme.IdealSheafData.map_id] using
      (Fan.disjoint_support_map_internalCenter_iff _ (𝟙 _) _ _ _ _).mpr (h a b hab hba)
  have hm := exists_iso_alongBoundary_reindex_of_disjoint_inversions
    (i := (Φ.boundaryIdeal h₀).subschemeι) J σ hd
  have hJ : J ∘ σ = (fun j ↦ ((s ∘ σ) j).internalCenter b (((d) ∘ σ) j)) := rfl
  dsimp only at hm
  rw [hJ] at hm
  rw [← Fan.internalBlowupTower_eq_alongBoundary b s (d),
    ← Fan.internalBlowupTower_eq_alongBoundary b (s ∘ σ) ((d) ∘ σ)] at hm
  obtain ⟨f, hf, hfB, hmark⟩ := hm
  obtain ⟨f', ⟨hf', hf'B⟩, -⟩ := e.existsUnique_isLift_internalBlowupTower b (b′)
    (b.detDualEquiv_map e.latticeEquiv.toIntLinearEquiv) (s ∘ σ) ((d) ∘ σ) hΦ
  have hproj : (f ≪≫ f').hom ≫ πB = πA ≫ φ := by
    rw [Iso.trans_hom, Category.assoc, hf'.hom_toBase, asIso_hom, ← Category.assoc, hf]
  refine ⟨f ≪≫ f', hproj, ?_, ?_, ?_⟩
  · rw [Iso.trans_hom, ← Category.assoc, hfB, hf'B]
  · intro a x
    simp only [Iso.trans_hom, Fan.internalBlowupPicardMarking_apply]
    rw [← pullback_comp, hf'.pullback_picardHom]
    have hx : (x ∘ σ.symm) ∘ σ = x := by ext j; simp
    simpa only [asIso_hom, hx] using hmark (Additive.ofMul (pullback φ a.toMul)) (x ∘ σ.symm)
  · have hcomp : (πA ≫ φ).toRationalMap = (πA).toRationalMap.comp (φ).toRationalMap := by
      rw [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom]
    simp only [hproj, hcomp, Scheme.RationalMap.comp_assoc, e.comp_xEvaluation b s σ χ,
      Scheme.RationalMap.comp_compHom]

end TauCeti.Toric.FanEquiv
