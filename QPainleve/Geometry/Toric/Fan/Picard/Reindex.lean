/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Transport
public import QPainleve.Geometry.Toric.Fan.Evaluation

import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Reorder
import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic

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

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones] {n : ℕ}

/-- Reordering the centers preserves the strict boundary and carries the total exceptional
coordinates along the permutation, provided that coincident centers retain their order. -/
theorem exists_iso_internalBlowupPicardMarking_reindex (b : Basis (Fin 2) ℤ N)
    (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ) (hΦ : Φ.IsRegular) (σ : Equiv.Perm (Fin n))
    (h : ∀ a b, a < b → σ b < σ a → (s (σ a), c (σ a)) ≠ (s (σ b), c (σ b))) :
    let A := internalBlowupTower b s c
    let B := internalBlowupTower b (s ∘ σ) (c ∘ σ)
    ∃ e : A.1 ≅ B.1,
      e.hom ≫ B.2.toTower.toBase = A.2.toTower.toBase ∧
      A.2.boundaryι ≫ e.hom = B.2.boundaryι ∧
      ∀ (a : Additive (LineBundleClass Φ.algebraicRealization)) (x : Fin n → ℤ),
        pullback e.hom (internalBlowupPicardMarking b (s ∘ σ) (c ∘ σ) hΦ (a, x ∘ σ)).toMul =
          (internalBlowupPicardMarking b s c hΦ (a, x)).toMul := by
  let J (j : Fin n) := (s j).internalCenter b (c j)
  have hd (a b : Fin n) (hab : a < b) (hba : σ b < σ a) :
      Disjoint ((J (σ a)).val.support : Set (Φ.boundaryIdeal h₀).subscheme)
        ((J (σ b)).val.support : Set _) := by
    simpa only [J, Scheme.IdealSheafData.map_id] using
      (disjoint_support_map_internalCenter_iff _ (𝟙 _) _ _ _ _).mpr (h a b hab hba)
  have hm := exists_iso_alongBoundary_reindex_of_disjoint_inversions
    (i := (Φ.boundaryIdeal h₀).subschemeι) J σ hd
  have hJ : J ∘ σ = (fun j ↦ ((s ∘ σ) j).internalCenter b ((c ∘ σ) j)) := rfl
  dsimp only at hm
  rw [hJ, ← internalBlowupTower_eq_alongBoundary b s c,
    ← internalBlowupTower_eq_alongBoundary b (s ∘ σ) (c ∘ σ)] at hm
  simpa only [internalBlowupPicardMarking_apply] using hm

end TauCeti.Toric.Fan

namespace TauCeti.Toric.FanEquiv

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  [h₀ : Nonempty Φ.cones] {n : ℕ}
  (e : FanEquiv Φ Ψ) (b : Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "t" σ:arg => e.rayEquiv ∘ s ∘ σ
local notation "φ" => e.toFanHom.algebraicMap

/-- A determinant-preserving fan equivalence and an order-preserving matching of
coincident centers transport the strict boundary and all total exceptional coordinates. -/
theorem exists_iso_transport_internalBlowupPicardMarking
    (b' : Basis (Fin 2) ℤ N') (hΦ : Φ.IsRegular) (c : Fin n → ℂˣ)
    (σ : Equiv.Perm (Fin n))
    (hdet : ∀ x y, b'.detDualEquiv (e.latticeEquiv x) (e.latticeEquiv y) = b.detDualEquiv x y)
    (h : ∀ a b, a < b → σ b < σ a → (s (σ a), c (σ a)) ≠ (s (σ b), c (σ b))) :
    letI : Nonempty Ψ.cones := h₀.map e.coneEquiv
    let hΨ := e.isRegular_iff.mpr hΦ
    let A := Fan.internalBlowupTower b s c
    let B := Fan.internalBlowupTower b' (t σ) (c ∘ σ)
    ∃ g : A.1 ≅ B.1,
      g.hom ≫ B.2.toTower.toBase = A.2.toTower.toBase ≫ φ ∧
      A.2.boundaryι ≫ g.hom = (e.boundaryIso h₀ inferInstance).hom ≫ B.2.boundaryι ∧
      ∀ (a : Additive (LineBundleClass Ψ.algebraicRealization)) (x : Fin n → ℤ),
        pullback g.hom (Fan.internalBlowupPicardMarking b' (t σ) (c ∘ σ) hΨ (a, x)).toMul =
          (Fan.internalBlowupPicardMarking b s c hΦ
            (Additive.ofMul (pullback φ a.toMul), x ∘ σ.symm)).toMul := by
  let : Nonempty Ψ.cones := h₀.map e.coneEquiv
  obtain ⟨f, hf, hfB, hmark⟩ :=
    Fan.exists_iso_internalBlowupPicardMarking_reindex b s c hΦ σ h
  obtain ⟨f', ⟨hf', hf'B⟩, -⟩ :=
    e.existsUnique_isLift_internalBlowupTower b b' hdet (s ∘ σ) (c ∘ σ)
  refine ⟨f ≪≫ f', ?_, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, hf'.hom_toBase, asIso_hom, ← Category.assoc, hf]
  · rw [Iso.trans_hom, ← Category.assoc, hfB, hf'B]
  · intro a x
    simp only [Iso.trans_hom, Fan.internalBlowupPicardMarking_apply]
    rw [← pullback_comp, hf'.pullback_picardHom]
    have hx : (x ∘ σ.symm) ∘ σ = x := by ext j; simp
    simpa only [asIso_hom, hx, Fan.internalBlowupPicardMarking_apply] using
      hmark (Additive.ofMul (pullback φ a.toMul)) (x ∘ σ.symm)

/-- Pullback along the inverse of a reindexed toric lift, expressed in the two
ordered Picard markings. The toric class follows the inverse fan equivalence and the
exceptional coordinates follow the permutation that sends new labels to old labels. -/
theorem internalBlowupPicardMarking_symm_pullback_inv_of_reindex
    [h₁ : Nonempty Ψ.cones] (b' : Basis (Fin 2) ℤ N')
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (c c' : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n))
    (hc : c ∘ σ = c')
    (hdet : ∀ x y, b'.detDualEquiv (e.latticeEquiv x) (e.latticeEquiv y) = b.detDualEquiv x y)
    (horder : ∀ a b, a < b → σ b < σ a →
      (s (σ a), c (σ a)) ≠ (s (σ b), c (σ b)))
    (f : (Fan.internalBlowupTower b s c).1 ≅
      (Fan.internalBlowupTower b' (t σ) c').1)
    (hf : f.hom ≫ (Fan.internalBlowupTower b' (t σ) c').2.toTower.toBase =
      (Fan.internalBlowupTower b s c).2.toTower.toBase ≫ φ)
    (L : LineBundleClass (Fan.internalBlowupTower b s c).1) :
    let x := (Fan.internalBlowupPicardMarking b s c hΦ).symm (Additive.ofMul L)
    (Fan.internalBlowupPicardMarking b' (t σ) c' hΨ).symm
      (Additive.ofMul (pullback f.inv L)) =
      (Additive.ofMul (pullback e.symm.toFanHom.algebraicMap x.1.toMul), x.2 ∘ σ) := by
  have hm := e.exists_iso_transport_internalBlowupPicardMarking b s b' hΦ c σ hdet horder
  dsimp only at hm
  rw [hc] at hm
  obtain ⟨f', he, -, hmark⟩ := hm
  let ρ := t σ
  let π := (Fan.internalBlowupTower b' ρ c').2.toTower.toBase
  have := Fan.isIntegral_internalBlowupTower b s c hΦ
  have := Fan.isModification_internalBlowupTower_toBase b s c hΦ
  have : IsModification π := Fan.isModification_internalBlowupTower_toBase b' ρ c' hΨ
  have hfe : f.hom = f'.hom := π.eq_of_comp_eq_of_isModification (hf.trans he.symm)
  have happly (x : Fin n → ℤ) : (x ∘ σ) ∘ σ.symm = x := by ext j; simp
  dsimp only
  apply (Fan.internalBlowupPicardMarking b' ρ c' hΨ).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Additive.toMul.injective
  apply (pullbackEquiv f).injective
  rw [pullbackEquiv_apply, pullbackEquiv_apply, toMul_ofMul, pullback_comp, Iso.hom_inv_id,
    pullback_id, hfe, hmark]
  simp only [toMul_ofMul, pullback_comp, e.algebraicMap_comp_symm, pullback_id, happly,
    ofMul_toMul, Prod.mk.eta, LinearEquiv.apply_symm_apply]

variable (χ : Multiplicative (Fin n → ℤ) →* ℂˣ) (σ : Equiv.Perm (Fin n))

local notation "b′" => b.map e.latticeEquiv.toIntLinearEquiv
local notation "χ′" => MonoidHom.comp χ (AddMonoidHom.toMultiplicative
  (LinearMap.toAddMonoidHom (LinearEquiv.toLinearMap (LinearEquiv.funCongrLeft ℤ ℤ σ.symm))))
local notation "d" => fun j : Fin n ↦ χ (ofAdd (Pi.single j 1))
local notation "A" => Fan.internalBlowupTower b s (d)
local notation "B" => Fan.internalBlowupTower (b′) (t σ) ((d) ∘ σ)
local notation "πA" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd (A)))
local notation "πB" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd (B)))

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
    letI := Fan.isModification_internalBlowupTower_toBase (b′) (t σ) ((d) ∘ σ) hΨ
    ∃ g : (A).1 ≅ (B).1,
      g.hom ≫ πB = πA ≫ φ ∧
      (A).2.boundaryι ≫ g.hom = (e.boundaryIso h₀ inferInstance).hom ≫ (B).2.boundaryι ∧
      (∀ (a : Additive (LineBundleClass Ψ.algebraicRealization)) (x : Fin n → ℤ),
        pullback g.hom (Fan.internalBlowupPicardMarking (b′) (t σ) ((d) ∘ σ) hΨ (a, x)).toMul =
        (Fan.internalBlowupPicardMarking b s (d) hΦ
          (Additive.ofMul (pullback φ a.toMul), x ∘ σ.symm)).toMul) ∧
      (g.hom ≫ πB).toRationalMap.comp (Ψ.xEvaluation (b′) (t σ) (χ′)) =
        ((πA).toRationalMap.comp (Φ.xEvaluation b s χ)).compHom
          (Spec.map (CommRingCat.ofHom (rename (R := ℂ) σ).toRingHom)) := by
  let : Nonempty Ψ.cones := h₀.map e.coneEquiv
  let hΨ := e.isRegular_iff.mpr hΦ
  let := Fan.isIntegral_internalBlowupTower b s (d) hΦ
  let := Fan.isModification_internalBlowupTower_toBase b s (d) hΦ
  let := Fan.isModification_internalBlowupTower_toBase (b′) (t σ) ((d) ∘ σ) hΨ
  obtain ⟨g, hproj, hboundary, hpicard⟩ := e.exists_iso_transport_internalBlowupPicardMarking b s
    (b′) hΦ (d) σ (b.detDualEquiv_map e.latticeEquiv.toIntLinearEquiv) h
  refine ⟨g, hproj, hboundary, hpicard, ?_⟩
  have hcomp : (πA ≫ φ).toRationalMap = (πA).toRationalMap.comp (φ).toRationalMap := by
    rw [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom]
  simp only [hproj, hcomp, Scheme.RationalMap.comp_assoc, e.comp_xEvaluation b s σ χ,
    Scheme.RationalMap.comp_compHom]

end TauCeti.Toric.FanEquiv
