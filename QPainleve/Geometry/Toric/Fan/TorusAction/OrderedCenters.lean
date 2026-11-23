/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import QPainleve.Geometry.Toric.Fan.Picard.BoundaryQuotient
public import QPainleve.Geometry.Toric.Fan.Picard.Translation
public import QPainleve.Geometry.Toric.Fan.TorusAction.Boundary

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.Geometry.Toric.CharacterTorus.CenterAlignment
import TauCeti.Algebra.Group.FreeAbelianCharacter

/-!
# Translations of ordered internal toric blowups

A torus translation lifts through the ordered towers exactly when it matches
the binomial parameters at each label. The lift matches the strict boundaries
and preserves the Picard coordinates. The charge kernel then gives the
criterion for the existence of a translating lift. Repeated parameters are
allowed, so the construction includes infinitely near centers.

This is the center alignment used in Gross, Hacking and Keel, *Moduli of
surfaces with an anti-canonical cycle*, Proposition 2.6 and Corollary 2.10.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]

local notation "Chars" => (Multiplicative (N →+ ℤ) →* ℂˣ)
local notation "boundary" => Φ.boundaryIdeal h₀

variable (b : Module.Basis (Fin 2) ℤ N) {n : ℕ}
  (s : Fin n → Φ.Ray) (c d : Fin n → ℂˣ)

local notation "P(" a ")" => internalBlowupTower b s a
local notation "T(" a ")" => WithBoundary.toTower (Sigma.snd (P(a)))
local notation "m(" j ")" =>
  LinearMap.toAddMonoidHom (b.detDualEquiv (Ray.primitiveGenerator (s j)))

/-- A prescribed translation lifts through the ordered internal blowups exactly when
its character values transport every labeled parameter. -/
theorem exists_isLift_internalBlowupTower_torusTranslation_iff (χ : Chars) :
    (∃ g : (P(c)).1 ≅ (P(d)).1, IsLift (Φ.torusTranslation χ) T(c) T(d) g) ↔
      ∀ j, d j * χ (ofAdd m(j)) = c j := by
  let Liftable (L R : Σ Y, WithBoundary (boundary).subschemeι n Y) :=
    ∃ g : L.1 ≅ R.1, IsLift (Φ.torusTranslation χ) L.2.toTower R.2.toTower g
  suffices Liftable (P(c)) (P(d)) ↔ ∀ j, d j * χ (ofAdd m(j)) = c j from this
  rw [internalBlowupTower_eq_alongBoundary, internalBlowupTower_eq_alongBoundary]
  constructor
  · rintro ⟨g, hg⟩ j
    have h := (hg.alongBoundary (boundaryTranslation χ)
      (boundaryι_comp_torusTranslation_hom χ)).1 j
    rw [(s j).comap_internalCenter_boundaryTranslation_hom b] at h
    exact (s j).internalCenter_injective b h
  · intro h
    obtain ⟨g, hg, _⟩ := exists_isLift_alongBoundary (Φ.torusTranslation χ)
      (boundaryTranslation χ) (boundaryι_comp_torusTranslation_hom χ)
      (fun j ↦ (s j).internalCenter b (c j)) (fun j ↦ (s j).internalCenter b (d j))
      (fun j ↦ by rw [(s j).comap_internalCenter_boundaryTranslation_hom b, h j])
    exact ⟨g, hg⟩

/-- Any translating lift restricts on the strict boundary to the original boundary
translation under the canonical embeddings. -/
@[reassoc]
theorem boundaryι_comp_of_isLift_internalBlowupTower_torusTranslation (χ : Chars)
    {g : (P(c)).1 ≅ (P(d)).1} (hg : IsLift (Φ.torusTranslation χ) T(c) T(d) g) :
    (P(c)).2.boundaryι ≫ g.hom = (boundaryTranslation χ).hom ≫ (P(d)).2.boundaryι := by
  let Preserves (L R : Σ Y, WithBoundary (boundary).subschemeι n Y) :=
    ∀ (g : L.1 ≅ R.1), IsLift (Φ.torusTranslation χ) L.2.toTower R.2.toTower g →
      L.2.boundaryι ≫ g.hom = (boundaryTranslation χ).hom ≫ R.2.boundaryι
  suffices Preserves (P(c)) (P(d)) from this g hg
  rw [internalBlowupTower_eq_alongBoundary, internalBlowupTower_eq_alongBoundary]
  intro g hg
  exact (hg.alongBoundary (boundaryTranslation χ) (boundaryι_comp_torusTranslation_hom χ)).2

/-- A translating lift of ordered internal blowups is an isomorphism over the complex base. -/
theorem hom_comp_internalBlowupTower_structureMap_of_isLift_torusTranslation (χ : Chars)
    {g : (P(c)).1 ≅ (P(d)).1} (hg : IsLift (Φ.torusTranslation χ) T(c) T(d) g) :
    g.hom ≫ (T(d)).toBase ≫ Φ.algebraicRealizationStructureMap =
      (T(c)).toBase ≫ Φ.algebraicRealizationStructureMap := by
  rw [hg.hom_toBase_assoc]
  exact Category.assoc _ _ _ |>.trans
    (congrArg ((T(c)).toBase ≫ ·)
      (HomIsOver.comp_over (f := (Φ.torusTranslation χ).hom) (S := Spec (.of ℂ))))

/-- The pullback by a translating lift sends each marked class to the class with
the same toric and total exceptional coordinates. -/
theorem pullback_internalBlowupPicardMarking_of_isLift_torusTranslation
    (hΦ : Φ.IsRegular) (χ : Chars)
    {g : (P(c)).1 ≅ (P(d)).1} (hg : IsLift (Φ.torusTranslation χ) T(c) T(d) g)
    (a : Additive (LineBundleClass Φ.algebraicRealization) × (Fin n → ℤ)) :
    LineBundleClass.pullback g.hom (internalBlowupPicardMarking b s d hΦ a).toMul =
      (internalBlowupPicardMarking b s c hΦ a).toMul := by
  obtain ⟨a, z⟩ := a
  simpa only [internalBlowupPicardMarking_apply, pullback_torusTranslation_eq hΦ,
    ofMul_toMul] using hg.pullback_picardHom a z

/-- Two ordered center tuples admit a translating lift exactly when they define
the same character on the integral charge kernel. -/
theorem exists_translation_lift_internalBlowupTower_iff :
    (∃ (χ : Chars) (g : (P(c)).1 ≅ (P(d)).1),
      IsLift (Φ.torusTranslation χ) T(c) T(d) g) ↔
      ∀ x ∈ (rayChargeMap s).ker, (∏ j, c j ^ x j) = ∏ j, d j ^ x j := by
  let e := Finsupp.linearEquivFunOnFinite ℤ ℤ (α := Fin n)
  let v := ((rayChargeMap s).comp e.toLinearMap).toAddMonoidHom
  let κ := freeAbelianCharEquiv (σ := Fin n) (M := ℂˣ)
  let B := ((b.detDualEquiv).trans (addMonoidHomLequivInt ℤ).symm).toAddEquiv.toMultiplicative
  have hv (j : Fin n) : v (Finsupp.single j 1) = (s j).primitiveGenerator := by
    simp [v, e]
  have hcoord (χ : Chars) :
      κ.symm d * (χ.comp B.toMonoidHom).comp v.toMultiplicative = κ.symm c ↔
        ∀ j, d j * χ (ofAdd m(j)) = c j := by
    rw [← κ.injective.eq_iff, funext_iff]
    simp [κ, B, hv, freeAbelianCharEquiv_apply]
  have hker :
      (∀ x ∈ v.ker, κ.symm d (ofAdd x) = κ.symm c (ofAdd x)) ↔
        ∀ x ∈ (rayChargeMap s).ker, (∏ j, c j ^ x j) = ∏ j, d j ^ x j := by
    refine Iff.trans ?_ (e.surjective.forall (p := fun x ↦ x ∈ (rayChargeMap s).ker →
      (∏ j, c j ^ x j) = ∏ j, d j ^ x j)).symm
    simp [κ, v, e, AddMonoidHom.mem_ker, LinearMap.mem_ker,
      freeAbelianCharEquiv_symm_apply_ofAdd, Finsupp.prod_fintype, eq_comm]
  rw [← hker, ← QPainleve.CharacterTorus.exists_center_translation_iff]
  constructor
  · rintro ⟨χ, g, hg⟩
    exact ⟨χ.comp B.toMonoidHom, (hcoord χ).mpr
      ((exists_isLift_internalBlowupTower_torusTranslation_iff b s c d χ).mp ⟨g, hg⟩)⟩
  · rintro ⟨z, hz⟩
    let χ := z.comp B.symm.toMonoidHom
    have hχ : χ.comp B.toMonoidHom = z := MonoidHom.ext fun x ↦ by simp [χ]
    obtain ⟨g, hg⟩ := (exists_isLift_internalBlowupTower_torusTranslation_iff b s c d χ).mpr
      ((hcoord χ).mp (by simpa only [hχ] using hz))
    exact ⟨χ, g, hg⟩

end TauCeti.Toric.Fan
