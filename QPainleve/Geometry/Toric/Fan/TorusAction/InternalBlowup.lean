/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import QPainleve.Geometry.Toric.Fan.Picard.BoundaryQuotient
public import QPainleve.Geometry.Toric.Fan.TorusAction.Center

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.Geometry.Toric.CharacterTorus.CenterAlignment
import QPainleve.Geometry.Toric.Fan.Picard.Translation

/-!
# Center alignment on marked toric blowups

A torus translation aligning the center parameters lifts through the actual ordered
blowups and commutes with the boundary embeddings. Its pullback is the identity in
the standard Picard coordinates. This realizes the center alignment of Gross, Hacking
and Keel, *Moduli of surfaces with an anti-canonical cycle*, Proposition 2.9, on the
marked models, including repeated centers.

The lift uses `BlowupTower.exists_isLift_alongBoundary`. Existence of an aligning
translation uses `CharacterTorus.exists_center_translation_iff`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]

local notation "Chars" => (Multiplicative (N →+ ℤ) →* ℂˣ)

variable {n : ℕ} (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "Y" c:arg => Sigma.fst (internalBlowupTower b s c)
local notation "T" c:arg => WithBoundary.toTower (Sigma.snd (internalBlowupTower b s c))
local notation "j" c:arg => WithBoundary.boundaryι (Sigma.snd (internalBlowupTower b s c))
local notation "m" i:arg => LinearMap.toAddMonoidHom (b.detDualEquiv (Ray.primitiveGenerator (s i)))

/-- A translation with the prescribed effect on the parameters lifts uniquely through the
ordered internal blowups. The lift matches the strict-transform boundary embeddings and
fixes both coordinates of the Picard markings. -/
theorem exists_unique_internal_blowup_torus_translation (hΦ : Φ.IsRegular)
    (χ : Chars) (c d : Fin n → ℂˣ) (hd : ∀ i, d i = c i / χ (ofAdd (m i))) :
    ∃! g : Y c ≅ Y d, IsLift (Φ.torusTranslation χ) (T c) (T d) g ∧
      j c ≫ g.hom = (boundaryTranslation χ).hom ≫ j d ∧
      ∀ a, pullback g.hom (internalBlowupPicardMarking b s d hΦ a).toMul =
        (internalBlowupPicardMarking b s c hΦ a).toMul := by
  have hJ i : ((s i).internalCenter b (d i)).val.comap (boundaryTranslation χ).hom =
      ((s i).internalCenter b (c i)).val := by
    rw [hd i]
    exact (s i).comap_internalCenter_boundaryTranslation_hom b χ (c i)
  have hex : ∃ g : Y c ≅ Y d, IsLift (Φ.torusTranslation χ) (T c) (T d) g ∧
      j c ≫ g.hom = (boundaryTranslation χ).hom ≫ j d := by
    rw [internalBlowupTower_eq_alongBoundary b s c, internalBlowupTower_eq_alongBoundary b s d]
    exact exists_isLift_alongBoundary (Φ.torusTranslation χ)
      (boundaryTranslation χ) (boundaryTranslation_hom_subschemeι χ).symm
      (fun i ↦ (s i).internalCenter b (c i)) (fun i ↦ (s i).internalCenter b (d i)) hJ
  obtain ⟨g, hg, hbd⟩ := hex
  refine ⟨g, ⟨hg, hbd, ?_⟩, fun _ h ↦ h.1.unique hg⟩
  rintro ⟨a, coeff⟩
  rw [internalBlowupPicardMarking_apply, internalBlowupPicardMarking_apply,
    hg.pullback_picardHom, Φ.pullback_torusTranslation_hom hΦ, ofMul_toMul]

/-- Agreement on the charge kernel gives an aligning translation of the ordered marked
models. The lift acts by the inverse translating character on the center parameters, and
its pullback preserves both Picard coordinates. -/
theorem exists_internalBlowup_torusTranslation_of_eq_on_chargeKernel (hΦ : Φ.IsRegular)
    (c d : Multiplicative (Fin n → ℤ) →* ℂˣ)
    (h : ∀ a ∈ (rayChargeMap s).ker, c (ofAdd a) = d (ofAdd a)) :
    let c' (i : Fin n) := c (ofAdd (Pi.single i 1))
    let d' (i : Fin n) := d (ofAdd (Pi.single i 1))
    ∃ χ : Chars, (∀ i, d' i = c' i / χ (ofAdd (m i))) ∧
      ∃! g : Y c' ≅ Y d', IsLift (Φ.torusTranslation χ) (T c') (T d') g ∧
        j c' ≫ g.hom = (boundaryTranslation χ).hom ≫ j d' ∧
        ∀ a, pullback g.hom (internalBlowupPicardMarking b s d' hΦ a).toMul =
          (internalBlowupPicardMarking b s c' hΦ a).toMul := by
  obtain ⟨z, hz⟩ := (QPainleve.CharacterTorus.exists_center_translation_iff
    (rayChargeMap s).toAddMonoidHom c d).mpr h
  let e := b.detDualEquiv.trans (addMonoidHomLequivInt ℤ).symm
  let χ := (z⁻¹).comp e.symm.toAddEquiv.toMultiplicative.toMonoidHom
  have hd (i : Fin n) : d (ofAdd (Pi.single i 1)) =
      c (ofAdd (Pi.single i 1)) / χ (ofAdd (m i)) := by
    have hi := DFunLike.congr_fun hz (ofAdd (Pi.single i 1))
    have he : e ((s i).primitiveGenerator) = m i := rfl
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, AddMonoidHom.coe_toMultiplicative,
      Function.comp_apply, toAdd_ofAdd, LinearMap.toAddMonoidHom_coe, rayChargeMap_single] at hi
    simpa [χ, ← he, div_eq_mul_inv] using hi.symm
  exact ⟨χ, hd, exists_unique_internal_blowup_torus_translation b s hΦ χ _ _ hd⟩

end TauCeti.Toric.Fan
