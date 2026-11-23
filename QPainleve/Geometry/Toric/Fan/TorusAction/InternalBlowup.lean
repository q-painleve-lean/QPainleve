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
import TauCeti.Algebra.Group.FreeAbelianCharacter

/-!
# Center alignment on marked toric blowups

A torus translation aligning the center parameters lifts through the actual ordered
blowups and commutes with the boundary embeddings. Its pullback is the identity in
the standard Picard coordinates. This realizes the center alignment of Gross, Hacking
and Keel, *Moduli of surfaces with an anti-canonical cycle*, Proposition 2.9, on the
marked models, including repeated centers.

Conversely, any lift of a prescribed translation matches the labeled centers.
The existence of a translating lift is equivalent to agreement on the integral
charge kernel, via `CharacterTorus.exists_center_translation_iff`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]

local notation "Chars" => (Multiplicative (N →+ ℤ) →* ℂˣ)
local notation "boundary" => Φ.boundaryIdeal h₀

variable {n : ℕ} (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "Y" c:arg => Sigma.fst (internalBlowupTower b s c)
local notation "T" c:arg => WithBoundary.toTower (Sigma.snd (internalBlowupTower b s c))
local notation "ι" c:arg => WithBoundary.boundaryι (Sigma.snd (internalBlowupTower b s c))
local notation "m" i:arg => LinearMap.toAddMonoidHom (b.detDualEquiv (Ray.primitiveGenerator (s i)))

section

variable (c d : Fin n → ℂˣ)

/-- A prescribed translation lifts through the ordered internal blowups exactly when
its character values transport every labeled parameter. -/
theorem exists_isLift_internalBlowupTower_torusTranslation_iff (χ : Chars) :
    (∃ g : Y c ≅ Y d, IsLift (Φ.torusTranslation χ) (T c) (T d) g) ↔
      ∀ j, d j * χ (ofAdd (m j)) = c j := by
  let Liftable (L R : Σ Z, WithBoundary (boundary).subschemeι n Z) :=
    ∃ g : L.1 ≅ R.1, IsLift (Φ.torusTranslation χ) L.2.toTower R.2.toTower g
  suffices Liftable (internalBlowupTower b s c) (internalBlowupTower b s d) ↔
      ∀ j, d j * χ (ofAdd (m j)) = c j from this
  rw [internalBlowupTower_eq_alongBoundary, internalBlowupTower_eq_alongBoundary]
  have hcenter (j : Fin n) :
      ((s j).internalCenter b (d j)).val.comap (boundaryTranslation χ).hom =
        ((s j).internalCenter b (d j * χ (ofAdd (m j)))).val := by
    simpa only [mul_div_cancel_right] using
      (s j).comap_internalCenter_boundaryTranslation_hom b χ (d j * χ (ofAdd (m j)))
  constructor
  · rintro ⟨g, hg⟩ j
    have h := (hg.alongBoundary (boundaryTranslation χ)
      (boundaryTranslation_hom_subschemeι χ).symm).1 j
    rw [hcenter j] at h
    exact (s j).internalCenter_injective b h
  · intro h
    obtain ⟨g, hg, _⟩ := exists_isLift_alongBoundary (Φ.torusTranslation χ)
      (boundaryTranslation χ) (boundaryTranslation_hom_subschemeι χ).symm
      (fun j ↦ (s j).internalCenter b (c j)) (fun j ↦ (s j).internalCenter b (d j))
      (fun j ↦ by rw [hcenter j, h j])
    exact ⟨g, hg⟩

/-- Any translating lift restricts on the strict boundary to the original boundary
translation under the canonical embeddings. -/
@[reassoc]
theorem boundaryι_comp_of_isLift_internalBlowupTower_torusTranslation (χ : Chars)
    {g : Y c ≅ Y d} (hg : IsLift (Φ.torusTranslation χ) (T c) (T d) g) :
    ι c ≫ g.hom = (boundaryTranslation χ).hom ≫ ι d := by
  let Preserves (L R : Σ Z, WithBoundary (boundary).subschemeι n Z) :=
    ∀ (g : L.1 ≅ R.1), IsLift (Φ.torusTranslation χ) L.2.toTower R.2.toTower g →
      L.2.boundaryι ≫ g.hom = (boundaryTranslation χ).hom ≫ R.2.boundaryι
  suffices Preserves (internalBlowupTower b s c) (internalBlowupTower b s d) from
    this g hg
  rw [internalBlowupTower_eq_alongBoundary, internalBlowupTower_eq_alongBoundary]
  intro g hg
  exact (hg.alongBoundary (boundaryTranslation χ) (boundaryTranslation_hom_subschemeι χ).symm).2

/-- A translating lift of ordered internal blowups is an isomorphism over the complex base. -/
theorem hom_comp_internalBlowupTower_structureMap_of_isLift_torusTranslation (χ : Chars)
    {g : Y c ≅ Y d} (hg : IsLift (Φ.torusTranslation χ) (T c) (T d) g) :
    g.hom ≫ (T d).toBase ≫ Φ.algebraicRealizationStructureMap =
      (T c).toBase ≫ Φ.algebraicRealizationStructureMap := by
  rw [hg.hom_toBase_assoc]
  exact Category.assoc _ _ _ |>.trans
    (congrArg ((T c).toBase ≫ ·)
      (HomIsOver.comp_over (f := (Φ.torusTranslation χ).hom) (S := Spec (.of ℂ))))

/-- The pullback by a translating lift sends each marked class to the class with
the same toric and total exceptional coordinates. -/
theorem pullback_internalBlowupPicardMarking_of_isLift_torusTranslation
    (hΦ : Φ.IsRegular) (χ : Chars)
    {g : Y c ≅ Y d} (hg : IsLift (Φ.torusTranslation χ) (T c) (T d) g)
    (a : Additive (LineBundleClass Φ.algebraicRealization) × (Fin n → ℤ)) :
    LineBundleClass.pullback g.hom (internalBlowupPicardMarking b s d hΦ a).toMul =
      (internalBlowupPicardMarking b s c hΦ a).toMul := by
  obtain ⟨a, z⟩ := a
  simpa only [internalBlowupPicardMarking_apply, Φ.pullback_torusTranslation_hom hΦ,
    ofMul_toMul] using hg.pullback_picardHom a z

/-- Two ordered center tuples admit a translating lift exactly when they define
the same character on the integral charge kernel. -/
theorem exists_translation_lift_internalBlowupTower_iff :
    (∃ (χ : Chars) (g : Y c ≅ Y d),
      IsLift (Φ.torusTranslation χ) (T c) (T d) g) ↔
      ∀ x ∈ (rayChargeMap s).ker, (∏ j, c j ^ x j) = ∏ j, d j ^ x j := by
  let e := Finsupp.linearEquivFunOnFinite ℤ ℤ (α := Fin n)
  let v := ((rayChargeMap s).comp e.toLinearMap).toAddMonoidHom
  let κ := freeAbelianCharEquiv (σ := Fin n) (M := ℂˣ)
  let B := ((b.detDualEquiv).trans (addMonoidHomLequivInt ℤ).symm).toAddEquiv.toMultiplicative
  have hv (j : Fin n) : v (Finsupp.single j 1) = (s j).primitiveGenerator := by
    simp [v, e]
  have hcoord (χ : Chars) :
      κ.symm d * (χ.comp B.toMonoidHom).comp v.toMultiplicative = κ.symm c ↔
        ∀ j, d j * χ (ofAdd (m j)) = c j := by
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

end

/-- A translation with the prescribed effect on the parameters lifts uniquely through the
ordered internal blowups. The lift matches the strict-transform boundary embeddings and
fixes both coordinates of the Picard markings. -/
theorem exists_unique_internal_blowup_torus_translation (hΦ : Φ.IsRegular)
    (χ : Chars) (c d : Fin n → ℂˣ) (hd : ∀ i, d i = c i / χ (ofAdd (m i))) :
    ∃! g : Y c ≅ Y d, IsLift (Φ.torusTranslation χ) (T c) (T d) g ∧
      ι c ≫ g.hom = (boundaryTranslation χ).hom ≫ ι d ∧
      ∀ a, LineBundleClass.pullback g.hom (internalBlowupPicardMarking b s d hΦ a).toMul =
        (internalBlowupPicardMarking b s c hΦ a).toMul := by
  obtain ⟨g, hg⟩ := (exists_isLift_internalBlowupTower_torusTranslation_iff b s c d χ).mpr
    (fun i ↦ eq_div_iff_mul_eq'.mp (hd i))
  exact ⟨g, ⟨hg, boundaryι_comp_of_isLift_internalBlowupTower_torusTranslation b s c d χ hg,
    pullback_internalBlowupPicardMarking_of_isLift_torusTranslation b s c d hΦ χ hg⟩,
    fun _ h ↦ h.1.unique hg⟩

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
        ι c' ≫ g.hom = (boundaryTranslation χ).hom ≫ ι d' ∧
        ∀ a, LineBundleClass.pullback g.hom (internalBlowupPicardMarking b s d' hΦ a).toMul =
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
