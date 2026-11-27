/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
public import QPainleve.Geometry.Toric.Fan.TorusAction.Evaluation
public import TauCeti.AlgebraicGeometry.Birational.Irreducible

import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import QPainleve.AlgebraicGeometry.Scheme.FunctionField
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced

/-!
# Translations of nodal contractions detected by X coordinates

An isomorphism between contractions of ordered toric blowup models lifts to a
translation when it identifies the scaled charge characters. The finite charge index
determines the translating character on the whole torus. The commuting projection
squares compare Picard pullback in the ordered markings.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

universe u

variable (K : Type u) [Field K] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  {n : ℕ} (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray) (c d : Fin n → Kˣ)

local notation "S" => Spec (CommRingCat.of K)
local notation "Y" a:arg => (Sigma.fst (internalBlowupTower K b s a) : Scheme)
local notation "T" a:arg => WithBoundary.toTower (Sigma.snd (internalBlowupTower K b s a))
local notation "π" a:arg => toBase (T a)
local notation "ι" a:arg => WithBoundary.boundaryι (Sigma.snd (internalBlowupTower K b s a))
local notation "F" => Φ.finiteFanScheme K
local notation "m" j:arg => ofAdd (LinearMap.toAddMonoidHom
  (b.detDualEquiv (Ray.primitiveGenerator (s j))))
local notation "χ₀" => Φ.functionFieldCharacter K
local notation "C" => algebraMap K (Scheme.functionField F)

variable {X X' : Scheme} {D : X.IdealSheafData} {D' : X'.IdealSheafData}
  {p : (internalBlowupTower K b s c).1 ⟶ X} {q : (internalBlowupTower K b s d).1 ⟶ X'}

local notation "base" => Φ.finiteFanSchemeToSpec K

variable {c d} in
/-- A torus translation lifting an isomorphism of contractions through their
ordered internal blowup models. The lift matches the centers in order. -/
structure ContractedToricTranslation
    (p : Y c ⟶ X) (q : Y d ⟶ X') (e : X ≅ X') where
  /-- The character specifying the translation of the torus. -/
  character : Multiplicative (N →+ ℤ) →* Kˣ
  /-- The isomorphism of the ordered blowup models. -/
  iso : Y c ≅ Y d
  /-- The isomorphism lifts the translation through the ordered towers. -/
  isLift : IsLift (Φ.torusTranslationIso K character) (T c) (T d) iso
  /-- The lift commutes with the projections to the contractions. -/
  commutes : p ≫ e.hom = iso.hom ≫ q

variable {b s c d} in
/-- The translating character determines its ordered lift. -/
@[ext]
theorem ContractedToricTranslation.ext {e : X ≅ X'}
    {t u : ContractedToricTranslation K b s p q e} (h : t.character = u.character) :
    t = u := by
  have hi := t.isLift.unique (h.symm ▸ u.isLift)
  cases t
  cases u
  cases h
  cases hi
  rfl

/-- A translating lift identifies the reduced total boundary supports on the ordered models. -/
theorem support_comap_contraction_of_translation
    {χ : Multiplicative (N →+ ℤ) →* Kˣ} {t : Y c ≅ Y d}
    (ht : IsLift (Φ.torusTranslationIso K χ) (T c) (T d) t)
    (hD : (D.comap p).support = (ι c).ker.support)
    (hD' : (D'.comap q).support = (ι d).ker.support) :
    (D.comap p).support = ((D'.comap q).comap t.hom).support := by
  have he := boundaryι_comp_of_isLift_internalBlowupTower_torusTranslation K b s c d χ ht
  have hker : (ι d).ker.comap t.hom = (ι c).ker := by
    have hk : ((ι c).ker.map t.hom) = (ι d).ker := by
      rw [map_ker, he, Scheme.Hom.ker_comp_of_isIso]
    rw [← hk, comap_map_of_isClosedImmersion]
  rw [support_comap (D'.comap q), hD', ← support_comap, hker, hD]

variable {b s c d} in
/-- A descending torus translation identifies the reduced boundary ideals when
their inverse images are supported on the strict toric boundaries. -/
theorem ContractedToricTranslation.comap_boundary
    {e : X ≅ X'} [Surjective p] [IsReduced D.subscheme] [IsReduced D'.subscheme]
    (t : ContractedToricTranslation K b s p q e)
    (hD : (D.comap p).support = (ι c).ker.support)
    (hD' : (D'.comap q).support = (ι d).ker.support) : D'.comap e.hom = D := by
  have hcomp : (D'.comap e.hom).comap p = (D'.comap q).comap t.iso.hom := by
    rw [← comap_comp, t.commutes, comap_comp]
  have hpre : ((D'.comap e.hom).comap p).support = (D.comap p).support :=
    (congrArg Scheme.IdealSheafData.support hcomp).trans
      (support_comap_contraction_of_translation K b s c d t.isLift hD hD').symm
  have hsupport : (D'.comap e.hom).support = D.support := by
    apply SetLike.coe_injective
    apply p.surjective.preimage_injective
    simpa only [support_comap, TopologicalSpace.Closeds.coe_preimage] using
      congrArg (fun I : TopologicalSpace.Closeds (Y c) ↦ (I : Set (Y c))) hpre
  simpa only [vanishingIdeal_support, radical_comap_of_isOpenImmersion,
    D.isReduced_subscheme_iff_radical_eq.mp ‹IsReduced D.subscheme›,
    D'.isReduced_subscheme_iff_radical_eq.mp ‹IsReduced D'.subscheme›] using
    congrArg (vanishingIdeal (X := X)) hsupport

variable {b s c d} [PerfectField K] in
/-- When a translating lift descends to the base surfaces, its pullback identifies
their Picard classes in the coordinates on the ordered models. -/
theorem ContractedToricTranslation.pullback_marking {e : X ≅ X'}
    (t : ContractedToricTranslation K b s p q e) (hΦ : Φ.IsRegular) (a : LineBundleClass X') :
    (internalBlowupPicardMarking K b s c hΦ).symm
        (Additive.ofMul (LineBundleClass.pullback p (LineBundleClass.pullback e.hom a))) =
      (internalBlowupPicardMarking K b s d hΦ).symm
        (Additive.ofMul (LineBundleClass.pullback q a)) := by
  rw [LineBundleClass.pullback_comp, t.commutes, ← LineBundleClass.pullback_comp]
  have hmark := pullback_internalBlowupPicardMarking_of_isLift_torusTranslation
    K b s c d hΦ t.character t.isLift ((internalBlowupPicardMarking K b s d hΦ).symm
        (Additive.ofMul (LineBundleClass.pullback q a)))
  simpa only [LinearEquiv.apply_symm_apply, toMul_ofMul, ofMul_toMul,
    LinearEquiv.symm_apply_eq] using congrArg Additive.ofMul hmark

variable [IsAlgClosed K] [IsIntegral X] [IrreducibleSpace X']
  [X.Over (Spec (.of K))] [X'.Over (Spec (.of K))]
  [IsSeparated (X' ↘ Spec (.of K))] [IsModification p] [IsModification q]

/-- On two isomorphic contractions of ordered models of the same fan, equality of
the pulled-back scaled charge functions identifies the isomorphism with the descent of a
unique torus translation. The centers are transported as an ordered tuple, including
infinitely near centers. -/
theorem existsUnique_contractedToricTranslation_of_eq_scaled_characters
    (hΦ : Φ.IsRegular) (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    (e : X ≅ X') [e.hom.IsOver S]
    (hc : p ≫ (X ↘ S) = π c ≫ base) (hd : q ≫ (X' ↘ S) = π d ≫ base)
    (heval :
      letI : IsModification (π c) := isModification_internalBlowupTower_toBase K b s c hΦ
      letI : IsModification (π d) := isModification_internalBlowupTower_toBase K b s d hΦ
      letI : IrreducibleSpace (Y c) := (IsModification.birational p).irreducibleSpace
      letI : IrreducibleSpace (Y d) := (IsModification.birational q).irreducibleSpace
      letI : IsIso p.functionFieldMap := p.isIso_functionFieldMap_of_isModification
      letI : IsIso q.functionFieldMap := q.isIso_functionFieldMap_of_isModification
      let e₀ := (π c).functionFieldMap ≫ CategoryTheory.inv (p.functionFieldMap)
      let e₁ := (π d).functionFieldMap ≫ CategoryTheory.inv (q.functionFieldMap)
      ∀ j : Fin n, (e₁ ≫ e.hom.functionFieldMap).hom (C (d j : K) * χ₀ (m j)) =
        e₀.hom (C (c j : K) * χ₀ (m j))) :
    Nonempty (Unique (ContractedToricTranslation K b s p q e)) := by
  have := isModification_internalBlowupTower_toBase K b s c hΦ
  have := isModification_internalBlowupTower_toBase K b s d hΦ
  have := (IsModification.birational p).irreducibleSpace
  have := (IsModification.birational q).irreducibleSpace
  have : IsReduced (Y c) := by
    have := smoothOfRelativeDimension_internalBlowupTower K b s c hΦ
    have : Smooth (π c ≫ base) := SmoothOfRelativeDimension.smooth 2 _
    exact (π c ≫ base).isReduced_of_smooth
  have := p.isIso_functionFieldMap_of_isModification
  have : IsIso q.functionFieldMap := q.isIso_functionFieldMap_of_isModification
  -- Compare the two ordered models over the generic point of the same contraction.
  obtain ⟨f, hf, hfd⟩ := p.exists_dominant_generic_section
  obtain ⟨g, hg, hgd⟩ := (q ≫ e.inv).exists_dominant_generic_section
  have hg' : g ≫ q = (f ≫ p) ≫ e.hom := by
    simpa only [Category.assoc, e.inv_hom_id, Category.comp_id, hf] using congrArg (· ≫ e.hom) hg
  have he : e.hom ≫ (X' ↘ S) = X ↘ S := HomIsOver.comp_over (f := e.hom)
  have hover : f ≫ π c ≫ base = g ≫ π d ≫ base := by
    calc
      _ = (f ≫ p) ≫ (X ↘ S) := by rw [Category.assoc, hc]
      _ = ((f ≫ p) ≫ e.hom) ≫ (X' ↘ S) := by rw [Category.assoc (f ≫ p) e.hom, he]
      _ = _ := by rw [← hg', Category.assoc, hd]
  have hfield : q.functionFieldMap ≫ g.functionFieldMap =
      e.hom.functionFieldMap ≫ p.functionFieldMap ≫ f.functionFieldMap := by
    rw [← Scheme.Hom.functionFieldMap_comp, Scheme.Hom.functionFieldMap_congr hg',
      Scheme.Hom.functionFieldMap_comp, Scheme.Hom.functionFieldMap_comp]
  have hgfield := (IsIso.inv_comp_eq q.functionFieldMap).mpr hfield.symm
  have hscaled (j : Fin n) :
      (g ≫ π d).functionFieldMap (C (d j : K) * χ₀ (m j)) =
        (f ≫ π c).functionFieldMap (C (c j : K) * χ₀ (m j)) := by
    rw [Scheme.Hom.functionFieldMap_comp, Scheme.Hom.functionFieldMap_comp, ← hgfield]
    have hj := congrArg f.functionFieldMap (congrArg p.functionFieldMap (heval j))
    simpa only [CommRingCat.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply,
      IsIso.inv_hom_id_apply] using hj
  obtain ⟨χ, ⟨t, ht, hfg⟩, huniq⟩ :=
    existsUnique_isLift_of_eq_scaled_characters_of_dominant K b s hΦ c d hindex hover hscaled
  have htq : p ≫ e.hom = t.hom ≫ q := by
    refine AlgebraicGeometry.ext_of_isDominant_of_isSeparated (X' ↘ S) ?_ f ?_
    · simp only [Category.assoc, he, hc, hd,
        hom_comp_internalBlowupTower_structureMap_of_isLift_torusTranslation K b s c d χ ht]
    · rw [← Category.assoc, ← Category.assoc, hfg]
      exact hg'.symm
  refine ⟨{ default := ⟨χ, t, ht, htq⟩, uniq := fun u ↦ ContractedToricTranslation.ext K ?_ }⟩
  apply huniq u.character
  refine ⟨u.iso, u.isLift, q.eq_of_comp_eq_of_isModification ?_⟩
  rw [Category.assoc, ← u.commutes, ← Category.assoc, hg']

end TauCeti.Toric.Fan
