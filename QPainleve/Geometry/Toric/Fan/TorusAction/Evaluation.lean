/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.TorusAction.InternalBlowup

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
import QPainleve.Geometry.Toric.Fan.Separated
import QPainleve.RingTheory.IntegralClosure.Units
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Equality of scaled character evaluations

If two dominant maps to a toric surface agree on the scaled charge characters, their
ratio on every rational character is a scalar when the charges span a finite-index
sublattice. The resulting character gives the translation relating the maps and
aligns the corresponding blowup centers.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Chars" => (Multiplicative (N →+ ℤ) →* ℂˣ)

variable {n : ℕ} (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "m" j:arg => ofAdd (LinearMap.toAddMonoidHom
  (Module.Basis.detDualEquiv b (Ray.primitiveGenerator (s j))))
local notation "C" => algebraMap ℂ (Scheme.functionField (Fan.algebraicRealization Φ))

section Dominant

variable {W : Scheme} [IsIntegral W] [W.Over S]
  {f g : W ⟶ Φ.algebraicRealization} [IsDominant f] [IsDominant g] [f.IsOver S] [g.IsOver S]

private theorem existsUnique_character_scale_of_eq_scaled_characters
    (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    (c d : Fin n → ℂˣ)
    (h : ∀ j, f.functionFieldMap (C (d j : ℂ) * Φ.character (m j)) =
      g.functionFieldMap (C (c j : ℂ) * Φ.character (m j))) :
    ∃! χ : Chars, ∀ a,
      f.functionFieldMap (Φ.character a) =
        algebraMap ℂ W.functionField (χ a : ℂ) * g.functionFieldMap (Φ.character a) := by
  let e := (b.detDualEquiv.trans (addMonoidHomLequivInt ℤ).symm).toAddEquiv.toMultiplicative
  let F := (Units.map f.functionFieldMap.hom.toMonoidHom).comp Φ.character.toHomUnits
  let G := (Units.map g.functionFieldMap.hom.toMonoidHom).comp Φ.character.toHomUnits
  let r := F / G
  let ι := Units.map (algebraMap ℂ W.functionField).toMonoidHom
  let H := (rayChargeMap s).range.toAddSubgroup.toSubgroup
  have hr (j : Fin n) : r (m j) = ι (c j / d j) := by
    have hj := h j
    rw [map_mul, map_mul, f.functionFieldMap_algebraMap ℂ,
      g.functionFieldMap_algebraMap ℂ] at hj
    dsimp only [r]
    rw [MonoidHom.div_apply, map_div, div_eq_div_iff_mul_eq_mul, mul_comm (F (m j)) (ι (d j))]
    apply Units.ext
    exact hj
  have hH (a : Multiplicative (N →+ ℤ)) (ha : a ∈ H.map e.toMonoidHom) : r a ∈ ι.range := by
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨x, hx⟩ : ∃ x, rayChargeMap s x = y.toAdd := hy
    have hs : (∑ j, x j • (s j).primitiveGenerator) = rayChargeMap s x := by
      simpa only [map_sum, map_zsmul, Pi.basisFun_repr, Pi.basisFun_apply, rayChargeMap_single]
        using congrArg (rayChargeMap s) ((Pi.basisFun ℤ (Fin n)).sum_repr x)
    have he : y = ∏ j : Fin n, (ofAdd (s j).primitiveGenerator) ^ x j := by
      rw [← ofAdd_toAdd y, ← hx, ← hs, ofAdd_sum]
      simp only [ofAdd_zsmul]
    rw [MulEquiv.coe_toMonoidHom, he, map_prod, map_prod]
    refine Subgroup.prod_mem _ fun j _ ↦ ?_
    have hj : e (ofAdd (s j).primitiveGenerator) = m j := rfl
    rw [map_zpow e, hj, map_zpow r, hr]
    exact ι.range.zpow_mem ⟨_, rfl⟩ _
  have : IsIntegrallyClosedIn ℂ W.functionField := TauCeti.isIntegrallyClosedIn_of_isAlgClosed
  have hi : (H.map e.toMonoidHom).index ≠ 0 := by
    rw [Subgroup.index_map_of_bijective e.bijective H, AddSubgroup.index_toSubgroup]
    exact hindex
  obtain ⟨χ, hχ, huniq⟩ := r.existsUnique_units_lift_of_finiteIndex _ hi hH
  have hiff (ψ : Chars) :
      ι.comp ψ = r ↔ ∀ a,
        f.functionFieldMap (Φ.character a) =
          algebraMap ℂ W.functionField (ψ a : ℂ) * g.functionFieldMap (Φ.character a) := by
    rw [MonoidHom.ext_iff]
    simp only [MonoidHom.comp_apply]
    apply forall_congr'
    intro a
    rw [MonoidHom.div_apply, eq_div_iff_mul_eq', Units.ext_iff]
    simp only [ι, F, G, Units.val_mul, MonoidHom.comp_apply, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_toHomUnits]
    exact eq_comm
  exact ⟨χ, (hiff χ).mp hχ, fun ψ hψ ↦ huniq ψ ((hiff ψ).mpr hψ)⟩

private theorem functionFieldMap_comp_torusTranslation_iff (χ : Chars) :
    f = g ≫ (Φ.torusTranslation χ).hom ↔ ∀ a,
      f.functionFieldMap (Φ.character a) =
        algebraMap ℂ W.functionField (χ a : ℂ) * g.functionFieldMap (Φ.character a) := by
  have hp (a : Multiplicative (N →+ ℤ)) :
      (g ≫ (Φ.torusTranslation χ).hom).functionFieldMap (Φ.character a) =
        algebraMap ℂ W.functionField (χ a : ℂ) * g.functionFieldMap (Φ.character a) := by
    rw [Scheme.Hom.functionFieldMap_comp, CommRingCat.comp_apply,
      Φ.functionFieldMap_torusTranslation_character, map_mul, g.functionFieldMap_algebraMap ℂ]
  constructor
  · rintro rfl
    exact hp
  · intro h
    apply Scheme.Hom.ext_of_functionFieldMap_eq S
    apply CommRingCat.hom_ext
    have he := Φ.functionFieldAlgHom_ext (f := f.functionFieldAlgHom ℂ)
      (g := (g ≫ (Φ.torusTranslation χ).hom).functionFieldAlgHom ℂ) fun a ↦ by
        simpa only [Scheme.Hom.functionFieldAlgHom_apply] using (h a).trans (hp a).symm
    ext a
    simpa only [Scheme.Hom.functionFieldAlgHom_apply] using DFunLike.congr_fun he a

/-- Equality of scaled charge characters along two dominant maps into a fan surface
determines a unique torus translation relating the maps. Its values on the charges
align the two labeled center tuples. -/
theorem existsUnique_comp_torusTranslation_of_eq_scaled_characters
    (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    (c d : Fin n → ℂˣ)
    (h : ∀ j, f.functionFieldMap (C (d j : ℂ) * Φ.character (m j)) =
      g.functionFieldMap (C (c j : ℂ) * Φ.character (m j))) :
    ∃! χ : Chars, f = g ≫ (Φ.torusTranslation χ).hom ∧ ∀ j, d j * χ (m j) = c j := by
  obtain ⟨χ, hχ, huniq⟩ := existsUnique_character_scale_of_eq_scaled_characters b s hindex c d h
  refine ⟨χ, ⟨(functionFieldMap_comp_torusTranslation_iff χ).mpr hχ, ?_⟩,
    fun ψ hψ ↦ huniq ψ ((functionFieldMap_comp_torusTranslation_iff ψ).mp hψ.1)⟩
  intro j
  apply Units.ext
  apply (algebraMap ℂ W.functionField).injective
  apply mul_right_cancel₀
    ((Group.isUnit (m j)).map Φ.character |>.map g.functionFieldMap.hom).ne_zero
  simpa only [map_mul, Units.val_mul, f.functionFieldMap_algebraMap ℂ,
    g.functionFieldMap_algebraMap ℂ, hχ, _root_.mul_assoc] using h j

end Dominant

local notation "Y" c:arg => Sigma.fst (internalBlowupTower b s c)
local notation "T" c:arg => WithBoundary.toTower (Sigma.snd (internalBlowupTower b s c))
local notation "π" c:arg => QPainleve.BlowupTower.toBase (T c)

/-- Two isomorphisms from a common surface into ordered toric blowup models with the
same scaled charge evaluations differ by the lift of a unique torus translation.
The lift matches each labeled center at its stage, including infinitely near centers.
Its comparison on the strict boundary and Picard marking is given by
`boundaryι_comp_of_isLift_internalBlowupTower_torusTranslation` and
`pullback_internalBlowupPicardMarking_of_isLift_torusTranslation`. -/
theorem existsUnique_isLift_of_eq_scaled_characters (hΦ : Φ.IsRegular)
    (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    (c d : Fin n → ℂˣ) {W : Scheme} [IsIntegral W]
    (e : W ≅ Y c) (e' : W ≅ Y d)
    (hover : e.hom ≫ π c ≫ Φ.algebraicRealizationStructureMap =
      e'.hom ≫ π d ≫ Φ.algebraicRealizationStructureMap)
    (h : have := isModification_internalBlowupTower_toBase b s c hΦ
         have := isModification_internalBlowupTower_toBase b s d hΦ
         ∀ j, (e'.hom ≫ π d).functionFieldMap (C (d j : ℂ) * Φ.character (m j)) =
           (e.hom ≫ π c).functionFieldMap (C (c j : ℂ) * Φ.character (m j))) :
    ∃! χ : Chars, IsLift (Φ.torusTranslation χ) (T c) (T d) (e.symm.trans e') := by
  have : IsModification (π c) := isModification_internalBlowupTower_toBase b s c hΦ
  have : IsModification (π d) := isModification_internalBlowupTower_toBase b s d hΦ
  let : W.Over S := ⟨e.hom ≫ π c ≫ Φ.algebraicRealizationStructureMap⟩
  have : (e.hom ≫ π c).IsOver S := ⟨Category.assoc _ _ _⟩
  have : (e'.hom ≫ π d).IsOver S := ⟨(Category.assoc _ _ _).trans hover.symm⟩
  obtain ⟨χ, ⟨hχ, hcd⟩, huniq⟩ :=
    existsUnique_comp_torusTranslation_of_eq_scaled_characters b s hindex c d h
  have hproj {ψ : Chars} {t : Y c ≅ Y d}
      (ht : IsLift (Φ.torusTranslation ψ) (T c) (T d) t) :
      (e.hom ≫ t.hom) ≫ π d = (e.hom ≫ π c) ≫ (Φ.torusTranslation ψ).hom := by
    rw [Category.assoc, ht.hom_toBase, Category.assoc]
  obtain ⟨t, ht⟩ := (exists_isLift_internalBlowupTower_torusTranslation_iff b s c d χ).mpr hcd
  have he : e'.hom = e.hom ≫ t.hom :=
    (π d).eq_of_comp_eq_of_isModification (hχ.trans (hproj ht).symm)
  have het : e.symm.trans e' = t := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, he, Iso.inv_hom_id_assoc]
  refine ⟨χ, het.symm ▸ ht, fun ψ hψ ↦ huniq ψ ⟨?_, ?_⟩⟩
  · simpa only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp] using hproj hψ
  · exact (exists_isLift_internalBlowupTower_torusTranslation_iff b s c d ψ).mp ⟨_, hψ⟩

end TauCeti.Toric.Fan
