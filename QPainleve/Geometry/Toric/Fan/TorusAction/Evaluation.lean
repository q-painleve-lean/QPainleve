/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.TorusAction.InternalBlowup

import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
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

universe u

variable (K : Type u) [Field K] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]

local notation "S" => Spec (CommRingCat.of K)
local notation "Chars" => (Multiplicative (N →+ ℤ) →* Kˣ)

variable {n : ℕ} (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "m" j:arg => ofAdd (LinearMap.toAddMonoidHom
  (Module.Basis.detDualEquiv b (Ray.primitiveGenerator (s j))))
local notation "χ₀" => Φ.functionFieldCharacter K
local notation "C" => algebraMap K (Scheme.functionField (Φ.finiteFanScheme K))

section Dominant

variable {W : Scheme} [IsIntegral W] [W.Over (Spec (.of K))]
  {f g : W ⟶ Φ.finiteFanScheme K} [IsDominant f] [IsDominant g]
  [f.IsOver (Spec (.of K))] [g.IsOver (Spec (.of K))]

variable [IsIntegrallyClosedIn K W.functionField] in
private theorem existsUnique_character_scale_of_eq_scaled_characters
    (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    (c d : Fin n → Kˣ)
    (h : ∀ j, f.functionFieldMap (C (d j : K) * χ₀ (m j)) =
      g.functionFieldMap (C (c j : K) * χ₀ (m j))) :
    ∃! χ : Chars, ∀ a,
      f.functionFieldMap (χ₀ a) =
        algebraMap K W.functionField (χ a : K) * g.functionFieldMap (χ₀ a) := by
  let e := (b.detDualEquiv.trans (addMonoidHomLequivInt ℤ).symm).toAddEquiv.toMultiplicative
  let F := (Units.map f.functionFieldMap.hom.toMonoidHom).comp (χ₀).toHomUnits
  let G := (Units.map g.functionFieldMap.hom.toMonoidHom).comp (χ₀).toHomUnits
  let r := F / G
  let ι := Units.map (algebraMap K W.functionField).toMonoidHom
  let H := (rayChargeMap s).range.toAddSubgroup.toSubgroup
  have hr (j : Fin n) : r (m j) = ι (c j / d j) := by
    have hj := h j
    rw [map_mul, map_mul, f.functionFieldMap_algebraMap K,
      g.functionFieldMap_algebraMap K] at hj
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
  have hi : (H.map e.toMonoidHom).index ≠ 0 := by
    rw [Subgroup.index_map_of_bijective e.bijective H, AddSubgroup.index_toSubgroup]
    exact hindex
  obtain ⟨χ, hχ, huniq⟩ := r.existsUnique_units_lift_of_finiteIndex _ hi hH
  have hiff (ψ : Chars) :
      ι.comp ψ = r ↔ ∀ a,
        f.functionFieldMap (χ₀ a) =
          algebraMap K W.functionField (ψ a : K) * g.functionFieldMap (χ₀ a) := by
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
    f = g ≫ (Φ.torusTranslationIso K χ).hom ↔ ∀ a,
      f.functionFieldMap (χ₀ a) =
        algebraMap K W.functionField (χ a : K) * g.functionFieldMap (χ₀ a) := by
  have hp (a : Multiplicative (N →+ ℤ)) :
      (g ≫ (Φ.torusTranslationIso K χ).hom).functionFieldMap (χ₀ a) =
        algebraMap K W.functionField (χ a : K) * g.functionFieldMap (χ₀ a) := by
    have hχ := Φ.functionFieldMap_torusTranslationIso_character K χ a.toAdd
    rw [ofAdd_toAdd] at hχ
    rw [Scheme.Hom.functionFieldMap_comp, CommRingCat.comp_apply, hχ, map_mul,
      g.functionFieldMap_algebraMap K]
  constructor
  · rintro rfl
    exact hp
  · intro h
    have : IsSeparated (Φ.finiteFanScheme K ↘ S) := by
      rw [Φ.finiteFanScheme_over K]
      infer_instance
    apply Scheme.Hom.ext_of_functionFieldMap_eq S
    apply CommRingCat.hom_ext
    have he := Φ.functionFieldCharacter_algHom_ext K (f := f.functionFieldAlgHom K)
      (g := (g ≫ (Φ.torusTranslationIso K χ).hom).functionFieldAlgHom K) fun a ↦ by
        simpa only [Scheme.Hom.functionFieldAlgHom_apply] using (h a).trans (hp a).symm
    ext a
    simpa only [Scheme.Hom.functionFieldAlgHom_apply] using DFunLike.congr_fun he a

variable [IsIntegrallyClosedIn K W.functionField] in
/-- Equality of scaled charge characters along two dominant maps into a fan surface
determines a unique torus translation relating the maps. Its values on the charges
align the two labeled center tuples. -/
theorem existsUnique_comp_torusTranslation_of_eq_scaled_characters
    (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    (c d : Fin n → Kˣ)
    (h : ∀ j, f.functionFieldMap (C (d j : K) * χ₀ (m j)) =
      g.functionFieldMap (C (c j : K) * χ₀ (m j))) :
    ∃! χ : Chars, f = g ≫ (Φ.torusTranslationIso K χ).hom ∧ ∀ j, d j * χ (m j) = c j := by
  obtain ⟨χ, hχ, huniq⟩ := existsUnique_character_scale_of_eq_scaled_characters K b s hindex c d h
  refine ⟨χ, ⟨(functionFieldMap_comp_torusTranslation_iff K χ).mpr hχ, ?_⟩,
    fun ψ hψ ↦ huniq ψ ((functionFieldMap_comp_torusTranslation_iff K ψ).mp hψ.1)⟩
  intro j
  apply Units.ext
  apply (algebraMap K W.functionField).injective
  apply mul_right_cancel₀
    ((Group.isUnit (m j)).map χ₀ |>.map g.functionFieldMap.hom).ne_zero
  simpa only [map_mul, Units.val_mul, f.functionFieldMap_algebraMap K,
    g.functionFieldMap_algebraMap K, hχ, _root_.mul_assoc] using h j

end Dominant

variable [IsAlgClosed K]

local notation "Y" c:arg => Sigma.fst (internalBlowupTower K b s c)
local notation "T" c:arg => WithBoundary.toTower (Sigma.snd (internalBlowupTower K b s c))
local notation "π" c:arg => QPainleve.BlowupTower.toBase (T c)

/-- Two dominant morphisms into ordered toric blowup models with equal scaled
charge evaluations differ by the lift of a unique torus translation. -/
theorem existsUnique_isLift_of_eq_scaled_characters_of_dominant
    (hΦ : Φ.IsRegular) (c d : Fin n → Kˣ) (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    {W : Scheme} [IsIntegral W] {f : W ⟶ Y c} {g : W ⟶ Y d}
    [IsDominant f] [IsDominant g]
    (hover : f ≫ π c ≫ Φ.finiteFanSchemeToSpec K =
      g ≫ π d ≫ Φ.finiteFanSchemeToSpec K)
    (heval : have := isModification_internalBlowupTower_toBase K b s c hΦ
             have := isModification_internalBlowupTower_toBase K b s d hΦ
             ∀ j, (g ≫ π d).functionFieldMap (C (d j : K) * χ₀ (m j)) =
               (f ≫ π c).functionFieldMap (C (c j : K) * χ₀ (m j))) :
    ∃! χ : Multiplicative (N →+ ℤ) →* Kˣ, ∃ t : Y c ≅ Y d,
      IsLift (Φ.torusTranslationIso K χ) (T c) (T d) t ∧ f ≫ t.hom = g := by
  have := isModification_internalBlowupTower_toBase K b s c hΦ
  have := isModification_internalBlowupTower_toBase K b s d hΦ
  let : W.Over S := ⟨f ≫ π c ≫ Φ.finiteFanSchemeToSpec K⟩
  have : (f ≫ π c).IsOver S := ⟨by rw [Φ.finiteFanScheme_over K, Category.assoc]; rfl⟩
  have : (g ≫ π d).IsOver S := ⟨by rw [Φ.finiteFanScheme_over K, Category.assoc]; exact hover.symm⟩
  have : IsIntegrallyClosedIn K W.functionField := TauCeti.isIntegrallyClosedIn_of_isAlgClosed
  obtain ⟨χ, ⟨hχ, hcenters⟩, huniq⟩ :=
    existsUnique_comp_torusTranslation_of_eq_scaled_characters K b s hindex c d heval
  obtain ⟨t, ht⟩ :=
    (exists_isLift_internalBlowupTower_torusTranslation_iff K b s c d χ).mpr hcenters
  have hproj {ψ : Multiplicative (N →+ ℤ) →* Kˣ} {t' : Y c ≅ Y d}
      (ht' : IsLift (Φ.torusTranslationIso K ψ) (T c) (T d) t') :
      (f ≫ t'.hom) ≫ π d = (f ≫ π c) ≫ (Φ.torusTranslationIso K ψ).hom := by
    simp only [Category.assoc, ht'.hom_toBase]
  refine ⟨χ, ⟨t, ht, (π d).eq_of_comp_eq_of_isModification ((hproj ht).trans hχ.symm)⟩, ?_⟩
  rintro ψ ⟨t', ht', hfg⟩
  exact huniq ψ ⟨hfg ▸ hproj ht',
    (exists_isLift_internalBlowupTower_torusTranslation_iff K b s c d ψ).mp ⟨t', ht'⟩⟩

/-- Two isomorphisms from a common surface into ordered toric blowup models with the
same scaled charge evaluations differ by the lift of a unique torus translation.
The lift matches each labeled center at its stage, including infinitely near centers.
Its comparison on the strict boundary and Picard marking is given by
`boundaryι_comp_of_isLift_internalBlowupTower_torusTranslation` and
`pullback_internalBlowupPicardMarking_of_isLift_torusTranslation`. -/
theorem existsUnique_isLift_of_eq_scaled_characters (hΦ : Φ.IsRegular)
    (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    (c d : Fin n → Kˣ) {W : Scheme} [IsIntegral W]
    (e : W ≅ Y c) (e' : W ≅ Y d)
    (hover : e.hom ≫ π c ≫ Φ.finiteFanSchemeToSpec K =
      e'.hom ≫ π d ≫ Φ.finiteFanSchemeToSpec K)
    (h : have := isModification_internalBlowupTower_toBase K b s c hΦ
         have := isModification_internalBlowupTower_toBase K b s d hΦ
         ∀ j, (e'.hom ≫ π d).functionFieldMap (C (d j : K) * χ₀ (m j)) =
           (e.hom ≫ π c).functionFieldMap (C (c j : K) * χ₀ (m j))) :
    ∃! χ : Chars, IsLift (Φ.torusTranslationIso K χ) (T c) (T d) (e.symm.trans e') := by
  obtain ⟨χ, ⟨t, ht, he⟩, huniq⟩ :=
    existsUnique_isLift_of_eq_scaled_characters_of_dominant K b s hΦ c d hindex hover h
  have het : e.symm.trans e' = t := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, ← he, Iso.inv_hom_id_assoc]
  refine ⟨χ, het.symm ▸ ht, fun ψ hψ ↦ huniq ψ ⟨_, hψ, ?_⟩⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

end TauCeti.Toric.Fan
