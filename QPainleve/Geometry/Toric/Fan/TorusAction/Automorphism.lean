/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.StrictTransform
public import QPainleve.Geometry.Toric.Fan.TorusAction.InternalBlowup

import QPainleve.AlgebraicGeometry.Blowup.Tower.Automorphism
import QPainleve.Geometry.Toric.CharacterTorus.CenterAlignment
import QPainleve.Geometry.Toric.Fan.Boundary.Automorphism
import QPainleve.Geometry.Toric.Fan.Picard.Translation
import QPainleve.Geometry.Toric.Fan.Smooth

/-!
# Picard-trivial automorphisms of ordered internal toric blowups

An automorphism of the ordered internal model that fixes the Picard group and
each strict boundary component descends to a translation of the toric model.
The center ideals force the translating character to be trivial on the charge
image, and every such translation lifts uniquely. The centers can repeat.

This is the ordered internal blowup calculation in the proof of Proposition 2.6
of Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  {n : ℕ} (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ)
  (hΦ : Φ.IsRegular)

local notation "X" => Φ.algebraicRealization
local notation "Y" => Sigma.fst (internalBlowupTower b s c)
local notation "T" => WithBoundary.toTower (Sigma.snd (internalBlowupTower b s c))
local notation "j" => WithBoundary.boundaryι (Sigma.snd (internalBlowupTower b s c))
local notation "p" => toBase T
local notation "base" => Φ.algebraicRealizationStructureMap
local notation "a" ρ:arg => (Ray.boundaryComponentι ρ hΦ ≫ j)
local notation "Chars" => (Multiplicative (N →+ ℤ) →* ℂˣ)
local notation "m" k:arg => LinearMap.toAddMonoidHom (b.detDualEquiv (Ray.primitiveGenerator (s k)))

/-- The ray component embedded through the fixed boundary is the strict transform of
the ray divisor in the ordered internal model. -/
theorem ker_boundaryComponentι_internalBlowupTower (ρ : Φ.Ray) :
    (a ρ).ker = strictTransform (Φ.rayBoundaryIdeal hΦ ρ) T := by
  let D := (Φ.boundaryIdeal inferInstance).subschemeι
  let J (k : Fin n) := (s k).internalCenter b (c k)
  let P (M : Σ Z, WithBoundary D n Z) :=
    (ρ.boundaryComponentι hΦ ≫ M.2.boundaryι).ker =
      strictTransform (Φ.rayBoundaryIdeal hΦ ρ) M.2.toTower
  apply (congrArg P (internalBlowupTower_eq_alongBoundary b s c)).mpr
  refine (strictTransform_rayBoundaryIdeal_alongBoundary hΦ J ρ ?_).symm
  intro k
  rw [Ray.internalCenter_val]
  exact (s k).isEffectiveCartier_comap_ker_binomialCenterOnBoundary hΦ
    (by simpa using Module.finrank_eq_card_basis b) (b.detDualEquiv_self _)
    ((s k).surjective_detCharacter b) (c k) ρ

/-- Automorphisms over the complex base of the ordered internal toric model that act
trivially on its Picard group and preserve the ideal of each strict ray divisor. -/
def internalBlowupPicardBoundaryAut : Subgroup (Aut Y) where
  carrier := {g | g.asIso.hom ≫ p ≫ base = p ≫ base ∧
    (∀ L, pullback g.asIso.hom L = L) ∧
    ∀ ρ, (strictTransform (Φ.rayBoundaryIdeal hΦ ρ) T).comap g.asIso.hom =
      strictTransform (Φ.rayBoundaryIdeal hΦ ρ) T}
  one_mem' := by simp [pullback_id]
  mul_mem' := by
    rintro g₁ g₂ ⟨h₁, hPic₁, hD₁⟩ ⟨h₂, hPic₂, hD₂⟩
    refine ⟨?_, fun L ↦ ?_, fun ρ ↦ ?_⟩
    · simp only [Aut.mul_asIso, Iso.trans_hom, Category.assoc, h₁, h₂]
    · simp only [Aut.mul_asIso, Iso.trans_hom, ← pullback_comp, hPic₁, hPic₂]
    · simp only [Aut.mul_asIso, Iso.trans_hom, comap_comp, hD₁, hD₂]
  inv_mem' := by
    rintro g ⟨h, hPic, hD⟩
    refine ⟨?_, fun L ↦ ?_, fun ρ ↦ ?_⟩
    · simpa only [Aut.inv_asIso, Iso.symm_hom, Iso.inv_hom_id_assoc] using
        (congrArg (fun q ↦ g.asIso.inv ≫ q) h).symm
    · simpa only [Aut.inv_asIso, Iso.symm_hom, pullback_comp,
        Iso.inv_hom_id, pullback_id] using (congrArg (pullback g.asIso.inv) (hPic L)).symm
    · simpa only [Aut.inv_asIso, Iso.symm_hom, ← comap_comp, Iso.inv_hom_id, comap_id] using
        (congrArg (fun I ↦ I.comap g.asIso.inv) (hD ρ)).symm

/-- Membership in the subgroup is tested by the structure morphism, Picard pullback, and
the strict-transform ideal sheaves. -/
@[simp]
theorem mem_internalBlowupPicardBoundaryAut (g : Aut Y) :
    g ∈ internalBlowupPicardBoundaryAut b s c hΦ ↔
      g.asIso.hom ≫ p ≫ base = p ≫ base ∧ (∀ L, pullback g.asIso.hom L = L) ∧
        ∀ ρ, (strictTransform (Φ.rayBoundaryIdeal hΦ ρ) T).comap g.asIso.hom =
          strictTransform (Φ.rayBoundaryIdeal hΦ ρ) T := (Iff.rfl)

private theorem map_ker_boundaryComponentι_toBase (ρ : Φ.Ray) :
    (a ρ).ker.map p = Φ.rayBoundaryIdeal hΦ ρ := by
  rw [map_ker, Category.assoc, WithBoundary.boundaryι_toBase, Ray.boundaryComponentι_subschemeι,
    ker_subschemeι]

private theorem comap_rayBoundaryIdeal_of_isLift {e : X ≅ X} {g : Y ≅ Y}
    (hg : IsLift e T T g) (ρ : Φ.Ray) (hD : (a ρ).ker.comap g.hom = (a ρ).ker) :
    (Φ.rayBoundaryIdeal hΦ ρ).comap e.hom = Φ.rayBoundaryIdeal hΦ ρ := by
  have hmap : (a ρ).ker.map g.hom = (a ρ).ker := by
    calc
      _ = ((a ρ).ker.comap g.hom).map g.hom := congrArg (fun J ↦ J.map g.hom) hD.symm
      _ = _ := by rw [map_comap_of_isClosedImmersion ((a ρ).ker) g.hom,
        Scheme.Hom.ker_eq_bot_of_isIso g.hom, sup_bot_eq]
  have ht := congrArg (fun I : Scheme.IdealSheafData Y ↦ I.map p) hmap
  rw [← map_comp, hg.hom_toBase, map_comp, map_ker_boundaryComponentι_toBase] at ht
  exact (congrArg (fun I ↦ I.comap e.hom) ht.symm).trans
    (comap_map_of_isClosedImmersion _ _)

private theorem comap_ker_boundaryComponentι_of_translation {g : Y ≅ Y} (χ : Chars)
    (hg : j ≫ g.hom = (boundaryTranslation χ).hom ≫ j) (ρ : Φ.Ray) :
    (a ρ).ker.comap g.hom = (a ρ).ker := by
  let d := boundaryTranslation (Φ := Φ) χ
  let t := Φ.torusTranslation χ
  let k := ρ.boundaryComponentι hΦ
  let I := Φ.rayBoundaryIdeal hΦ ρ
  let l := (Φ.boundaryIdeal inferInstance).subschemeι
  have hk : k ≫ l = I.subschemeι := ρ.boundaryComponentι_subschemeι hΦ
  have ht : I.map t.hom = I := by
    calc
      _ = (I.comap t.hom).map t.hom :=
        congrArg (fun J ↦ J.map t.hom) (Φ.comap_rayBoundaryIdeal_torusTranslation_hom hΦ χ ρ).symm
      _ = _ := by rw [map_comap_of_isClosedImmersion, Scheme.Hom.ker_eq_bot_of_isIso, sup_bot_eq]
  have hmap : k.ker.map d.hom = k.ker := by
    have h : (k.ker.map d.hom).map l = k.ker.map l := by
      rw [← map_comp, boundaryTranslation_hom_subschemeι, map_comp, map_ker, hk, ker_subschemeι]
      exact ht
    simpa only [comap_map_of_isClosedImmersion] using congrArg (fun J ↦ J.comap l) h
  have hfix : (a ρ ≫ g.hom).ker = (a ρ).ker := by
    rw [Category.assoc, hg, ← Category.assoc, ← map_ker, ← map_ker, ← map_ker, hmap]
  exact (congrArg (fun I ↦ I.comap g.hom) hfix.symm).trans
    (Scheme.Hom.comap_ker_comp_of_isClosedImmersion _ _)

private theorem existsUnique_lift_fixed_centres (χ : Chars) (hχ : ∀ k, χ (ofAdd (m k)) = 1) :
    ∃! g : internalBlowupPicardBoundaryAut b s c hΦ,
      IsLift (Φ.torusTranslation χ) T T (g : Aut Y).asIso := by
  obtain ⟨g, ⟨hg, hb, hPic⟩, -⟩ := exists_unique_internal_blowup_torus_translation b s hΦ
    χ c c (fun k ↦ by simp [hχ k])
  have hOver : g.hom ≫ p ≫ base = p ≫ base := by
    exact hom_comp_internalBlowupTower_structureMap_of_isLift_torusTranslation b s c c χ hg
  have hPic' (L : LineBundleClass Y) : pullback g.hom L = L := by
    obtain ⟨x, hx⟩ := (internalBlowupPicardMarking b s c hΦ).surjective (Additive.ofMul L)
    simpa only [hx, toMul_ofMul] using hPic x
  refine ⟨⟨Aut.of g, ⟨hOver, hPic', fun ρ ↦
    by simpa only [ker_boundaryComponentι_internalBlowupTower] using
      comap_ker_boundaryComponentι_of_translation b s c hΦ χ hb ρ⟩⟩, hg, ?_⟩
  intro g' hg'
  exact Subtype.ext (Aut.ext (hg'.unique hg))

private theorem existsUnique_translation_of_internalBlowupAut (hc : Φ.IsComplete)
    (g : internalBlowupPicardBoundaryAut b s c hΦ) :
    ∃! χ : Chars, IsLift (Φ.torusTranslation χ) T T (g : Aut Y).asIso ∧
      ∀ k, χ (ofAdd (m k)) = 1 := by
  let H := isClosedPointTower_internalBlowupTower b s c
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  have : SmoothOfRelativeDimension 2 base :=
    hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  obtain ⟨e, ⟨he, hePic, heOver⟩, heUnique⟩ :=
    H.existsUnique_isLift_over_of_picard_trivial base (g : Aut Y).asIso g.property.2.1 g.property.1
  have : e.hom.IsOver (Spec (.of ℂ)) := ⟨heOver⟩
  obtain ⟨χ, rfl, hUniq⟩ := Φ.existsUnique_torusTranslation_of_comap_rayBoundaryIdeal_eq hΦ hc e
    (fun ρ ↦ comap_rayBoundaryIdeal_of_isLift b s c hΦ he ρ (by
      simpa only [ker_boundaryComponentι_internalBlowupTower] using g.property.2.2 ρ))
  refine ⟨χ, ⟨he, fun k ↦ ?_⟩, ?_⟩
  · have hparam :=
      (exists_isLift_internalBlowupTower_torusTranslation_iff b s c c χ).mp ⟨_, he⟩ k
    exact mul_left_cancel (hparam.trans (mul_one (c k)).symm)
  · intro ψ hψ
    exact hUniq ψ (heUnique _ ⟨hψ.1, Φ.pullback_torusTranslation_hom hΦ ψ, by
      simpa only [algebraicRealization_over] using
        (HomIsOver.comp_over (f := (Φ.torusTranslation ψ).hom) (S := Spec (.of ℂ)))⟩)

private def detCharacterEquiv : N ≃+ (N →+ ℤ) :=
  (b.detDualEquiv.trans (addMonoidHomLequivInt ℤ).symm).toAddEquiv

local notation "Charge" => LinearMap.toAddMonoidHom (rayChargeMap s)
local notation "Stabilizer" => MonoidHom.ker
  (MonoidHom.compHom' (P := ℂˣ) (AddMonoidHom.toMultiplicative Charge))
local notation "translate" z:arg =>
  MonoidHom.comp z
    (MulEquiv.toMonoidHom (AddEquiv.toMultiplicative (AddEquiv.symm (detCharacterEquiv b))))

omit [Nonempty Φ.cones] in
private theorem mem_translationKernel_iff (z : Multiplicative N →* ℂˣ) :
    z ∈ Stabilizer ↔ ∀ k, z (ofAdd (s k).primitiveGenerator) = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hz k
    have he : z.comp (AddMonoidHom.toMultiplicative Charge) = 1 := hz
    simpa only [MonoidHom.comp_apply, AddMonoidHom.coe_toMultiplicative,
      Function.comp_apply, toAdd_ofAdd, LinearMap.toAddMonoidHom_coe, rayChargeMap_single,
      MonoidHom.one_apply] using DFunLike.congr_fun he (ofAdd (Pi.single k 1))
  · intro hz
    apply MonoidHom.toAdditiveRight.injective
    apply AddMonoidHom.toIntLinearMap_injective
    apply (Pi.basisFun ℤ (Fin n)).ext
    intro k
    simp [Pi.basisFun_apply, hz]

omit [Nonempty Φ.cones] in
private theorem translate_mem_iff (z : Multiplicative N →* ℂˣ) :
    z ∈ Stabilizer ↔ ∀ k, (translate z) (ofAdd (m k)) = 1 := by
  rw [mem_translationKernel_iff]
  have hm (k : Fin n) : detCharacterEquiv b (s k).primitiveGenerator = m k := (rfl)
  have hval (k : Fin n) : (translate z) (ofAdd (m k)) = z (ofAdd (s k).primitiveGenerator) :=
    congrArg (fun v : N ↦ z (ofAdd v)) ((detCharacterEquiv b).symm_apply_eq.mpr (hm k).symm)
  simp only [hval]

private theorem existsUnique_lift_translation (z : Stabilizer) :
    ∃! g : internalBlowupPicardBoundaryAut b s c hΦ,
      IsLift (Φ.torusTranslation (translate z.val)) T T (g : Aut Y).asIso :=
  existsUnique_lift_fixed_centres b s c hΦ _ ((translate_mem_iff b s _).mp z.property)

private def liftTranslation : Stabilizer →* internalBlowupPicardBoundaryAut b s c hΦ where
  toFun z := (existsUnique_lift_translation b s c hΦ z).exists.choose
  map_one' := by
    apply (existsUnique_lift_translation b s c hΦ 1).unique
      (existsUnique_lift_translation b s c hΦ 1).exists.choose_spec
    simpa only [Subgroup.coe_one, MonoidHom.one_comp, torusTranslation_one, Aut.one_asIso]
      using IsLift.refl T
  map_mul' z w := by
    apply (existsUnique_lift_translation b s c hΦ (z * w)).unique
      (existsUnique_lift_translation b s c hΦ (z * w)).exists.choose_spec
    simp only [Subgroup.coe_mul, Aut.mul_asIso, MonoidHom.mul_comp]
    rw [mul_comm (translate z.val), ← torusTranslation_trans]
    exact (existsUnique_lift_translation b s c hΦ w).exists.choose_spec.trans
      (existsUnique_lift_translation b s c hΦ z).exists.choose_spec

private theorem liftTranslation_isLift (z : Stabilizer) :
    IsLift (Φ.torusTranslation (translate z.val)) T T
      ((liftTranslation b s c hΦ z : internalBlowupPicardBoundaryAut b s c hΦ) : Aut Y).asIso :=
  (existsUnique_lift_translation b s c hΦ z).exists.choose_spec

private theorem liftTranslation_bijective (hc : Φ.IsComplete) :
    Function.Bijective (liftTranslation b s c hΦ) := by
  constructor
  · intro z w h
    obtain ⟨χ, -, huniq⟩ :=
      existsUnique_translation_of_internalBlowupAut b s c hΦ hc (liftTranslation b s c hΦ z)
    have hz := huniq (translate z.val)
      ⟨liftTranslation_isLift b s c hΦ z, (translate_mem_iff b s _).mp z.property⟩
    have hw := huniq (translate w.val)
      ⟨h ▸ liftTranslation_isLift b s c hΦ w, (translate_mem_iff b s _).mp w.property⟩
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    obtain ⟨y, rfl⟩ := (detCharacterEquiv b).symm.toMultiplicative.surjective x
    exact DFunLike.congr_fun (hz.trans hw.symm) y
  · intro g
    obtain ⟨χ, ⟨hχ, hcentres⟩, -⟩ := existsUnique_translation_of_internalBlowupAut b s c hΦ hc g
    let z := χ.comp (detCharacterEquiv b).toMultiplicative.toMonoidHom
    have hz : translate z = χ := by ext x; simp [z]
    have hmem : z ∈ Stabilizer := (translate_mem_iff b s _).mpr (hz.symm ▸ hcentres)
    refine ⟨⟨z, hmem⟩, (existsUnique_lift_translation b s c hΦ ⟨z, hmem⟩).unique
      (liftTranslation_isLift b s c hΦ ⟨z, hmem⟩) ?_⟩
    exact hz.symm ▸ hχ

private def chargeQuotientCharacterEquiv :
    Stabilizer ≃* (Multiplicative (N ⧸ (rayChargeMap s).range) →* ℂˣ) :=
  (MulEquiv.subgroupCongr (QPainleve.CharacterTorus.translationKernel_eq ℂ Charge)).trans
    (MonoidHom.domRestrictHomKerEquiv ℂˣ (AddMonoidHom.range Charge).toSubgroup)

/-- The character group of the quotient of the ray lattice by the charge image is
isomorphic to the group of Picard-trivial automorphisms of the ordered internal model
that fix every strict boundary divisor. The charge map may have any rank. -/
def internalBlowupPicardBoundaryAutMulEquiv (hc : Φ.IsComplete) :
    (Multiplicative (N ⧸ (rayChargeMap s).range) →* ℂˣ) ≃*
      internalBlowupPicardBoundaryAut b s c hΦ :=
  (chargeQuotientCharacterEquiv s).symm.trans
    (MulEquiv.ofBijective (liftTranslation b s c hΦ) (liftTranslation_bijective b s c hΦ hc))

/-- The automorphism attached to a quotient character is the ordered lift of its toric
translation, using the determinant to identify lattice vectors with torus exponents. -/
theorem internalBlowupPicardBoundaryAutMulEquiv_isLift (hc : Φ.IsComplete)
    (z : Multiplicative (N ⧸ (rayChargeMap s).range) →* ℂˣ) :
    IsLift
      (Φ.torusTranslation
        (z.comp ((Submodule.mkQ (rayChargeMap s).range).toAddMonoidHom.toMultiplicative.comp
          (b.detDualEquiv.trans (addMonoidHomLequivInt ℤ).symm).symm.toAddEquiv.toMultiplicative)))
      T T ((internalBlowupPicardBoundaryAutMulEquiv b s c hΦ hc z :
        internalBlowupPicardBoundaryAut b s c hΦ) : Aut Y).asIso := by
  exact liftTranslation_isLift b s c hΦ ((chargeQuotientCharacterEquiv s).symm z)

end TauCeti.Toric.Fan
