/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.Trivialization
public import QPainleve.Geometry.Toric.Fan.Ruling.Torus

import Mathlib.LinearAlgebra.Transvection.Basic
import QPainleve.Geometry.Toric.Fan.Scheme
import TauCeti.Geometry.Toric.Algebraic.Fan.Product.Isomorphism

/-!
# The transition of a Hirzebruch ruling over the base torus

The two affine ruling products restrict to products over the dense torus of the
base. Their change of trivialization is the toric automorphism induced by the
integral shear `(x, y) ↦ (x + e • y, y)`. In character coordinates this is the
pullback `u ↦ u t^e`, `t ↦ t`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Module PointedCone
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric.Fan

local notation "P₁" => Fan.projectiveSpace (Pi.basisFun ℤ (Fin 1)) (isIntegralLattice_intCast 1)
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Z₁" => Fin 1 → ℤ
local notation "W" => Fin 1 → ℝ
local notation "F" => Fan.prod P₁ projectiveLineTorusFan

private def shearLinearEquiv (R : Type) [CommRing R] (a : R) :
    ((Fin 1 → R) × (Fin 1 → R)) ≃ₗ[R] ((Fin 1 → R) × (Fin 1 → R)) :=
  LinearEquiv.transvection
    (f := a • (LinearMap.proj (0 : Fin 1)).comp (LinearMap.snd R (Fin 1 → R) (Fin 1 → R)))
    (v := (1, 0)) (by simp)

private theorem shearLinearEquiv_apply (R : Type) [CommRing R] (a : R)
    (x : (Fin 1 → R) × (Fin 1 → R)) :
    shearLinearEquiv R a x = (x.1 + a • x.2, x.2) := by
  rw [shearLinearEquiv, LinearEquiv.transvection.apply]
  ext j
  · simp [Subsingleton.elim j (0 : Fin 1)]
  · simp

private theorem map_prod_bot_shear (e : ℤ) (σ : PointedCone ℝ W) :
    PointedCone.map (shearLinearEquiv ℝ e).toLinearMap
      (σ.prod (⊥ : PointedCone ℝ W)) = σ.prod ⊥ := by
  have hfix {x : W × W} (hx : x ∈ σ.prod (⊥ : PointedCone ℝ W)) :
      shearLinearEquiv ℝ e x = x := by
    have hz := (Submodule.mem_bot (R := NNReal)).mp hx.2
    rw [shearLinearEquiv_apply, hz, smul_zero, add_zero, ← hz, Prod.mk.eta]
  ext x
  rw [PointedCone.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [LinearEquiv.coe_coe, hfix hy] at hyx
    exact hyx ▸ hy
  · exact fun hx ↦ ⟨x, hx, hfix hx⟩

/-- The shear `(x, y) ↦ (x + e • y, y)` of the projective-line product fan over
the base torus. It fixes every cone, since the base fan consists of the zero cone. -/
def projectiveLineTorusShear (e : ℤ) : FanEquiv (F) (F) where
  latticeEquiv := (shearLinearEquiv ℤ e).toAddEquiv
  realEquiv := shearLinearEquiv ℝ e
  map_lattice x := by
    have hcoe : (shearLinearEquiv ℤ e).toAddEquiv x = shearLinearEquiv ℤ e x := (rfl)
    simp only [hcoe, shearLinearEquiv_apply]
    ext j
    · simp
    · rfl
  map_mem σ := by
    have hfix (ρ : PointedCone ℝ (W × W)) (hρ : ρ ∈ (F).cones) :
        ρ.map (shearLinearEquiv ℝ e).toLinearMap = ρ := by
      obtain ⟨ρ₁, _, ρ₂, hρ₂, rfl⟩ := ((P₁).mem_prod_cones _).mp hρ
      rw [mem_projectiveLineTorusFan_cones.mp hρ₂, map_prod_bot_shear]
    constructor
    · intro hσ
      have hinj : Function.Injective (PointedCone.map (shearLinearEquiv ℝ e).toLinearMap) :=
        Submodule.map_injective_of_injective (shearLinearEquiv ℝ e).injective
      exact (hinj (hfix _ hσ)) ▸ hσ
    · intro hσ
      rwa [hfix _ hσ]

/-- The lattice map of the toric shear. -/
@[simp]
theorem projectiveLineTorusShear_latticeEquiv_apply (e : ℤ) (x : Z₁ × Z₁) :
    (projectiveLineTorusShear e).latticeEquiv x = (x.1 + e • x.2, x.2) :=
  shearLinearEquiv_apply ℤ e x

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (e : ℤ)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "m" => (LinearMap.toAddMonoidHom (Basis.coord b 1))
local notation "h" => nonneg_or_nonpos_hirzebruch_ruling_character b e r hr
local notation "U" => Φ.characterRulingTorusSubfan m h
local notation "A[" k "]" => hirzebruchRulingAffineFan b e r hr k
local notation "g" => Φ.characterRuling m h

private theorem torusSubfan_cones_subset_affine (k : Fin 2) :
    (U).cones ⊆ (A[k]).cones := by
  intro σ hσ
  obtain ⟨hσ, hz⟩ := (Φ.mem_characterRulingTorusSubfan_cones_iff m h).mp hσ
  refine (mem_hirzebruchRulingAffineFan_cones_iff b e r hr k).mpr ⟨hσ, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have he : (Φ.characterFanHom m h).realMap x = 0 := funext fun j ↦ by simp [hz x hx]
  simpa only [LinearMap.coe_restrictScalars, he] using
    (zero_mem (if k = 0 then affineRayCone else negativeRayCone))

private def torusSubfanToAffine (k : Fin 2) : FanHom U (A[k]) :=
  FanHom.ofLatticeMap _ _ (AddMonoidHom.id N) fun σ hσ ↦ by
    rw [(U).lattice.extend_id, PointedCone.map_id]
    exact ⟨σ, torusSubfan_cones_subset_affine b e r hr k hσ, le_rfl⟩

private theorem affineInclusion_comp_torusSubfanToAffine (k : Fin 2) :
    (hirzebruchRulingAffineFanInclusion b e r hr k).comp (torusSubfanToAffine b e r hr k) =
      Φ.characterRulingTorusSubfanInclusion m h := by
  apply FanHom.ext
  ext x
  simp [torusSubfanToAffine]

private theorem affineProjection_comp_torusSubfanToAffine (k : Fin 2) :
    (hirzebruchRulingAffineFanProjection b e r hr k).comp (torusSubfanToAffine b e r hr k) =
      (projectiveLineTorusToAffineFan k).comp (Φ.characterRulingTorusFanHom m h) := by
  apply FanHom.ext
  ext x j
  simp [torusSubfanToAffine]

private theorem mem_product_torus_cones_iff (k : Fin 2) {σ : PointedCone ℝ (W × W)} :
    σ ∈ (F).cones ↔
      σ ∈ (Fan.prod P₁ (projectiveLineAffineFan k)).cones ∧ ∀ x ∈ σ, x.2 = 0 := by
  constructor
  · intro hσ
    obtain ⟨ρ, hρ, τ, hτ, rfl⟩ := ((P₁).mem_prod_cones _).mp hσ
    obtain rfl := mem_projectiveLineTorusFan_cones.mp hτ
    have hbot := (projectiveLineAffineFan k).bot_mem
      (mem_projectiveLineAffineFan_cones.mpr (.refl _))
    exact ⟨((P₁).mem_prod_cones _).mpr ⟨ρ, hρ, ⊥, hbot, rfl⟩,
      fun x hx ↦ (Submodule.mem_bot (R := NNReal)).mp hx.2⟩
  · rintro ⟨hσ, hz⟩
    obtain ⟨ρ, hρ, τ, _, rfl⟩ := ((P₁).mem_prod_cones _).mp hσ
    have hτ : τ = ⊥ := le_bot_iff.mp fun y hy ↦
      (Submodule.mem_bot (R := NNReal)).mpr (hz (0, y) ⟨zero_mem _, hy⟩)
    exact ((P₁).mem_prod_cones _).mpr ⟨ρ, hρ, τ, mem_projectiveLineTorusFan_cones.mpr hτ, rfl⟩

variable (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "E[" k "]" => hirzebruchRulingAffineFanEquiv b e r hr hΦ hc k

private theorem affineEquiv_snd (k : Fin 2) (x : V) (j : Fin 1) :
    ((E[k]).realEquiv x).2 j = Φ.lattice.realCharacter m x := by
  have he := congrArg (fun f ↦ f.realMap x j)
    (snd_comp_hirzebruchRulingAffineFanEquiv b e r hr hΦ hc k)
  rw [hirzebruchRulingAffineFanProjection_realMap] at he
  simpa only [FanHom.comp_realMap, LinearMap.comp_apply, FanHom.snd_realMap,
    LinearMap.snd_apply, FanEquiv.toFanHom_realMap, LinearEquiv.coe_coe] using he

private def overlapChartFanEquiv (k : Fin 2) : FanEquiv U (F) where
  latticeEquiv := (E[k]).latticeEquiv
  realEquiv := (E[k]).realEquiv
  map_lattice := (E[k]).map_lattice
  map_mem σ := by
    rw [mem_product_torus_cones_iff k, (E[k]).map_mem,
      Φ.mem_characterRulingTorusSubfan_cones_iff m h]
    have hz : (∀ x ∈ σ.map (E[k]).realEquiv.toLinearMap, x.2 = 0) ↔
        ∀ x ∈ σ, Φ.lattice.realCharacter m x = 0 := by
      constructor
      · intro hz x hx
        have hx' := hz _ (PointedCone.mem_map.mpr ⟨x, hx, rfl⟩)
        simpa only [LinearEquiv.coe_coe, affineEquiv_snd b e r hr hΦ hc, Pi.zero_apply]
          using congrFun hx' 0
      · rintro hz _ ⟨x, hx, rfl⟩
        funext j
        simpa only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, Pi.zero_apply,
          affineEquiv_snd b e r hr hΦ hc] using hz x hx
    rw [hz]
    constructor
    · exact fun ⟨ha, hz⟩ ↦
        ⟨((mem_hirzebruchRulingAffineFan_cones_iff b e r hr k).mp ha).1, hz⟩
    · exact fun hσ ↦ ⟨torusSubfan_cones_subset_affine b e r hr k
        ((Φ.mem_characterRulingTorusSubfan_cones_iff m h).mpr hσ), hσ.2⟩

private theorem overlapChartFanEquiv_latticeEquiv (k : Fin 2) (x : N) :
    (overlapChartFanEquiv b e r hr hΦ hc k).latticeEquiv x = (E[k]).latticeEquiv x := (rfl)

private theorem snd_comp_overlapChartFanEquiv (k : Fin 2) :
    (FanHom.snd P₁ projectiveLineTorusFan).comp
        (overlapChartFanEquiv b e r hr hΦ hc k).toFanHom =
      Φ.characterRulingTorusFanHom m h := by
  apply FanHom.ext
  ext x j
  simp [FanHom.snd_latticeMap, overlapChartFanEquiv_latticeEquiv,
    hirzebruchRulingAffineFanEquiv_latticeEquiv_apply]

private theorem fst_comp_overlapChartFanEquiv (k : Fin 2) :
    (FanHom.fst P₁ projectiveLineTorusFan).comp
        (overlapChartFanEquiv b e r hr hΦ hc k).toFanHom =
      ((FanHom.fst P₁ (projectiveLineAffineFan k)).comp (E[k]).toFanHom).comp
        (torusSubfanToAffine b e r hr k) := by
  apply FanHom.ext
  ext x j
  simp [FanHom.fst_latticeMap, overlapChartFanEquiv_latticeEquiv, torusSubfanToAffine]

local notation "q" => (projectiveLineTorusFan.algebraicRealization ↘ S)
local notation "p" => (projectiveLine ℂ ↘ S)
local notation "ι[" k "]" => (FanHom.algebraicMap (projectiveLineTorusToAffineFan k))
local notation "Pₜ" => pullback p q

local notation "J" => isPullback_projectiveLineTorusProduct.isoPullback
local notation "I" => IsPullback.isoPullback (Fan.isPullback_characterRulingTorusSubfan Φ m h)

/-- The restriction of the indicated affine ruling chart over the base torus,
expressed as the product of the projective line and that torus. -/
def hirzebruchRulingTorusChartIso (k : Fin 2) :
    pullback g projectiveLineTorusι ≅ Pₜ :=
  (I).symm ≪≫ asIso (overlapChartFanEquiv b e r hr hΦ hc k).toFanHom.algebraicMap ≪≫ J

local notation "C[" k "]" => hirzebruchRulingTorusChartIso b e r hr hΦ hc k

/-- The restricted product chart is over the base torus. -/
@[reassoc (attr := simp)]
theorem hirzebruchRulingTorusChartIso_hom_snd (k : Fin 2) :
    (C[k]).hom ≫ pullback.snd p q = pullback.snd g projectiveLineTorusι := by
  simp only [hirzebruchRulingTorusChartIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    IsPullback.isoPullback_hom_snd, asIso_hom, ← FanHom.algebraicMap_comp,
    snd_comp_overlapChartFanEquiv]
  exact (Φ.isPullback_characterRulingTorusSubfan m h).isoPullback_inv_snd

private theorem torusSubfanToAffine_comp_pullback (k : Fin 2) :
    (I).hom ≫ pullback.lift (pullback.fst g projectiveLineTorusι)
        (pullback.snd g projectiveLineTorusι ≫ ι[k])
        (by rw [Category.assoc, projectiveLineTorusToAffineFan_algebraicMap_comp_ι,
          pullback.condition]) =
      (torusSubfanToAffine b e r hr k).algebraicMap ≫
        (isPullback_hirzebruchRulingAffineFan b e r hr k).isoPullback.hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst,
      ← FanHom.algebraicMap_comp, affineInclusion_comp_torusSubfanToAffine]
  · simp only [Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc,
      IsPullback.isoPullback_hom_snd, ← FanHom.algebraicMap_comp,
      affineProjection_comp_torusSubfanToAffine]

/-- Pulling the affine ruling trivialization back to the base torus gives
`hirzebruchRulingTorusChartIso`. The two inclusions use the same overlap map
on the base. -/
theorem hirzebruchRulingTorusChartIso_comp_pullback (k : Fin 2) :
    (C[k]).hom ≫ pullback.lift (pullback.fst p q) (pullback.snd p q ≫ ι[k])
        (by rw [Category.assoc, FanHom.algebraicMap_comp_algebraicRealizationStructureMap,
          ← Fan.algebraicRealization_over, pullback.condition]) =
      pullback.lift (pullback.fst g projectiveLineTorusι)
          (pullback.snd g projectiveLineTorusι ≫ ι[k])
          (by rw [Category.assoc, projectiveLineTorusToAffineFan_algebraicMap_comp_ι,
            pullback.condition]) ≫
        (hirzebruchRulingAffineIso b e r hr hΦ hc k).hom := by
  apply pullback.hom_ext
  · apply (cancel_epi (I).hom).mp
    simp only [Category.assoc, pullback.lift_fst, hirzebruchRulingTorusChartIso,
      Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc, IsPullback.isoPullback_hom_fst,
      asIso_hom]
    rw [← Category.assoc (I).hom, torusSubfanToAffine_comp_pullback, Category.assoc,
      hirzebruchRulingAffineIso_hom_fst, ← reassoc_of% FanHom.algebraicMap_comp,
      fst_comp_overlapChartFanEquiv, reassoc_of% FanHom.algebraicMap_comp,
      reassoc_of% FanHom.algebraicMap_comp]
  · simp

private theorem overlapChartFanEquiv_symm_trans :
    (overlapChartFanEquiv b e r hr hΦ hc 0).symm.trans
        (overlapChartFanEquiv b e r hr hΦ hc 1) = projectiveLineTorusShear e := by
  apply FanEquiv.ext
  apply AddEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := (overlapChartFanEquiv b e r hr hΦ hc 0).latticeEquiv.surjective x
  rw [FanEquiv.trans_latticeEquiv, FanEquiv.symm_latticeEquiv, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply, projectiveLineTorusShear_latticeEquiv_apply]
  simpa only [overlapChartFanEquiv_latticeEquiv] using
    hirzebruchRulingAffineFanEquiv_latticeEquiv_transition b e r hr hΦ hc y

private theorem snd_comp_projectiveLineTorusShear (e : ℤ) :
    (FanHom.snd P₁ projectiveLineTorusFan).comp (projectiveLineTorusShear e).toFanHom =
      FanHom.snd P₁ projectiveLineTorusFan := by
  apply FanHom.ext
  ext x j
  simp [FanHom.snd_latticeMap]

/-- The automorphism changing from the first affine product to the second on the
overlap, as an isomorphism of schemes over the base torus. -/
def hirzebruchRulingOverlapTransition (e : ℤ) : Pₜ ≅ Pₜ :=
  (J).symm ≪≫ asIso (projectiveLineTorusShear e).toFanHom.algebraicMap ≪≫ J

/-- In the product fan coordinates the overlap map is the algebraic realization
of the toric shear. -/
@[reassoc]
theorem isoPullback_hom_comp_hirzebruchRulingOverlapTransition_hom (e : ℤ) :
    (J).hom ≫ (hirzebruchRulingOverlapTransition e).hom =
      (projectiveLineTorusShear e).toFanHom.algebraicMap ≫ (J).hom := by
  simp only [hirzebruchRulingOverlapTransition, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc, asIso_hom]

/-- The overlap automorphism fixes the base torus. -/
@[reassoc (attr := simp)]
theorem hirzebruchRulingOverlapTransition_hom_snd (e : ℤ) :
    (hirzebruchRulingOverlapTransition e).hom ≫ pullback.snd p q = pullback.snd p q := by
  simp only [hirzebruchRulingOverlapTransition, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    IsPullback.isoPullback_hom_snd, asIso_hom, ← FanHom.algebraicMap_comp,
    snd_comp_projectiveLineTorusShear]
  exact isPullback_projectiveLineTorusProduct.isoPullback_inv_snd

/-- The restriction of chart one is chart zero followed by the toric shear. -/
@[reassoc]
theorem hirzebruchRulingTorusChartIso_hom_comp_overlapTransition :
    (C[0]).hom ≫ (hirzebruchRulingOverlapTransition e).hom = (C[1]).hom := by
  simp only [hirzebruchRulingTorusChartIso, hirzebruchRulingOverlapTransition,
    ← overlapChartFanEquiv_symm_trans b e r hr hΦ hc, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, Category.assoc, Iso.hom_inv_id_assoc, FanEquiv.toFanHom_trans,
    FanHom.algebraicMap_comp, FanEquiv.algebraicMap_comp_symm_assoc]

end TauCeti.Toric.Fan
