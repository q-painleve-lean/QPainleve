/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ruling.Laurent
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Scaling

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Basic
import QPainleve.Geometry.Toric.Fan.DenseTorus
import TauCeti.Geometry.Toric.Algebraic.Fan.Normal

/-!
# Toric shears as projective-line scalings

The product of the projective-line fan with the zero-cone fan realizes the
projective line over the Laurent polynomial ring. In these coordinates an
integral shear acts by a diagonal projective automorphism. This expresses
the transition of the Hirzebruch ruling charts in the projective-line
coordinates used for split projective bundles.

The comparison uses the Laurent product projections and
`projectiveLine.polynomialPoint_comp_scalingBy`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory LaurentPolynomial Limits Multiplicative PointedCone
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric

local notation "P" => Fan.projectiveSpace (Pi.basisFun ℤ (Fin 1)) (isIntegralLattice_intCast 1)
local notation "T₀" => projectiveLineTorusFan
local notation "F" => (Fan.prod P T₀)
local notation "L" => LaurentPolynomial ℂ
local notation "SL" => Spec (CommRingCat.of L)
local notation "q" => (projectiveLine L ↘ SL)
local notation "fstF" => (FanHom.fst P T₀)
local notation "sndF" => (FanHom.snd P T₀)
local notation "π₂" => FanHom.algebraicMap sndF
local notation "eT" => projectiveLineTorusIsoSpecLaurent

local notation "m(" f ")" =>
  AddMonoidHom.comp (Pi.evalAddMonoidHom (fun _ : Fin 1 ↦ ℤ) 0) (FanHom.latticeMap f)

namespace Fan

local notation "E" => projectiveLineTorusProductIsoLaurent

private theorem productFan_nonempty_cones : Nonempty (F).cones :=
  ⟨⟨(⊥ : PointedCone ℝ (Fin 1 → ℝ)).prod (⊥ : PointedCone ℝ (Fin 1 → ℝ)),
    (Fan.mem_prod_cones ..).mpr ⟨_, Fan.bot_mem_projectiveSpace_cones _ _,
      _, mem_projectiveLineTorusFan_cones.mpr rfl, rfl⟩⟩⟩

local notation "d" => Fan.denseTorusι F productFan_nonempty_cones
local notation "A" => affineCoordinateRing (Fan.lattice F) (⊥ : PointedCone ℝ _)

private def characterUnits :
    Multiplicative (((Fin 1 → ℤ) × (Fin 1 → ℤ)) →+ ℤ) →* Aˣ :=
  ((MonoidAlgebra.of ℂ _).comp
    (denseTorusDualEquiv (Fan.lattice F)).symm.toMultiplicative.toMonoidHom).toHomUnits

local notation "z(" χ ")" => characterUnits (ofAdd χ)
local notation "m₀" => m(fstF)
local notation "m₁" => m(sndF)
local notation "k" => (laurentEval z(m₁) : L →ₐ[ℂ] A)

/-- In the base projection on the dense torus, the Laurent parameter pulls back
to the character of the second factor. -/
private theorem denseTorusι_comp_laurentBase :
    d ≫ π₂ ≫ (eT).hom = Spec.map (CommRingCat.ofHom (k).toRingHom) := by
  have : IsOpenImmersion (Spec.algebraMap (Polynomial ℂ) L) :=
    IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial ℂ)
  apply (cancel_mono (Spec.algebraMap (Polynomial ℂ) L ≫
    projectiveLine.polynomialChartι ℂ 0)).mp
  simp only [Category.assoc, Spec.algebraMap,
    projectiveLineTorusIsoSpecLaurent_hom_comp_chart]
  rw [projectiveLineTorusι_def, ← reassoc_of% FanHom.algebraicMap_comp,
    FanHom.denseTorusι_comp_projectiveLineToricIso,
    projectiveLine.polynomialPoint_def, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  congr 2
  apply congrArg CommRingCat.ofHom
  apply Polynomial.ringHom_ext
  · intro a
    simp [Polynomial.coe_eval₂RingHom, LaurentPolynomial.algebraMap_eq_toLaurent,
      AlgHom.apply_laurentPolynomial_C]
  · simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RingHom.comp_apply,
      LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, laurentEval_T_one, FanHom.comp_latticeMap,
      projectiveLineTorusFanInclusion_latticeMap, AddMonoidHom.id_comp]
    rfl

private theorem denseTorusι_comp_laurentProduct (f : FanHom F F)
    (hf : FanHom.comp sndF f = sndF) :
    d ≫ f.algebraicMap ≫ (E).hom =
      projectiveLine.polynomialPoint L (k).toRingHom 0 (z(m(FanHom.comp fstF f)) : A) := by
  apply (projectiveLine.isPullback_baseChangeProjection ℂ L).hom_ext
  · simp only [Category.assoc, projectiveLineTorusProductIsoLaurent_hom_baseChangeProjection,
      ← reassoc_of% FanHom.algebraicMap_comp, FanHom.denseTorusι_comp_projectiveLineToricIso,
      projectiveLine.polynomialPoint_comp_baseChangeProjection]
    congr 1
    exact ((k).comp_algebraMap).symm
  · simp only [Category.assoc, projectiveLineTorusProductIsoLaurent_hom_toBase,
      ← reassoc_of% FanHom.algebraicMap_comp, hf, denseTorusι_comp_laurentBase,
      projectiveLine.polynomialPoint_over]

/-- In Laurent product coordinates, the lattice shear `(x, y) ↦ (x + a • y, y)`
acts as `[X₀ : X₁] ↦ [t⁻ᵃ X₀ : X₁]` over the base with Laurent parameter `t`.
In the chart with fiber coordinate `X₁ / X₀` it acts by multiplication by `tᵃ`. -/
@[reassoc]
theorem _root_.TauCeti.Toric.FanHom.algebraicMap_comp_projectiveLineTorusProductIsoLaurent_of_shear
    (f : FanHom F F) (a : ℤ) (hf : ∀ x, f.latticeMap x = (x.1 + a • x.2, x.2)) :
    f.algebraicMap ≫ (E).hom =
      (E).hom ≫ (projectiveLine.scalingBy L (isUnit_T (-a)).unit).hom := by
  have hsnd : FanHom.comp sndF f = sndF := by
    apply FanHom.ext
    ext x j
    simp [FanHom.comp_latticeMap, FanHom.snd_latticeMap, hf]
  have hfst : m(FanHom.comp fstF f) = m₀ + a • m₁ := by
    ext x
    simp [FanHom.comp_latticeMap, FanHom.fst_latticeMap, FanHom.snd_latticeMap, hf]
  refine AlgebraicGeometry.ext_of_isDominant_of_isSeparated q ?_ d ?_
  · simp only [Category.assoc, projectiveLine.scalingBy_hom_over,
      projectiveLineTorusProductIsoLaurent_hom_toBase, ← reassoc_of% FanHom.algebraicMap_comp, hsnd]
  · have hid := denseTorusι_comp_laurentProduct (FanHom.id F) (by simp)
    simp only [FanHom.algebraicMap_id, Category.id_comp, FanHom.comp_id] at hid
    have hrev : (0 : Fin 2).rev = 1 := rfl
    rw [denseTorusι_comp_laurentProduct f hsnd, hfst,
      ← Category.assoc d, hid, projectiveLine.polynomialPoint_rev _ 0 z(m₀),
      projectiveLine.polynomialPoint_rev _ 0 z(m₀ + a • m₁), hrev,
      projectiveLine.polynomialPoint_comp_scalingBy]
    simp only [ofAdd_add, ofAdd_zsmul, map_mul, map_zpow, mul_inv_rev, Units.val_mul,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, IsUnit.unit_spec, laurentEval_T, zpow_neg]

end Fan

end TauCeti.Toric
