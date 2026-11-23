/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Orthogonal
public import QPainleve.Geometry.Toric.Fan.Picard.ChargeKernel
public import QPainleve.Geometry.Toric.Fan.Picard.NodalDescent

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Blowup.Tower.Numerical
import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import QPainleve.Geometry.Toric.Fan.Smooth
import TauCeti.LinearAlgebra.Matrix.Dual

/-!
# The boundary orthogonal lattice of a toric presentation

The Picard orthogonal complement of the boundary on the original surface is identified
with the integral charge kernel by intersecting the pullback with the total exceptional
classes on the internal blowup model. The comparison is compatible with the ordered
Picard marking. In the inverse direction it yields a toric class of prescribed boundary
degrees and exceptional coefficients given by the negatives of the charge coordinates.

This is the marked Picard calculation of Gross, Hacking and Keel, *Birational geometry
of cluster algebras*, Theorem 5.5. The nodal and internal towers can both be empty.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass LinearMap.BilinForm
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}

local notation "Z" => Φ.algebraicRealization
local notation "fZ" => (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ))
local notation "Dtor" => Φ.boundaryIdeal inferInstance
local notation "Pic(" S ")" => Additive (LineBundleClass S)

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (hΦ : Φ.IsRegular) (hdim : Module.finrank ℤ N = 2)
  (s : Fin n → Φ.Ray) (m : Fin n → N →+ ℤ)
  (hm : ∀ j, m j (s j).primitiveGenerator = 0) (hprim : ∀ j, Function.Surjective (m j))
  (c : Fin n → ℂˣ)
  (J : Fin n →
    {I : (Φ.boundaryIdeal inferInstance).subscheme.IdealSheafData // I.IsEffectiveCartier})
  (hJ : ∀ j, (J j).val = ((s j).binomialCenterOnBoundary hdim (hm j) (hprim j) (c j)).ker)

local notation "model" => (alongBoundary (subschemeι Dtor) J)
local notation "W" => Sigma.fst model
local notation "U" => WithBoundary.toTower (Sigma.snd model)
local notation "hU" => isClosedPointTower_alongBoundary_binomialCenters hdim s m hm hprim c J hJ
local notation "Dint" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd model))
omit [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ] in
include hΦ hdim in
private theorem smooth_toric_surface :
    SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (.of ℂ)) :=
  hdim ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
local notation "smoothZ" => smooth_toric_surface hΦ hdim
local notation "A₁" =>
  (@Chow.intersectionBilinForm ℂ _ _ Z inferInstance inferInstance inferInstance smoothZ)
local notation "S₁" => LinearMap.range (markedBoundaryMap hΦ s)

variable {X Y : Scheme} [X.Over (Spec (.of ℂ))] [X.IsProjectiveOver ℂ] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))]
  {D : X.IdealSheafData} {d : ℕ} {T : QPainleve.BlowupTower X d Y}
  (hT : IsNodalBoundaryTower D (X ↘ Spec (.of ℂ)) (𝟙 X) T)
  (e : Y ≅ (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι J).1)
  (he : e.inv ≫ T.toBase ≫ (X ↘ Spec (.of ℂ)) =
    (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι J).2.toTower.toBase ≫
      (Φ.algebraicRealization ↘ Spec (.of ℂ)))
  (hD : ((D.comap T.toBase).comap e.inv).support =
    (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι J).2.boundaryι.ker.support)

local notation "fX" => (X ↘ Spec (CommRingCat.of ℂ))
local notation "A₀" => Chow.intersectionBilinForm ℂ X
local notation "M₀" =>
  Scheme.Opens.primeDivisorSpanCompl (Closeds.compl (Scheme.IdealSheafData.support D))
local notation "V₀" => Closeds.compl (Scheme.IdealSheafData.support (D.comap T.toBase))
local notation "V₁" => Closeds.compl (Scheme.IdealSheafData.support Dint)
local notation "negDot" r => (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))
local notation "B₀" => (LinearMap.BilinForm.prod A₀ (negDot d))
local notation "B₁" => (LinearMap.BilinForm.prod A₁ (negDot n))

local instance : IsNoetherian X := isNoetherian_of_finiteType fX
local instance : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
  (fX).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two

include hΦ hJ hT e in
private def resolutionMarking :
    (Pic(X) × (Fin d → ℤ)) ≃ₗ[ℤ] (Pic(Z) × (Fin n → ℤ)) :=
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  picardEquivOfCommonResolution ℂ hT.isClosedPointTower hU e.symm

local notation "E" => resolutionMarking hΦ hdim s m hm hprim c J hJ hT e

omit [Φ.algebraicRealization.IsProjectiveOver ℂ] in
include hJ hT in
private theorem internal_picardHom_resolutionMarking (a : Pic(X) × (Fin d → ℤ)) :
    (U).picardHom (E a) = Additive.ofMul (pullback e.inv (T.picardHom a).toMul) := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  exact picardHom_picardEquivOfCommonResolution ℂ hT.isClosedPointTower hU e.symm a

include hJ hT he in
private theorem pairing_resolutionMarking (a b : Pic(X) × (Fin d → ℤ)) :
    B₁ (E a) (E b) = B₀ a b := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  simpa only [LinearMap.BilinForm.prod_apply, Chow.intersectionBilinForm_apply, LinearMap.neg_apply,
    dotProductBilin_apply_apply, dotProduct, sub_eq_add_neg, resolutionMarking] using
    classIntersectionNumber_picardEquivOfCommonResolution ℂ hT.isClosedPointTower hU e.symm he a b

omit [Φ.algebraicRealization.IsProjectiveOver ℂ] in
include hΦ hJ e in
private def internalMarking : Pic(Y) ≃ₗ[ℤ] (Pic(Z) × (Fin n → ℤ)) :=
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  ((pullbackEquiv e.symm).toAdditive.toIntLinearEquiv).trans ((U).picardMarking hU fZ).symm

local notation "F" => internalMarking hΦ hdim s m hm hprim c J hJ e

omit [Φ.algebraicRealization.IsProjectiveOver ℂ] in
include hΦ hJ in
private theorem internal_picardHom_internalMarking (a : Pic(Y)) :
    (U).picardHom (F a) = Additive.ofMul (pullback e.inv a.toMul) := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  rw [← (U).picardMarking_apply hU fZ, internalMarking, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  change Additive.ofMul (pullbackEquiv e.symm a.toMul) = _
  rw [pullbackEquiv_apply]
  rfl

omit [Φ.algebraicRealization.IsProjectiveOver ℂ] [X.Over (Spec (.of ℂ))]
  [X.IsProjectiveOver ℂ] [IsIntegral X] [SmoothOfRelativeDimension 2 fX] in
include hJ hD in
private theorem internalMarking_mem_markedBoundary_iff [IsNoetherian Y] [IsIntegral Y]
    [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (a : Pic(Y)) :
    F a ∈ S₁ ↔ a ∈ Scheme.Opens.primeDivisorSpanCompl V₀ := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  let : IsNoetherian W := (U).isNoetherian
  let : IsIntegral W := (hU).isIntegral fZ
  let : SmoothOfRelativeDimension 2 ((U).toBase ≫ fZ) := (hU).smoothOfRelativeDimension fZ
  let := ((U).toBase ≫ fZ).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hUopen : e.inv ⁻¹ᵁ V₀ = V₁ := by
    rw [← compl_support_comap, hD]
  have hspan := map_range_markedBoundaryMap_picardHom hΦ hdim s m hm hprim c J hJ hU
  have hmap := Submodule.comap_map_eq_of_injective ((hU).bijective_picardHom fZ).injective S₁
  rw [← hmap, Submodule.mem_comap, hspan,
    ← primeDivisorSpanCompl_internalBlowup hΦ hdim s m hm hprim c J hJ,
    internal_picardHom_internalMarking hΦ hdim s m hm hprim c J hJ e,
    ← hUopen, ← Submodule.Quotient.mk_eq_zero,
    ← Scheme.Hom.quotientPrimeDivisorSpanComplEquiv_mk, LinearEquiv.map_eq_zero_iff,
    Submodule.Quotient.mk_eq_zero, ofMul_toMul]

include hJ hT he hD in
private def orthogonalMarking : (A₀).orthogonal M₀ ≃ₗ[ℤ] (B₁).orthogonal S₁ := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  let : IsNoetherian Y := T.isNoetherian
  let : Y.Over (Spec (.of ℂ)) := ⟨T.toBase ≫ fX⟩
  let : Y.IsProjectiveOver ℂ := T.isProjectiveOver ℂ
  let : IsIntegral Y := hT.isClosedPointTower.isIntegral fX
  let : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of ℂ)) :=
    hT.isClosedPointTower.smoothOfRelativeDimension fX
  let : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y) :=
    (Y ↘ Spec (.of ℂ)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let : (W).Over (Spec (.of ℂ)) := ⟨(U).toBase ≫ fZ⟩
  let : e.inv.IsOver (Spec (.of ℂ)) := ⟨he⟩
  have hpair (a b : Pic(Y)) : B₁ (F a) (F b) = Chow.intersectionBilinForm ℂ Y a b := by
    have hmark (x y : Pic(Z) × (Fin n → ℤ)) :
        Chow.classIntersectionNumber ℂ W ((U).picardHom x).toMul ((U).picardHom y).toMul =
          B₁ x y := by
      simpa only [picardMarking_apply, LinearMap.BilinForm.prod_apply,
        Chow.intersectionBilinForm_apply, LinearMap.neg_apply, dotProductBilin_apply_apply,
        dotProduct, sub_eq_add_neg] using classIntersectionNumber_picardMarking ℂ hU x y
    rw [← hmark, Chow.intersectionBilinForm_apply, internal_picardHom_internalMarking,
      internal_picardHom_internalMarking, toMul_ofMul, toMul_ofMul]
    exact Chow.classIntersectionNumber_pullback_of_isIso ℂ e.inv a.toMul b.toMul
  have hmem (a : Pic(Y)) :
      F a ∈ (B₁).orthogonal S₁ ↔
        a ∈ (Chow.intersectionBilinForm ℂ Y).orthogonal
          (Scheme.Opens.primeDivisorSpanCompl V₀) := by
    simp only [mem_orthogonal_iff]
    rw [(F).surjective.forall (p := fun z ↦ z ∈ S₁ → B₁ z (F a) = 0)]
    simp only [internalMarking_mem_markedBoundary_iff hΦ hdim s m hm hprim c J hJ e hD, hpair]
  refine (hT.boundaryOrthogonalIsometry ℂ).toLinearEquiv.trans ((F).ofSubmodules _ _ ?_)
  ext z
  obtain ⟨a, rfl⟩ := (F).surjective z
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, hmem]

include hJ hT he hD in
private theorem coe_orthogonalMarking (κ : (A₀).orthogonal M₀) :
    (orthogonalMarking hΦ hdim s m hm hprim c J hJ hT e he hD κ : Pic(Z) × (Fin n → ℤ)) =
      E (κ.val, 0) := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  change F (hT.boundaryOrthogonalIsometry ℂ κ : Pic(Y)) = _
  apply ((hU).bijective_picardHom fZ).injective
  rw [internal_picardHom_internalMarking, hT.boundaryOrthogonalIsometry_apply ℂ,
    internal_picardHom_resolutionMarking, picardHom_apply_zero, toMul_ofMul]

variable [LinearMap.IsPerfPair (Chow.intersectionBilinForm ℂ X)]

include hJ hT he in
private theorem isPerfPair_internal_markedForm : (B₁).IsPerfPair := by
  have hneg : (negDot d).IsPerfPair := by
    convert LinearMap.IsPerfPair.compl₁₂
      (dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin d → ℤ))
      (LinearEquiv.neg ℤ) (LinearEquiv.refl ℤ _) using 1
    ext x y
    simp
  let : (B₀).IsPerfPair := LinearMap.BilinForm.isPerfPair_prod_iff.mpr ⟨inferInstance, hneg⟩
  apply LinearMap.IsPerfPair.congr B₀ (E).symm (E).symm B₁
  apply LinearMap.ext₂
  intro a b
  simpa only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm] using
    pairing_resolutionMarking hΦ hdim s m hm hprim c J hJ hT e he a b

include hJ hT he hD in
/-- In an ordered toric presentation the integral boundary orthogonal is the charge kernel.
The ambient intersection pairing is perfect, as for a smooth projective rational surface.
The charge image can have any rank. -/
def picardBoundaryOrthogonalEquivChargeKernel : (A₀).orthogonal M₀ ≃ₗ[ℤ] (rayChargeMap s).ker :=
  let := isPerfPair_internal_markedForm hΦ hdim s m hm hprim c J hJ hT e he
  (orthogonalMarking hΦ hdim s m hm hprim c J hJ hT e he hD).trans
    (boundaryOrthogonalEquivChargeKernel hΦ s B₁)

local notation "q" =>
  picardBoundaryOrthogonalEquivChargeKernel hΦ hdim s m hm hprim c J hJ hT e he hD

include hJ hT he hD in
/-- The inverse charge comparison pulls back to the toric class of the prescribed boundary
degrees minus the total exceptional classes weighted by the charge coordinates. -/
theorem exists_picardBoundaryOrthogonalEquivChargeKernel_symm_marking
    (x : (rayChargeMap s).ker) :
    ∃ H : Pic(Z), ((U).picardHom (H, -(x : Fin n → ℤ))).toMul =
        pullback (e.inv ≫ T.toBase) ((q).symm x).val.toMul ∧
      ∀ G : Pic(Z), (∀ v : Φ.Ray → ℤ, Chow.classIntersectionNumber ℂ Z
        (Φ.rayDivisorToPicard hΦ v).toMul G.toMul = ∑ j, v (s j) * (x : Fin n → ℤ) j) ↔
        G = H := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  let := isPerfPair_internal_markedForm hΦ hdim s m hm hprim c J hJ hT e he
  let y := (boundaryOrthogonalEquivChargeKernel hΦ s B₁).symm x
  have hy : (y : Pic(Z) × (Fin n → ℤ)) = E (((q).symm x).val, 0) := by
    rw [← coe_orthogonalMarking hΦ hdim s m hm hprim c J hJ hT e he hD]
    exact congrArg Subtype.val
      ((orthogonalMarking hΦ hdim s m hm hprim c J hJ hT e he hD).apply_symm_apply y).symm
  have hsecond := boundaryOrthogonalEquivChargeKernel_symm_snd hΦ s A₁ x
  have hpic : ((U).picardHom (y.val.1, -(x : Fin n → ℤ))).toMul =
      pullback (e.inv ≫ T.toBase) ((q).symm x).val.toMul := by
    rw [← hsecond, Prod.mk.eta, hy]
    have h := internal_picardHom_resolutionMarking hΦ hdim s m hm hprim c J hJ hT e
      (((q).symm x).val, 0)
    simpa only [picardHom_apply_zero, toMul_ofMul, pullback_comp] using congrArg Additive.toMul h
  refine ⟨y.val.1, hpic, fun G ↦ ?_⟩
  obtain ⟨H, _, hunique⟩ := existsUnique_rayDivisorToPicard_pairing_eq_charge hΦ s A₁ x
  have hdegree := boundaryOrthogonalEquivChargeKernel_symm_fst_pairing hΦ s A₁ x
  constructor
  · intro hG
    have hGH := hunique G (by simpa only [Chow.intersectionBilinForm_apply] using hG)
    exact hGH.trans (hunique y.val.1 hdegree).symm
  · rintro rfl
    simpa only [Chow.intersectionBilinForm_apply] using hdegree

include hJ hT he hD in
/-- Pulling an orthogonal class to the internal model and intersecting it with the total
exceptional class at label `j` gives its `j`-th charge coordinate. -/
@[simp] theorem picardBoundaryOrthogonalEquivChargeKernel_apply
    (κ : (A₀).orthogonal M₀) (j : Fin n) :
    let : (W).Over (Spec (.of ℂ)) := ⟨(U).toBase ≫ fZ⟩
    (q κ : Fin n → ℤ) j = Chow.classIntersectionNumber ℂ W
      (pullback (e.inv ≫ T.toBase) κ.val.toMul) ((U).exceptionalClass j) := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  let : (W).Over (Spec (.of ℂ)) := ⟨(U).toBase ≫ fZ⟩
  let := isPerfPair_internal_markedForm hΦ hdim s m hm hprim c J hJ hT e he
  let z := E (κ.val, 0)
  have hz := internal_picardHom_resolutionMarking hΦ hdim s m hm hprim c J hJ hT e (κ.val, 0)
  have hκ : ((U).picardHom z).toMul = pullback (e.inv ≫ T.toBase) κ.val.toMul := by
    simpa only [z, picardHom_apply_zero, toMul_ofMul, pullback_comp] using
      congrArg Additive.toMul hz
  have hx : ((U).picardHom (0, Pi.single j 1)).toMul = (U).exceptionalClass j := by
    simpa only [zpow_one] using (U).picardHom_apply_single j 1
  dsimp only
  rw [Chow.classIntersectionNumber_comm, ← hx, ← hκ,
    ← picardMarking_apply U hU fZ, ← picardMarking_apply U hU fZ,
    classIntersectionNumber_picardMarking ℂ hU]
  exact (boundaryOrthogonalEquivChargeKernel_apply hΦ s B₁
    (orthogonalMarking hΦ hdim s m hm hprim c J hJ hT e he hD κ) j).trans
      (by simp [coe_orthogonalMarking, LinearMap.BilinForm.prod_apply,
        dotProductBilin_apply_apply, dotProduct, z])

include hJ hT he hD in
/-- The integral intersection form on the charge kernel of the presentation, transported
from the original surface's boundary orthogonal complement. -/
def chargeKernelIntersectionForm : LinearMap.BilinForm ℤ (rayChargeMap s).ker :=
  LinearMap.BilinForm.congr q ((A₀).restrict ((A₀).orthogonal M₀))

include hJ hT he hD in
/-- The transported charge pairing evaluates by intersection of the inverse images on
the original surface. -/
@[simp] theorem chargeKernelIntersectionForm_apply (x y : (rayChargeMap s).ker) :
    chargeKernelIntersectionForm hΦ hdim s m hm hprim c J hJ hT e he hD x y =
      A₀ ((q).symm x).val ((q).symm y).val := by
  simp only [chargeKernelIntersectionForm, LinearMap.BilinForm.congr_apply,
    LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]

include hJ hT he hD in
/-- In the internal model, the charge pairing is the intersection of the toric coordinates
minus the dot product of the charge vectors. The same comparison applies to self-intersections. -/
theorem chargeKernelIntersectionForm_eq_classIntersectionNumber_sub_dotProduct
    (x y : (rayChargeMap s).ker) (H G : Pic(Z))
    (hx : ((U).picardHom (H, -(x : Fin n → ℤ))).toMul =
      pullback (e.inv ≫ T.toBase) ((q).symm x).val.toMul)
    (hy : ((U).picardHom (G, -(y : Fin n → ℤ))).toMul =
      pullback (e.inv ≫ T.toBase) ((q).symm y).val.toMul) :
    chargeKernelIntersectionForm hΦ hdim s m hm hprim c J hJ hT e he hD x y =
      Chow.classIntersectionNumber ℂ Z H.toMul G.toMul -
        ∑ j, (x : Fin n → ℤ) j * (y : Fin n → ℤ) j := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  have hmark (z : (rayChargeMap s).ker) (L : Pic(Z))
      (hz : ((U).picardHom (L, -(z : Fin n → ℤ))).toMul =
        pullback (e.inv ≫ T.toBase) ((q).symm z).val.toMul) :
      E (((q).symm z).val, 0) = (L, -(z : Fin n → ℤ)) := by
    apply ((hU).bijective_picardHom fZ).injective
    rw [internal_picardHom_resolutionMarking hΦ hdim s m hm hprim c J hJ hT e]
    simp only [picardHom_apply_zero, pullback_comp] at hz ⊢
    exact (congrArg Additive.ofMul hz).symm
  have hp := pairing_resolutionMarking hΦ hdim s m hm hprim c J hJ hT e he
    (((q).symm x).val, 0) (((q).symm y).val, 0)
  rw [hmark x H hx, hmark y G hy] at hp
  simpa only [LinearMap.BilinForm.prod_apply, Chow.intersectionBilinForm_apply,
    LinearMap.neg_apply, dotProductBilin_apply_apply, dotProduct, Prod.fst, Prod.snd,
    Pi.neg_apply, neg_mul_neg, Pi.zero_apply, zero_mul, Finset.sum_const_zero, neg_zero,
    add_zero, sub_eq_add_neg, chargeKernelIntersectionForm_apply] using hp.symm

end TauCeti.Toric.Fan
