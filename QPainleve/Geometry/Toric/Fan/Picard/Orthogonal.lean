/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Orthogonal
public import QPainleve.Geometry.Toric.Fan.Picard.ChargeKernel
public import QPainleve.Geometry.Toric.Fan.Picard.NodalDescent
public import QPainleve.Geometry.Toric.BaseChange.Fan

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Reflection
import QPainleve.Algebra.Cluster.ChargeKernel.Index
import QPainleve.AlgebraicGeometry.Blowup.Tower.Numerical
import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import QPainleve.Geometry.Toric.Fan.Picard.Norm.Congruence
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

variable (k : Type) [Field k] [IsAlgClosed k]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}

local notation "Z" => (Φ.finiteFanScheme k)
local notation "fZ" => ((Φ.finiteFanScheme k) ↘ (Spec (CommRingCat.of k)))
local notation "Dtor" => Φ.toricBoundaryIdeal k inferInstance
local notation "Pic(" S ")" => Additive (LineBundleClass S)

variable [(Φ.finiteFanScheme k).IsProjectiveOver k]
  (hΦ : Φ.IsRegular) (hdim : Module.finrank ℤ N = 2)
  (s : Fin n → Φ.Ray) (m : Fin n → N →+ ℤ)
  (hm : ∀ j, m j (s j).primitiveGenerator = 0) (hprim : ∀ j, Function.Surjective (m j))
  (c : Fin n → kˣ)
  (J : Fin n →
    {I : (Φ.toricBoundaryIdeal k inferInstance).subscheme.IdealSheafData // I.IsEffectiveCartier})
  (hJ : ∀ j, (J j).val = ((s j).binomialCenterOnBoundary k hdim (hm j) (hprim j) (c j)).ker)

local notation "model" => (alongBoundary (subschemeι Dtor) J)
local notation "W" => Sigma.fst model
local notation "U" => WithBoundary.toTower (Sigma.snd model)
local notation "hU" => isClosedPointTower_alongBoundary_binomialCenters k hdim s m hm hprim c J hJ
local notation "Dint" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd model))
local notation "smoothZ" =>
  cast (congrArg (fun d ↦ SmoothOfRelativeDimension d fZ) hdim)
    (Eq.mpr (congrArg (SmoothOfRelativeDimension _) (Φ.finiteFanScheme_over k))
      (Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ))
local notation "A₁" =>
  (@Chow.intersectionBilinForm k _ _ Z inferInstance inferInstance inferInstance smoothZ)
local notation "S₁" => LinearMap.range (markedBoundaryMap k hΦ s)

variable {X Y : Scheme} [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ (Spec (.of k)))]
  {D : X.IdealSheafData} {d : ℕ} {T : QPainleve.BlowupTower X d Y}
  (hT : IsNodalBoundaryTower D (X ↘ (Spec (.of k))) (𝟙 X) T)
  (e : Y ≅ (alongBoundary (Φ.toricBoundaryIdeal k inferInstance).subschemeι J).1)
  (he : e.inv ≫ T.toBase ≫ (X ↘ (Spec (.of k))) =
    (alongBoundary (Φ.toricBoundaryIdeal k inferInstance).subschemeι J).2.toTower.toBase ≫
      ((Φ.finiteFanScheme k) ↘ (Spec (.of k))))
  (hD : ((D.comap T.toBase).comap e.inv).support =
    (alongBoundary (Φ.toricBoundaryIdeal k inferInstance).subschemeι J).2.boundaryι.ker.support)

local notation "fX" => (X ↘ (Spec (CommRingCat.of k)))
local notation "A₀" => Chow.intersectionBilinForm k X
local notation "M₀" =>
  (@Scheme.Opens.primeDivisorSpanCompl X
    (LocallyOfFiniteType.isLocallyNoetherian fX) inferInstance
    (Scheme.Hom.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two fX)
    (Closeds.compl (Scheme.IdealSheafData.support D)))
local notation "V₀" => Closeds.compl (Scheme.IdealSheafData.support (D.comap T.toBase))
local notation "V₁" => Closeds.compl (Scheme.IdealSheafData.support Dint)
local notation "negDot" r => (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))
local notation "B₀" => (LinearMap.BilinForm.prod A₀ (negDot d))
local notation "B₁" => (LinearMap.BilinForm.prod A₁ (negDot n))

include hΦ hJ hT e in
private def resolutionMarking :
    (Pic(X) × (Fin d → ℤ)) ≃ₗ[ℤ] (Pic(Z) × (Fin n → ℤ)) :=
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  let : IsNoetherian X := isNoetherian_of_finiteType fX
  picardEquivOfCommonResolution k hT.isClosedPointTower hU e.symm

local notation "E" => resolutionMarking k hΦ hdim s m hm hprim c J hJ hT e

omit [(Φ.finiteFanScheme k).IsProjectiveOver k] in
include hJ hT in
private theorem internal_picardHom_resolutionMarking (a : Pic(X) × (Fin d → ℤ)) :
    (U).picardHom (E a) = Additive.ofMul (pullback e.inv (T.picardHom a).toMul) := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  let : IsNoetherian X := isNoetherian_of_finiteType fX
  exact picardHom_picardEquivOfCommonResolution k hT.isClosedPointTower hU e.symm a

include hJ hT he in
private theorem pairing_resolutionMarking (a b : Pic(X) × (Fin d → ℤ)) :
    B₁ (E a) (E b) = B₀ a b := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  let : IsNoetherian X := isNoetherian_of_finiteType fX
  simpa only [LinearMap.BilinForm.prod_apply, Chow.intersectionBilinForm_apply, LinearMap.neg_apply,
    dotProductBilin_apply_apply, dotProduct, sub_eq_add_neg, resolutionMarking] using
    classIntersectionNumber_picardEquivOfCommonResolution k hT.isClosedPointTower hU e.symm he a b

omit [(Φ.finiteFanScheme k).IsProjectiveOver k] in
include hΦ hJ e in
private def internalMarking : Pic(Y) ≃ₗ[ℤ] (Pic(Z) × (Fin n → ℤ)) :=
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  ((pullbackEquiv e.symm).toAdditive.toIntLinearEquiv).trans ((U).picardMarking hU fZ).symm

local notation "F" => internalMarking k hΦ hdim s m hm hprim c J hJ e

omit [(Φ.finiteFanScheme k).IsProjectiveOver k] in
include hΦ hJ in
private theorem internal_picardHom_internalMarking (a : Pic(Y)) :
    (U).picardHom (F a) = Additive.ofMul (pullback e.inv a.toMul) := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  rw [← (U).picardMarking_apply hU fZ, internalMarking, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  change Additive.ofMul (pullbackEquiv e.symm a.toMul) = _
  rw [pullbackEquiv_apply]
  rfl

omit [(Φ.finiteFanScheme k).IsProjectiveOver k] [X.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [IsIntegral X] [SmoothOfRelativeDimension 2 fX] in
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
  have hspan := map_range_markedBoundaryMap_picardHom k hΦ hdim s m hm hprim c J hJ hU
  have hmap := Submodule.comap_map_eq_of_injective ((hU).bijective_picardHom fZ).injective S₁
  rw [← hmap, Submodule.mem_comap, hspan,
    ← primeDivisorSpanCompl_internalBlowup k hΦ hdim s m hm hprim c J hJ,
    internal_picardHom_internalMarking k hΦ hdim s m hm hprim c J hJ e,
    ← hUopen, ← Submodule.Quotient.mk_eq_zero,
    ← Scheme.Hom.quotientPrimeDivisorSpanComplEquiv_mk, LinearEquiv.map_eq_zero_iff,
    Submodule.Quotient.mk_eq_zero, ofMul_toMul]

include hJ hT he hD in
private def orthogonalMarking : (A₀).orthogonal M₀ ≃ₗ[ℤ] (B₁).orthogonal S₁ := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  let : IsNoetherian X := isNoetherian_of_finiteType fX
  let : IsNoetherian Y := T.isNoetherian
  let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ fX⟩
  let : Y.IsProjectiveOver k := T.isProjectiveOver k
  let : IsIntegral Y := hT.isClosedPointTower.isIntegral fX
  let : SmoothOfRelativeDimension 2 (Y ↘ (Spec (.of k))) :=
    hT.isClosedPointTower.smoothOfRelativeDimension fX
  let : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y) :=
    (Y ↘ (Spec (.of k))).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let : (W).Over (Spec (.of k)) := ⟨(U).toBase ≫ fZ⟩
  let : e.inv.IsOver (Spec (.of k)) := ⟨he⟩
  have hpair (a b : Pic(Y)) : B₁ (F a) (F b) = Chow.intersectionBilinForm k Y a b := by
    have hmark (x y : Pic(Z) × (Fin n → ℤ)) :
        Chow.classIntersectionNumber k W ((U).picardHom x).toMul ((U).picardHom y).toMul =
          B₁ x y := by
      simpa only [picardMarking_apply, LinearMap.BilinForm.prod_apply,
        Chow.intersectionBilinForm_apply, LinearMap.neg_apply, dotProductBilin_apply_apply,
        dotProduct, sub_eq_add_neg] using classIntersectionNumber_picardMarking k hU x y
    rw [← hmark, Chow.intersectionBilinForm_apply, internal_picardHom_internalMarking,
      internal_picardHom_internalMarking, toMul_ofMul, toMul_ofMul]
    exact Chow.classIntersectionNumber_pullback_of_isIso k e.inv a.toMul b.toMul
  have hmem (a : Pic(Y)) :
      F a ∈ (B₁).orthogonal S₁ ↔
        a ∈ (Chow.intersectionBilinForm k Y).orthogonal
          (Scheme.Opens.primeDivisorSpanCompl V₀) := by
    simp only [mem_orthogonal_iff]
    rw [(F).surjective.forall (p := fun z ↦ z ∈ S₁ → B₁ z (F a) = 0)]
    simp only [internalMarking_mem_markedBoundary_iff k hΦ hdim s m hm hprim c J hJ e hD, hpair]
  refine (hT.boundaryOrthogonalIsometry k).toLinearEquiv.trans ((F).ofSubmodules _ _ ?_)
  ext z
  obtain ⟨a, rfl⟩ := (F).surjective z
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, hmem]

include hJ hT he hD in
private theorem coe_orthogonalMarking (κ : (A₀).orthogonal M₀) :
    (orthogonalMarking k hΦ hdim s m hm hprim c J hJ hT e he hD κ : Pic(Z) × (Fin n → ℤ)) =
      E (κ.val, 0) := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  let : IsNoetherian X := isNoetherian_of_finiteType fX
  change F (hT.boundaryOrthogonalIsometry k κ : Pic(Y)) = _
  apply ((hU).bijective_picardHom fZ).injective
  rw [internal_picardHom_internalMarking, hT.boundaryOrthogonalIsometry_apply k,
    internal_picardHom_resolutionMarking, picardHom_apply_zero, toMul_ofMul]

variable [LinearMap.IsPerfPair (Chow.intersectionBilinForm k X)]

include hJ hT he in
/-- The perfect intersection pairing of the original surface gives a perfect pairing
on the toric Picard marking of its nodal refinement. -/
theorem isPerfPair_internal_markedForm : (B₁).IsPerfPair := by
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
    pairing_resolutionMarking k hΦ hdim s m hm hprim c J hJ hT e he a b

include hJ hT he hD in
/-- In an ordered toric presentation the integral boundary orthogonal is the charge kernel.
The ambient intersection pairing is perfect, as for a smooth projective rational surface.
The charge image can have any rank. -/
def picardBoundaryOrthogonalEquivChargeKernel : (A₀).orthogonal M₀ ≃ₗ[ℤ] (rayChargeMap s).ker :=
  let := isPerfPair_internal_markedForm k hΦ hdim s m hm hprim c J hJ hT e he
  (orthogonalMarking k hΦ hdim s m hm hprim c J hJ hT e he hD).trans
    (boundaryOrthogonalEquivChargeKernel k hΦ s B₁)

local notation "q" =>
  picardBoundaryOrthogonalEquivChargeKernel k hΦ hdim s m hm hprim c J hJ hT e he hD

include hJ hT he hD in
private theorem coe_markedChargeKernelEquiv_symm (x : (rayChargeMap s).ker) :
    let _ := isPerfPair_internal_markedForm k hΦ hdim s m hm hprim c J hJ hT e he
    ((boundaryOrthogonalEquivChargeKernel k hΦ s B₁).symm x).val =
      E (((q).symm x).val, 0) := by
  intro _
  let y := (boundaryOrthogonalEquivChargeKernel k hΦ s B₁).symm x
  rw [← coe_orthogonalMarking k hΦ hdim s m hm hprim c J hJ hT e he hD]
  exact congrArg Subtype.val
    ((orthogonalMarking k hΦ hdim s m hm hprim c J hJ hT e he hD).apply_symm_apply y).symm

include hJ hT he hD in
/-- The inverse charge comparison on the original surface pulls back to the inverse
charge comparison in the toric Picard marking. -/
theorem picardHom_boundaryOrthogonalEquivChargeKernel_symm (x : (rayChargeMap s).ker) :
    letI := isPerfPair_internal_markedForm k hΦ hdim s m hm hprim c J hJ hT e he
    ((U).picardHom ((boundaryOrthogonalEquivChargeKernel k hΦ s B₁).symm x).val).toMul =
      pullback (e.inv ≫ T.toBase) ((q).symm x).val.toMul := by
  rw [coe_markedChargeKernelEquiv_symm k hΦ hdim s m hm hprim c J hJ hT e he hD]
  have h := internal_picardHom_resolutionMarking k hΦ hdim s m hm hprim c J hJ hT e
    (((q).symm x).val, 0)
  simpa only [picardHom_apply_zero, toMul_ofMul, pullback_comp] using congrArg Additive.toMul h

include hJ hT he hD in
/-- The inverse charge comparison pulls back to the toric class of the prescribed boundary
degrees minus the total exceptional classes weighted by the charge coordinates. -/
theorem exists_picardBoundaryOrthogonalEquivChargeKernel_symm_marking
    (x : (rayChargeMap s).ker) :
    ∃ H : Pic(Z), ((U).picardHom (H, -(x : Fin n → ℤ))).toMul =
        pullback (e.inv ≫ T.toBase) ((q).symm x).val.toMul ∧
      ∀ G : Pic(Z), (∀ v : Φ.Ray → ℤ, Chow.classIntersectionNumber k Z
        (Φ.rayChartDivisorToPicard k hΦ v).toMul G.toMul = ∑ j, v (s j) * (x : Fin n → ℤ) j) ↔
        G = H := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  let := isPerfPair_internal_markedForm k hΦ hdim s m hm hprim c J hJ hT e he
  let y := (boundaryOrthogonalEquivChargeKernel k hΦ s B₁).symm x
  have hsecond := boundaryOrthogonalEquivChargeKernel_symm_snd k hΦ s A₁ x
  have hpic : ((U).picardHom (y.val.1, -(x : Fin n → ℤ))).toMul =
      pullback (e.inv ≫ T.toBase) ((q).symm x).val.toMul := by
    rw [← hsecond, Prod.mk.eta]
    exact picardHom_boundaryOrthogonalEquivChargeKernel_symm k
      hΦ hdim s m hm hprim c J hJ hT e he hD x
  refine ⟨y.val.1, hpic, fun G ↦ ?_⟩
  obtain ⟨H, _, hunique⟩ := existsUnique_rayDivisorToPicard_pairing_eq_charge k hΦ s A₁ x
  have hdegree := boundaryOrthogonalEquivChargeKernel_symm_fst_pairing k hΦ s A₁ x
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
    let : (W).Over (Spec (.of k)) := ⟨(U).toBase ≫ fZ⟩
    (q κ : Fin n → ℤ) j = Chow.classIntersectionNumber k W
      (pullback (e.inv ≫ T.toBase) κ.val.toMul) ((U).exceptionalClass j) := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  let : (W).Over (Spec (.of k)) := ⟨(U).toBase ≫ fZ⟩
  let := isPerfPair_internal_markedForm k hΦ hdim s m hm hprim c J hJ hT e he
  let z := E (κ.val, 0)
  have hz := internal_picardHom_resolutionMarking k hΦ hdim s m hm hprim c J hJ hT e (κ.val, 0)
  have hκ : ((U).picardHom z).toMul = pullback (e.inv ≫ T.toBase) κ.val.toMul := by
    simpa only [z, picardHom_apply_zero, toMul_ofMul, pullback_comp] using
      congrArg Additive.toMul hz
  have hx : ((U).picardHom (0, Pi.single j 1)).toMul = (U).exceptionalClass j := by
    simpa only [zpow_one] using (U).picardHom_apply_single j 1
  dsimp only
  rw [Chow.classIntersectionNumber_comm, ← hx, ← hκ,
    ← picardMarking_apply U hU fZ, ← picardMarking_apply U hU fZ,
    classIntersectionNumber_picardMarking k hU]
  exact (boundaryOrthogonalEquivChargeKernel_apply k hΦ s B₁
    (orthogonalMarking k hΦ hdim s m hm hprim c J hJ hT e he hD κ) j).trans
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
    chargeKernelIntersectionForm k hΦ hdim s m hm hprim c J hJ hT e he hD x y =
      A₀ ((q).symm x).val ((q).symm y).val := by
  simp only [chargeKernelIntersectionForm, LinearMap.BilinForm.congr_apply,
    LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]

include hJ hT he hD in
private theorem chargeKernelIntersectionForm_eq_internal (x y : (rayChargeMap s).ker) :
    let _ := isPerfPair_internal_markedForm k hΦ hdim s m hm hprim c J hJ hT e he
    let lift := (boundaryOrthogonalEquivChargeKernel k hΦ s B₁).symm
    chargeKernelIntersectionForm k hΦ hdim s m hm hprim c J hJ hT e he hD x y =
      B₁ (lift x).val (lift y).val := by
  let := isPerfPair_internal_markedForm k hΦ hdim s m hm hprim c J hJ hT e he
  dsimp only
  rw [coe_markedChargeKernelEquiv_symm k hΦ hdim s m hm hprim c J hJ hT e he hD,
    coe_markedChargeKernelEquiv_symm k hΦ hdim s m hm hprim c J hJ hT e he hD,
    pairing_resolutionMarking k hΦ hdim s m hm hprim c J hJ hT e he]
  simp only [chargeKernelIntersectionForm_apply, LinearMap.BilinForm.prod_apply,
    map_zero, add_zero]

include hJ hT he hD in
/-- In charge coordinates on the original surface, the norm is the negative sum of the
squared coordinates minus the determinant sum in clockwise order on the presenting fan.
The orders are read from any positive cyclic ray numbering. -/
theorem chargeKernelIntersectionForm_norm_eq_sum_det (b : Module.Basis (Fin 2) ℤ N)
    (hc : Φ.IsComplete) {r : ℕ} [NeZero r] (u : ZMod r ≃ Φ.Ray)
    (hu : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ)
    (x : (rayChargeMap s).ker) :
    chargeKernelIntersectionForm k hΦ hdim s m hm hprim c J hJ hT e he hD x x =
      -(∑ k, x.val k ^ 2) - ∑ k, ∑ l with (u.symm (s l)).val < (u.symm (s k)).val,
        b.detDualEquiv (s k).primitiveGenerator (s l).primitiveGenerator * x.val k * x.val l := by
  let := isPerfPair_internal_markedForm k hΦ hdim s m hm hprim c J hJ hT e he
  let y := (boundaryOrthogonalEquivChargeKernel k hΦ s B₁).symm x
  have h := boundary_orthogonal_norm_eq_sum_det k b hΦ hc u hu s y
  rw [chargeKernelIntersectionForm_eq_internal k hΦ hdim s m hm hprim c J hJ hT e he hD x x]
  simpa only [y, boundaryOrthogonalEquivChargeKernel_symm_snd, Pi.neg_apply, neg_sq, mul_neg,
    neg_mul, neg_neg] using h

include hJ hT he hD in
/-- The square of a charge relation on the original surface is congruent to the
negative sum of its coordinate squares modulo every common divisor of the charge
determinants. The congruence survives the nodal contractions. -/
theorem chargeKernelIntersectionForm_norm_modEq (b : Module.Basis (Fin 2) ℤ N)
    (hc : Φ.IsComplete) (x : (rayChargeMap s).ker) {a : ℤ}
    (ha : ∀ j k, a ∣ b.detDualEquiv (s j).primitiveGenerator (s k).primitiveGenerator) :
    chargeKernelIntersectionForm k hΦ hdim s m hm hprim c J hJ hT e he hD x x ≡
      -∑ j, x.val j ^ 2 [ZMOD a] := by
  rw [chargeKernelIntersectionForm_eq_internal k hΦ hdim s m hm hprim c J hJ hT e he hD x x]
  let := isPerfPair_internal_markedForm k hΦ hdim s m hm hprim c J hJ hT e he
  exact boundaryOrthogonalEquivChargeKernel_symm_norm_modEq k b hΦ hc s x ha

include hJ hT he hD in
/-- In the internal model, the charge pairing is the intersection of the toric coordinates
minus the dot product of the charge vectors. The same comparison applies to self-intersections. -/
theorem chargeKernelIntersectionForm_eq_classIntersectionNumber_sub_dotProduct
    (x y : (rayChargeMap s).ker) (H G : Pic(Z))
    (hx : ((U).picardHom (H, -(x : Fin n → ℤ))).toMul =
      pullback (e.inv ≫ T.toBase) ((q).symm x).val.toMul)
    (hy : ((U).picardHom (G, -(y : Fin n → ℤ))).toMul =
      pullback (e.inv ≫ T.toBase) ((q).symm y).val.toMul) :
    chargeKernelIntersectionForm k hΦ hdim s m hm hprim c J hJ hT e he hD x y =
      Chow.classIntersectionNumber k Z H.toMul G.toMul -
        ∑ j, (x : Fin n → ℤ) j * (y : Fin n → ℤ) j := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  have hmark (z : (rayChargeMap s).ker) (L : Pic(Z))
      (hz : ((U).picardHom (L, -(z : Fin n → ℤ))).toMul =
        pullback (e.inv ≫ T.toBase) ((q).symm z).val.toMul) :
      E (((q).symm z).val, 0) = (L, -(z : Fin n → ℤ)) := by
    apply ((hU).bijective_picardHom fZ).injective
    rw [internal_picardHom_resolutionMarking k hΦ hdim s m hm hprim c J hJ hT e]
    simp only [picardHom_apply_zero, pullback_comp] at hz ⊢
    exact (congrArg Additive.ofMul hz).symm
  have hp := pairing_resolutionMarking k hΦ hdim s m hm hprim c J hJ hT e he
    (((q).symm x).val, 0) (((q).symm y).val, 0)
  rw [hmark x H hx, hmark y G hy] at hp
  simpa only [LinearMap.BilinForm.prod_apply, Chow.intersectionBilinForm_apply,
    LinearMap.neg_apply, dotProductBilin_apply_apply, dotProduct, Prod.fst, Prod.snd,
    Pi.neg_apply, neg_mul_neg, Pi.zero_apply, zero_mul, Finset.sum_const_zero, neg_zero,
    add_zero, sub_eq_add_neg, chargeKernelIntersectionForm_apply] using hp.symm

section Isotropic

variable (hc : Φ.IsComplete)

local notation "v" => rayChargeMap s
local notation "Q" => chargeKernelIntersectionForm k hΦ hdim s m hm hprim c J hJ hT e he hD

include hΦ hc hJ hT he hD in
/-- The sum of the squared coordinates of an isotropic charge relation is divisible by the
charge index. For infinite index, whose index is zero, the sum itself vanishes. -/
theorem chargeIndex_dvd_sum_sq_of_isotropic (x : (v).ker) (hx : Q x x = 0) :
    ((v).range.toAddSubgroup.index : ℤ) ∣ ∑ j, x.val j ^ 2 := by
  have := Φ.lattice.free
  have := Φ.lattice.finite
  let b := Module.finBasisOfFinrankEq ℤ N hdim
  let ω : LinearMap.BilinForm ℤ N := b.detDualEquiv.toLinearMap
  have hω : ω.IsAlt := b.detDualEquiv_self
  have hb : ω (b 0) (b 1) = 1 := b.detDualEquiv_apply_basis_zero_one
  have hindex := (v).index_range_eq_gcd_chargeExchangeMatrix b hω hb
  have hd (j k : Fin n) :
      ((v).range.toAddSubgroup.index : ℤ) ∣
        b.detDualEquiv (s j).primitiveGenerator (s k).primitiveGenerator := by
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast, hindex]
    simpa only [QPainleve.Cluster.chargeExchangeMatrix_apply, rayChargeMap_single, ω,
      LinearEquiv.coe_coe] using
      (Finset.gcd_dvd (f := fun jk : Fin n × Fin n ↦
        (QPainleve.Cluster.chargeExchangeMatrix ω v jk.1 jk.2).natAbs)
        (Finset.mem_univ (j, k)))
  have hnorm := chargeKernelIntersectionForm_norm_modEq k hΦ hdim s m hm hprim c J hJ
    hT e he hD b hc x hd
  rw [hx, Int.modEq_comm, Int.modEq_zero_iff_dvd, dvd_neg] at hnorm
  exact hnorm

include hΦ hc hJ hT he hD in
/-- A nonzero isotropic class in the transported Picard form forces the charge image to
have rank two. This applies without assuming that the boundary classes form a cycle. -/
theorem finrank_rayChargeMap_range_of_isotropic {x : (v).ker} (hx : x ≠ 0) (hxx : Q x x = 0) :
    Module.finrank ℤ (v).range = 2 := by
  have := Φ.lattice.free
  have := Φ.lattice.finite
  have hindex : (v).range.toAddSubgroup.index ≠ 0 := by
    intro hz
    have hs := chargeIndex_dvd_sum_sq_of_isotropic k hΦ hdim s m hm hprim c J hJ hT e he hD hc x hxx
    rw [hz, Nat.cast_zero, zero_dvd_iff] at hs
    exact hx (Subtype.ext (funext fun j ↦
      (Finset.sum_sq_eq_zero_iff _ _).mp hs j (Finset.mem_univ j)))
  have hfinite := AddSubgroup.index_ne_zero_iff_finite.mp hindex
  exact ((v).range.finiteQuotient_iff.mp hfinite).trans hdim

end Isotropic

end TauCeti.Toric.Fan

namespace TauCeti.Toric.Fan

variable (k : Type) [Field k] [IsAlgClosed k]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "dim" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "J[" c "]" => (fun j ↦ Ray.internalCenter k b (s j) (c j))
local notation "hJ[" c "]" => (fun j ↦ Ray.internalCenter_val k b (s j) (c j))
local notation "M[" c "]" =>
  alongBoundary (subschemeι (Fan.toricBoundaryIdeal k Φ inferInstance)) (J[c])
local notation "U[" c "]" => WithBoundary.toTower (Sigma.snd (M[c]))
local notation "m" =>
  (fun j ↦ LinearMap.toAddMonoidHom (Module.Basis.detDualEquiv b (Ray.primitiveGenerator (s j))))
local notation "hm" => (fun j ↦ Module.Basis.detDualEquiv_self b (Ray.primitiveGenerator (s j)))
local notation "hprim" => (fun j ↦ Ray.surjective_detCharacter (s j) b)
local notation "hU[" z "]" =>
  isClosedPointTower_alongBoundary_binomialCenters k dim s m hm hprim z (J[z]) (hJ[z])
local notation "fZ" => ((Φ.finiteFanScheme k) ↘ (Spec (CommRingCat.of k)))
local notation "smoothZ" =>
  cast (congrArg (fun d ↦ SmoothOfRelativeDimension d fZ) dim)
    (Eq.mpr (congrArg (SmoothOfRelativeDimension _) (Φ.finiteFanScheme_over k))
      (Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ))

variable [(Φ.finiteFanScheme k).IsProjectiveOver k]
  {c d : Fin n → kˣ}
  {X Y W W' : Scheme} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [Y.IsProjectiveOver k] [IsIntegral X] [IsIntegral Y]
  [SmoothOfRelativeDimension 2 (X ↘ (Spec (.of k)))]
  [SmoothOfRelativeDimension 2 (Y ↘ (Spec (.of k)))]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm k X)]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm k Y)]
  {D : X.IdealSheafData} {E : Y.IdealSheafData} {l l' : ℕ}
  {P : QPainleve.BlowupTower X l W} {Q : QPainleve.BlowupTower Y l' W'}
  (hP : IsNodalBoundaryTower D (X ↘ (Spec (.of k))) (𝟙 X) P)
  (hQ : IsNodalBoundaryTower E (Y ↘ (Spec (.of k))) (𝟙 Y) Q)
  (p : W ≅ (alongBoundary (Φ.toricBoundaryIdeal k inferInstance).subschemeι
    (fun j ↦ (s j).internalCenter k b (c j))).1)
  (q : W' ≅ (alongBoundary (Φ.toricBoundaryIdeal k inferInstance).subschemeι
    (fun j ↦ (s j).internalCenter k b (d j))).1)
  (hp : p.inv ≫ P.toBase ≫ (X ↘ (Spec (.of k))) =
    (alongBoundary (Φ.toricBoundaryIdeal k inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter k b (c j))).2.toTower.toBase ≫
      ((Φ.finiteFanScheme k) ↘ (Spec (.of k))))
  (hq : q.inv ≫ Q.toBase ≫ (Y ↘ (Spec (.of k))) =
    (alongBoundary (Φ.toricBoundaryIdeal k inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter k b (d j))).2.toTower.toBase ≫
      ((Φ.finiteFanScheme k) ↘ (Spec (.of k))))
  (hDs : ((D.comap P.toBase).comap p.inv).support =
    (alongBoundary (Φ.toricBoundaryIdeal k inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter k b (c j))).2.boundaryι.ker.support)
  (hEs : ((E.comap Q.toBase).comap q.inv).support =
    (alongBoundary (Φ.toricBoundaryIdeal k inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter k b (d j))).2.boundaryι.ker.support)

local notation "a" => (Iso.inv p ≫ QPainleve.BlowupTower.toBase P)
local notation "a'" => (Iso.inv q ≫ QPainleve.BlowupTower.toBase Q)

local notation "ChargeKernel" => LinearMap.ker (rayChargeMap s)
local notation "kD" =>
  picardBoundaryOrthogonalEquivChargeKernel k hΦ dim s m hm hprim c (J[c]) (hJ[c]) hP p hp hDs
local notation "kE" =>
  picardBoundaryOrthogonalEquivChargeKernel k hΦ dim s m hm hprim d (J[d]) (hJ[d]) hQ q hq hEs
local notation "mark[" z "]" => picardMarking (U[z]) (hU[z]) fZ

/-- A map of Picard classes that preserves the marked coordinates of a charge
relation sends it to the class of the same relation on the other surface. -/
theorem map_picardBoundaryOrthogonalEquivChargeKernel_symm_of_matching_markings
    (G : LineBundleClass Y → LineBundleClass X) (x : ChargeKernel)
    (hmark : letI : SmoothOfRelativeDimension 2 fZ := smoothZ
      let L := ((kE).symm x).val.toMul
      (mark[c]).symm (Additive.ofMul (pullback a (G L))) =
        (mark[d]).symm (Additive.ofMul (pullback a' L))) :
    G ((kE).symm x).val.toMul = ((kD).symm x).val.toMul := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  let L := ((kE).symm x).val.toMul
  obtain ⟨H, hH, hdeg⟩ := exists_picardBoundaryOrthogonalEquivChargeKernel_symm_marking k
    hΦ dim s m hm hprim c (J[c]) (hJ[c]) hP p hp hDs x
  obtain ⟨H', hH', hdeg'⟩ := exists_picardBoundaryOrthogonalEquivChargeKernel_symm_marking k
    hΦ dim s m hm hprim d (J[d]) (hJ[d]) hQ q hq hEs x
  have hHH' : H' = H := (hdeg H').mp ((hdeg' H').mpr rfl)
  have hcoords : (mark[d]).symm (Additive.ofMul (pullback a' L)) =
      (H', -(x : Fin n → ℤ)) := by
    apply (mark[d]).injective
    rw [LinearEquiv.apply_symm_apply, picardMarking_apply]
    exact (congrArg Additive.ofMul hH').symm
  have hclass : pullback a (G L) = pullback a ((kD).symm x).val.toMul := by
    have h := congrArg (fun z ↦ ((mark[c]) z).toMul) (hmark.trans hcoords)
    simpa only [LinearEquiv.apply_symm_apply, toMul_ofMul, hHH', picardMarking_apply, hH] using h
  have hinj : Function.Injective (pullback a) := by
    intro L₁ L₂ h
    simp only [← pullback_comp] at h
    let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ (Spec (.of k)))
    apply hP.isClosedPointTower.injective_pullback_toBase (X ↘ (Spec (.of k)))
    apply (pullbackEquiv p.symm).injective
    simpa only [pullbackEquiv_apply, Iso.symm_hom] using h
  exact hinj hclass

end TauCeti.Toric.Fan

namespace TauCeti.Toric.Fan

variable (k : Type) [Field k] [IsAlgClosed k]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "ChargeKernel" => LinearMap.ker (rayChargeMap s)
local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "m" =>
  (fun j ↦ LinearMap.toAddMonoidHom (Module.Basis.detDualEquiv b (Ray.primitiveGenerator (s j))))
local notation "hm" => (fun j ↦ Module.Basis.detDualEquiv_self b (Ray.primitiveGenerator (s j)))
local notation "hprim" => (fun j ↦ Ray.surjective_detCharacter (s j) b)
local notation "J[" c "]" => (fun j ↦ Ray.internalCenter k b (s j) (c j))
local notation "hJ[" c "]" => (fun j ↦ Ray.internalCenter_val k b (s j) (c j))

omit [IsAlgClosed k] in
/-- Transport the structural map and boundary support across an equality of tower presentations. -/
theorem transport_boundaryPresentation {X Y : Scheme} [X.Over (Spec (.of k))] {D : X.IdealSheafData}
    {length : ℕ} {P : QPainleve.BlowupTower X length Y}
    {U W : Σ Z, WithBoundary (Φ.toricBoundaryIdeal k inferInstance).subschemeι n Z}
    (h : U = W) (e : Y ≅ W.1)
    (he : e.inv ≫ P.toBase ≫ (X ↘ (Spec (.of k))) =
      W.2.toTower.toBase ≫ ((Φ.finiteFanScheme k) ↘ (Spec (.of k))))
    (hD : ((D.comap P.toBase).comap e.inv).support = W.2.boundaryι.ker.support) :
    let a := e ≪≫ eqToIso (congrArg Sigma.fst h).symm
    a.inv ≫ P.toBase ≫ (X ↘ (Spec (.of k))) = U.2.toTower.toBase ≫ (Φ.finiteFanSchemeToSpec k) ∧
      ((D.comap P.toBase).comap a.inv).support = U.2.boundaryι.ker.support := by
  subst W
  simpa only [eqToIso_refl, Iso.trans_refl, ← finiteFanScheme_over] using
    And.intro he hD

variable [(Φ.finiteFanScheme k).IsProjectiveOver k]

variable {c : Fin n → kˣ}
  {X Y : Scheme} [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ (Spec (.of k)))]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm k X)]
  {D : X.IdealSheafData} {d : ℕ} {T : QPainleve.BlowupTower X d Y}
  (hT : IsNodalBoundaryTower D (X ↘ (Spec (.of k))) (𝟙 X) T)
  (e : Y ≅ (alongBoundary (Φ.toricBoundaryIdeal k inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter k b (c j))).1)
  (he : e.inv ≫ T.toBase ≫ (X ↘ (Spec (.of k))) =
    (alongBoundary (Φ.toricBoundaryIdeal k inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter k b (c j))).2.toTower.toBase ≫
      ((Φ.finiteFanScheme k) ↘ (Spec (.of k))))
  (hD : ((D.comap T.toBase).comap e.inv).support =
    (alongBoundary (Φ.toricBoundaryIdeal k inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter k b (c j))).2.boundaryι.ker.support)

local notation "charge" =>
  picardBoundaryOrthogonalEquivChargeKernel k hΦ rankTwo s m hm hprim c (J[c]) (hJ[c]) hT e he hD

/-- The charge coordinates identify the boundary-orthogonal classes on the contracted
surface with the kernel of the charge map of its ordered toric presentation. -/
def markedBoundaryChargeEquiv : D.boundaryOrthogonal k ≃ₗ[ℤ] ChargeKernel :=
  ((charge).symm.trans (LinearEquiv.ofEq _ _ (D.boundaryOrthogonal_def k).symm)).symm

/-- The inverse charge coordinates give the same underlying Picard class as the
inverse of the span-based comparison. -/
@[simp]
theorem coe_markedBoundaryChargeEquiv_symm (x : ChargeKernel) :
    ((markedBoundaryChargeEquiv k hΦ b s hT e he hD).symm x).val = ((charge).symm x).val := by
  simp only [markedBoundaryChargeEquiv, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply]

section InternalBlowup

variable {a : Y ≅ (internalBlowupTower k b s c).1}
  (ha : a.inv ≫ T.toBase ≫ (X ↘ (Spec (.of k))) =
    (internalBlowupTower k b s c).2.toTower.toBase ≫
      ((Φ.finiteFanScheme k) ↘ (Spec (.of k))))
  (hb : ((D.comap T.toBase).comap a.inv).support =
    (internalBlowupTower k b s c).2.boundaryι.ker.support)

local notation "M" => alongBoundary (subschemeι (Fan.toricBoundaryIdeal k Φ inferInstance)) (J[c])

/-- The total exceptional coefficients of a pulled-back boundary-orthogonal class
are the negatives of its charge coordinates. -/
theorem internalBlowupPicardMarking_symm_pullback_snd_eq_neg_charge
    (κ : D.boundaryOrthogonal k) :
    let h := internalBlowupTower_eq_alongBoundary k b s c
    let a' := a ≪≫ eqToIso (congrArg Sigma.fst h)
    let hp := transport_boundaryPresentation k h.symm a ha hb
    ((internalBlowupPicardMarking k b s c hΦ).symm
        (Additive.ofMul (pullback (a.inv ≫ T.toBase) κ.val.toMul))).2 =
      -(markedBoundaryChargeEquiv k hΦ b s hT a' hp.1 hp.2 κ : Fin n → ℤ) := by
  suffices coords : ∀ (U : Σ Z, WithBoundary (Φ.toricBoundaryIdeal k inferInstance).subschemeι n Z)
      (h : U = M) (a : Y ≅ U.1)
      (ha : a.inv ≫ T.toBase ≫ (X ↘ (Spec (.of k))) =
        U.2.toTower.toBase ≫ ((Φ.finiteFanScheme k) ↘ (Spec (.of k))))
      (hb : ((D.comap T.toBase).comap a.inv).support = U.2.boundaryι.ker.support)
      (z : Additive (LineBundleClass (Φ.finiteFanScheme k)) × (Fin n → ℤ))
      (hz : U.2.toTower.picardHom z = Additive.ofMul (pullback (a.inv ≫ T.toBase) κ.val.toMul)),
      let a' := a ≪≫ eqToIso (congrArg Sigma.fst h)
      let hp := transport_boundaryPresentation k h.symm a ha hb
      z.2 = -(markedBoundaryChargeEquiv k hΦ b s hT a' hp.1 hp.2 κ : Fin n → ℤ) by
    apply coords _ (internalBlowupTower_eq_alongBoundary k b s c) a ha hb
    rw [← internalBlowupPicardMarking_apply k b s c hΦ, LinearEquiv.apply_symm_apply]
  intro U h a ha hb z hz
  subst U
  simp only [eqToIso_refl, Iso.trans_refl]
  let χ := markedBoundaryChargeEquiv k hΦ b s hT a ha hb
  obtain ⟨H, hH, -⟩ := exists_picardBoundaryOrthogonalEquivChargeKernel_symm_marking k
    hΦ rankTwo s m hm hprim c (J[c]) (hJ[c]) hT a ha hb (χ κ)
  rw [← coe_markedBoundaryChargeEquiv_symm k hΦ b s hT a ha hb, LinearEquiv.symm_apply_apply] at hH
  let f := (Φ.finiteFanScheme k) ↘ (Spec (.of k))
  let : SmoothOfRelativeDimension 2 f := by
    rw [show f = Φ.finiteFanSchemeToSpec k from Φ.finiteFanScheme_over k]
    exact rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ
  have hU := isClosedPointTower_alongBoundary_binomialCenters k rankTwo s m hm hprim c
    (J[c]) (hJ[c])
  exact congrArg Prod.snd ((hU.bijective_picardHom f).injective
    (hz.trans (congrArg Additive.ofMul hH.symm)))

end InternalBlowup

end TauCeti.Toric.Fan
