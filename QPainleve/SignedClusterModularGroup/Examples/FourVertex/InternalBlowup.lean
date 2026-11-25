/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import QPainleve.AlgebraicGeometry.Chow.Nef.Boundary
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import QPainleve.Geometry.Toric.Fan.Picard.StrictTransform
public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Octagon
public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Words

import QPainleve.Algebra.Cluster.ChargeKernel.Index
import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Canonical
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction
import QPainleve.AlgebraicGeometry.IdealSheaf.Image.Over
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import QPainleve.Geometry.Toric.Fan.Boundary.DualGraph
import QPainleve.Geometry.Toric.Fan.Boundary.Prestable
import QPainleve.Geometry.Toric.Fan.Hirzebruch.Canonical
import QPainleve.Geometry.Toric.Fan.Logarithmic.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Internal blowups of the four-vertex octagon

Blowing up one smooth boundary point on each diagonal ray gives the
anticanonical pair for the doubled-square seed. The strict ray classes are
computed in the ordered total-transform Picard marking, so their intersection
matrix is independent of the four center parameters.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory LinearMap Module
open QPainleve.BlowupTower QPainleve.Cluster
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Chow TauCeti.Toric

namespace QPainleve.FourVertex

local notation "N" => (Fin 2 → ℤ)
local notation "i₂" => AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin 2)
local notation "b₂" => Pi.basisFun ℤ (Fin 2)
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Pic(" X ")" => Additive (LineBundleClass X)

variable {Φ : Fan i₂}

/-- The diagonal rays in the order of the four internal blowup labels. -/
def diagonalRay (v : ZMod 8 ≃ Φ.Ray) (j : Fin 4) : Φ.Ray :=
  v (![1, 3, 5, 7] j)

/-- The four center labels are at positions `1, 3, 5, 7` in the octagon numbering. -/
theorem diagonalRay_apply (v : ZMod 8 ≃ Φ.Ray) (j : Fin 4) :
    diagonalRay v j = v (![1, 3, 5, 7] j) := (rfl)

/-- The diagonal rays are distinct, so the four centers lie on distinct boundary components. -/
theorem diagonalRay_injective (v : ZMod 8 ≃ Φ.Ray) : Function.Injective (diagonalRay v) :=
  v.injective.comp (by decide : Function.Injective (![1, 3, 5, 7] : Fin 4 → ZMod 8))

variable (v : ZMod 8 ≃ Φ.Ray)
  (hv : ∀ j, (v j).primitiveGenerator = octagonGenerator j)

include hv in
/-- The ordered primitive charges are the four diagonal directions of the octagon. -/
theorem primitiveGenerator_diagonalRay (j : Fin 4) :
    (diagonalRay v j).primitiveGenerator = chargeVector j := by
  rw [diagonalRay_apply, hv, octagonGenerator_apply, chargeVector_eq, boundaryRay_eq]
  revert j
  decide

include hv in
/-- The diagonal centers give the doubled-square exchange matrix in vertex order. -/
theorem chargeExchangeMatrix_diagonalRay :
    chargeExchangeMatrix (b₂).detDualEquiv.toLinearMap (Fan.rayChargeMap (diagonalRay v)) =
      exchangeMatrix.matrix := by
  ext j k
  rw [exchangeMatrix_matrix_apply, Matrix.det_fin_two_of]
  simp only [chargeExchangeMatrix_apply, Fan.rayChargeMap_single, LinearEquiv.coe_coe,
    primitiveGenerator_diagonalRay v hv, Basis.detDualEquiv_apply, Basis.det_apply,
    Matrix.det_fin_two, Basis.toMatrix_apply, Pi.basisFun_repr,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_comm (chargeVector k 0)]

include hv in
/-- The four diagonal charges generate a sublattice of index two. -/
theorem chargeIndex_diagonalRay :
    (Fan.rayChargeMap (diagonalRay v)).range.toAddSubgroup.index = 2 := by
  rw [LinearMap.index_range_eq_gcd_chargeExchangeMatrix _ b₂
    (fun x ↦ Basis.detDualEquiv_self b₂ x) (Basis.detDualEquiv_apply_basis_zero_one b₂),
    chargeExchangeMatrix_diagonalRay v hv, exchangeMatrix_matrix]
  decide

private theorem rank_two : Module.finrank ℤ N = 2 := by simp

variable [Nonempty Φ.cones] (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (hnext : ∀ j, (b₂).detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
    ∃ σ : Φ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ)

local notation "X" => Φ.algebraicRealization
local notation "B" => intersectionBilinForm ℂ X

section Intersection

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S)]

local notation "R" j:arg => Φ.rayDivisorToPicard hΦ (Pi.single (v j) 1)

include hv hΦ hc hnext in
open Classical in
private theorem ray_pairing (j k : ZMod 8) :
    B (R j) (R k) = (if j = k then if j.val % 2 = 0 then -2 else -1 else 0) +
      (if k = j - 1 ∨ k = j + 1 then 1 else 0) := by
  rw [Φ.intersectionBilinForm_rayDivisorToPicard_single_single hΦ rank_two]
  by_cases hjk : j = k
  · subst k
    have hne : ¬ (j = j - 1 ∨ j = j + 1) := by
      revert j
      decide
    simp only [ite_eq_right hne, add_zero]
    exact rayBoundarySelfIntersection_eq_of_octagon hΦ hc v hv (fun l ↦ (hnext l).2) j
  · have hprev := hnext (j - 1)
    rw [sub_add_cancel] at hprev
    have h := Φ.ray_neighbors_iff_of_det b₂ hΦ hc hprev (hnext j) (v k)
    have hadj : (∃ σ : Φ.cones, (v j).toCone ≤ σ ∧ (v k).toCone ≤ σ) ↔
        k = j - 1 ∨ k = j + 1 := by
      constructor
      · intro hp
        simpa only [Equiv.apply_eq_iff_eq] using h.mp ⟨v.injective.ne hjk, hp⟩
      · intro hp
        exact (h.mpr (by simpa only [Equiv.apply_eq_iff_eq] using hp)).2
    rw [ite_eq_right (v.injective.ne hjk), ite_eq_right hjk, zero_add]
    exact if_congr hadj rfl rfl

end Intersection

variable (c : Fin 4 → ℂˣ)

local notation "s" => diagonalRay v
local notation "U" => Fan.internalBlowupTower b₂ s c
local notation "Y" => (U).1
local notation "T" => WithBoundary.toTower (Sigma.snd U)
local notation "f" => (X ↘ S)
local notation "g" => (toBase T ≫ f)
local notation "D" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd U))
local notation "hT" => Fan.isClosedPointTower_internalBlowupTower b₂ s c
local notation "R" j:arg => Φ.rayDivisorToPicard hΦ (Pi.single (v j) 1)
local notation "M" => Fan.internalBlowupPicardMarking b₂ s c hΦ
local notation "prime" j:arg => Scheme.IdealSheafData.boundaryPrimeEmbedding D
  (Fan.internalBlowupBoundaryPrimeEquiv hΦ b₂ s c (v j))

omit [Nonempty Φ.cones] in
include hΦ in
private theorem smooth_base : SmoothOfRelativeDimension 2 f := by
  rw [Fan.algebraicRealization_over]
  simpa only [rank_two] using Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ

include hΦ in
private theorem smooth_model : SmoothOfRelativeDimension 2 g :=
  let := smooth_base hΦ
  (hT).smoothOfRelativeDimension f

include hΦ hc in
private theorem isProjectiveOver_model :
    letI : (Y).Over S := ⟨g⟩
    (Y).IsProjectiveOver ℂ := by
  let : (X).IsProjectiveOver ℂ := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b₂
  exact (T).isProjectiveOver ℂ

include hΦ in
private theorem isEffectiveCartier_boundary
    (hD : (Φ.boundaryIdeal inferInstance).IsEffectiveCartier) :
    (D).IsEffectiveCartier := by
  let := smooth_base hΦ
  let I := Φ.boundaryIdeal inferInstance
  let J (j : Fin 4) := (s j).internalCenter b₂ (c j)
  have h := strictTransform_ker_comp_alongBoundary I.subschemeι (𝟙 I.subscheme) J
    (fun j ↦ by simpa only [Scheme.IdealSheafData.comap_id] using (J j).property)
  simp only [Category.id_comp, Scheme.IdealSheafData.ker_subschemeι] at h
  have he : (T).strictTransform I = D := by
    rw [Fan.internalBlowupTower_eq_alongBoundary]
    exact h
  exact he ▸ (hT).isEffectiveCartier_strictTransform f hD

open Classical in
private theorem marking_boundaryPrime (j : ZMod 8) :
    letI : IsIntegral Y := Fan.isIntegral_internalBlowupTower b₂ s c hΦ
    letI : IsNoetherian Y := (T).isNoetherian
    letI := smooth_model v hΦ c
    letI := (g).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (M) (Φ.markedBoundaryMap hΦ s (Pi.single (v j) 1)) =
      Additive.ofMul (LineBundleClass.primeDivisorClass (prime j)) := by
  rw [Fan.internalBlowupPicardMarking_apply]
  let p := Fan.internalBlowupBoundaryPrimeEquiv hΦ b₂ s c (v j)
  have he : prime j = ⟨p.val, (Scheme.IdealSheafData.mem_boundaryPrimes.mp p.property).2⟩ :=
    Subtype.ext ((D).coe_boundaryPrimeEmbedding p)
  rw [he]
  exact Fan.picardHom_markedBoundaryMap_single_eq_primeDivisorClass hΦ b₂ s c (v j)

omit [Nonempty Φ.cones] in
open Classical in
private theorem dotProduct_exceptional_boundary (j k : ZMod 8) :
    (∑ a : Fin 4, (-(Pi.single (v j) 1 : Φ.Ray → ℤ) (s a)) *
      (-(Pi.single (v k) 1 : Φ.Ray → ℤ) (s a))) =
      if j = k ∧ j.val % 2 = 1 then 1 else 0 := by
  simp only [Pi.single_apply, diagonalRay_apply, Equiv.apply_eq_iff_eq]
  revert j k
  decide

include hv hc hnext in
open Classical in
private theorem intersection_boundaryPrime (j k : ZMod 8) :
    letI : IsIntegral Y := Fan.isIntegral_internalBlowupTower b₂ s c hΦ
    letI : IsNoetherian Y := (T).isNoetherian
    letI : (Y).Over S := ⟨g⟩
    letI := smooth_model v hΦ c
    letI := (g).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    Chow.classIntersectionNumber ℂ Y (LineBundleClass.primeDivisorClass (prime j))
      (LineBundleClass.primeDivisorClass (prime k)) =
      (-2 : ℤ) * (if j = k then 1 else 0) + (if k = j - 1 then 1 else 0) +
        (if k = j + 1 then 1 else 0) := by
  let : (X).IsProjectiveOver ℂ := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b₂
  let := smooth_base hΦ
  let : IsIntegral Y := Fan.isIntegral_internalBlowupTower b₂ s c hΦ
  let : IsNoetherian Y := (T).isNoetherian
  let := smooth_model v hΦ c
  let := (g).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have h := classIntersectionNumber_picardMarking ℂ (hT)
    (Φ.markedBoundaryMap hΦ s (Pi.single (v j) 1))
    (Φ.markedBoundaryMap hΦ s (Pi.single (v k) 1))
  have hmark (l : ZMod 8) :
      (T).picardMarking (hT) f (Φ.markedBoundaryMap hΦ s (Pi.single (v l) 1)) =
        Additive.ofMul (LineBundleClass.primeDivisorClass (prime l)) := by
    simpa only [picardMarking_apply, Fan.internalBlowupPicardMarking_apply] using
      marking_boundaryPrime v hΦ c l
  dsimp only at h
  rw [hmark j, hmark k] at h
  simp only [toMul_ofMul, Fan.markedBoundaryMap_apply] at h
  rw [← intersectionBilinForm_apply ℂ X (R j) (R k),
    ray_pairing v hv hΦ hc hnext, dotProduct_exceptional_boundary] at h
  rw [h]
  clear h
  revert j k
  decide

private theorem isOver_boundaryι :
    let : (Y).Over S := ⟨g⟩
    ((U).2.boundaryι).IsOver S := by
  let : (Y).Over S := ⟨g⟩
  constructor
  rw [(Φ.boundaryIdeal inferInstance).over_eq_subschemeι_comp]
  exact (U).2.boundaryι_toBase_assoc f

include hc hΦ in
private theorem prestable_boundary :
    let : (Y).Over S := ⟨g⟩
    PrestableFamily ((D).subscheme ↘ S) := by
  intro _
  let : (X).IsProjectiveOver ℂ := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b₂
  let : IsProper Φ.algebraicRealizationStructureMap := by
    rw [← Fan.algebraicRealization_over]
    infer_instance
  let : (Y).Over S := ⟨g⟩
  let e := asIso (U).2.boundaryι.toImage
  let : ((U).2.boundaryι).IsOver S := isOver_boundaryι v c
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily) e.hom _).mp
  rw [comp_over]
  exact Φ.prestableFamily_boundary hΦ hc rank_two

private def numberedPrime : ZMod 8 ↪ CodimensionOnePoint Y :=
  (v.trans (Fan.internalBlowupBoundaryPrimeEquiv hΦ b₂ s c)).toEmbedding.trans
    (D).boundaryPrimeEmbedding

private theorem mem_support_iff_mem_range_numberedPrime (p : CodimensionOnePoint Y) :
    p.val ∈ (D).support ↔ p ∈ Set.range (numberedPrime v hΦ c) := by
  have he : Set.range (numberedPrime v hΦ c) = Set.range (D).boundaryPrimeEmbedding := by
    rw [numberedPrime, Function.Embedding.coe_trans, Equiv.coe_toEmbedding, Set.range_comp,
      Equiv.range_eq_univ, Set.image_univ]
  rw [he, Scheme.IdealSheafData.range_boundaryPrimeEmbedding]
  rfl

local notation "δ(" h ")" =>
  (LineBundleClass.mk (Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf h))⁻¹

open Classical in
private theorem total_boundary_class (hD : (D).IsEffectiveCartier) :
    let : (Y).Over S := ⟨g⟩
    let : IsIntegral Y := Fan.isIntegral_internalBlowupTower b₂ s c hΦ
    let : IsNoetherian Y := (T).isNoetherian
    let := smooth_model v hΦ c
    let := (g).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    ∀ [IsReduced (D).subscheme],
      Additive.ofMul δ(hD) = ∑ j : ZMod 8, Additive.ofMul
        (LineBundleClass.primeDivisorClass (prime j)) := by
  intros
  exact hD.ofMul_inv_toInvertibleSheaf_eq_sum_primeDivisorClass (numberedPrime v hΦ c)
    (mem_support_iff_mem_range_numberedPrime v hΦ c)

open Classical in
private theorem total_boundary_coordinates (hD : (D).IsEffectiveCartier)
    [IsReduced (D).subscheme] :
    Additive.ofMul δ(hD) = (M) (Φ.rayDivisorToPicard hΦ 1, fun _ ↦ -1) := by
  let := Fintype.ofFinite Φ.Ray
  rw [total_boundary_class v hΦ c hD]
  simp_rw [← marking_boundaryPrime v hΦ c]
  have hsum := Finset.univ_sum_single (1 : Φ.Ray → ℤ)
  simp only [Pi.one_apply] at hsum
  rw [← map_sum, ← map_sum, v.sum_comp (fun ρ ↦ (Pi.single ρ (1 : ℤ) : Φ.Ray → ℤ)), hsum]
  simp only [Fan.markedBoundaryMap_apply, Pi.one_apply]

include hc hv hnext in
open Classical in
private theorem primitive_nef_square_zero (hD : (D).IsEffectiveCartier) :
    let : (Y).Over S := ⟨g⟩
    let : IsIntegral Y := Fan.isIntegral_internalBlowupTower b₂ s c hΦ
    let : IsNoetherian Y := (T).isNoetherian
    let : (Y).IsProjectiveOver ℂ := isProjectiveOver_model v hΦ hc c
    let := smooth_model v hΦ c
    let := (g).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    ∀ [IsReduced (D).subscheme],
      TauCeti.IsPrimitive (Additive.ofMul δ(hD)) ∧
      δ(hD).IsNef ℂ g ∧ classIntersectionNumber ℂ Y δ(hD) δ(hD) = 0 := by
  intros
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension g (n := 2)
  let Q := classIntersectionBilinForm ℂ hdim
  have hδ := total_boundary_class v hΦ c hD
  have hrow (k : ZMod 8) : Q (Additive.ofMul δ(hD))
      (Additive.ofMul (LineBundleClass.primeDivisorClass (prime k))) = 0 := by
    rw [hδ]
    simp only [map_sum, LinearMap.sum_apply, Q, classIntersectionBilinForm_apply, toMul_ofMul,
      intersection_boundaryPrime v hv hΦ hc hnext c]
    revert k
    decide
  refine ⟨?_, ?_, ?_⟩
  · rw [total_boundary_coordinates v hΦ c hD, LinearEquiv.isPrimitive_iff (M)]
    let p := LinearMap.proj (0 : Fin 4) ∘ₗ LinearMap.snd ℤ (Pic(X)) (Fin 4 → ℤ)
    exact TauCeti.isPrimitive_def.mpr ⟨-p, by simp [p]⟩
  · refine (hD.isNef_inv_mk_toInvertibleSheaf_iff hdim).mpr fun p hp ↦ ?_
    obtain ⟨j, rfl⟩ := (mem_support_iff_mem_range_numberedPrime v hΦ c p).mp hp
    simpa only [Q, classIntersectionBilinForm_apply, toMul_ofMul, numberedPrime,
      Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.trans_apply] using
      le_of_eq (hrow j).symm
  · have hzero : Q (Additive.ofMul δ(hD)) (Additive.ofMul δ(hD)) = 0 := by
      conv_lhs => rhs; rw [hδ]
      simp only [map_sum, hrow, Finset.sum_const_zero]
    simpa only [Q, classIntersectionBilinForm_apply, toMul_ofMul] using hzero

section Canonical

open LineBundleClass Scheme.IdealSheafData

local notation "K(" Z ")" => mk (QPainleve.canonicalBundle ℂ Z 2)
local notation "D₀" => Φ.boundaryIdeal inferInstance

private theorem canonical_internal (hD₀ : (D₀).IsEffectiveCartier)
    (hD : (D).IsEffectiveCartier) :
    letI : (Y).Over S := ⟨g⟩
    letI : SmoothOfRelativeDimension 2 f := smooth_base hΦ
    letI : SmoothOfRelativeDimension 2 (Y ↘ S) := smooth_model v hΦ c
    mk hD₀.toInvertibleSheaf = K(X) → mk hD.toInvertibleSheaf = K(Y) := by
  intro hK
  let : (Y).Over S := ⟨g⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := smooth_model v hΦ c
  let := smooth_base hΦ
  let : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  let : IsNoetherian X := isNoetherian_of_finiteType f
  let : (T).toBase.IsOver S := ⟨rfl⟩
  let hRam := (hT).isEffectiveCartier_ramificationIdealSheafToBase ℂ
  let hTot := (hT).isEffectiveCartier_totalTransform f hD₀
  have hI := Fan.comap_boundaryIdeal_internalBlowupTower b₂ s c hΦ hD₀
  have hPic : pullback (T).toBase (mk hD₀.toInvertibleSheaf) =
      mk hD.toInvertibleSheaf * mk hRam.toInvertibleSheaf := by
    rw [hD₀.pullback_mk_toInvertibleSheaf hTot,
      mk_toInvertibleSheaf_congr hTot (TauCeti.isEffectiveCartier_mul hD hRam) hI,
      mk_toInvertibleSheaf_mul]
  have hR := (hT).ramificationIdealSheafToBase_def ℂ
  have hK' := QPainleve.mk_canonicalBundle_eq_pullback_mul_inv_ramification ℂ (T).toBase 2
    (hR ▸ hRam)
  rw [← mk_toInvertibleSheaf_congr hRam _ hR, ← hK, hPic, mul_inv_cancel_right] at hK'
  exact hK'.symm

variable {Ω : Fan i₂} [Nonempty Ω.cones]
  (hΩ : Ω.IsRegular) (hcΩ : Ω.IsComplete) (r : Fin 4 ≃ Ω.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b₂ 0, b₂ 1, -b₂ 0, (0 : ℤ) • b₂ 0 - b₂ 1])
  {W : Scheme} {T₀ : BlowupTower Ω.algebraicRealization 4 W} {H : Φ.IsSubdivision Ω}
  (hT₀ : IsNodalBoundaryTower (Ω.boundaryIdeal inferInstance)
    Ω.algebraicRealizationStructureMap (𝟙 _) T₀)
  (a : Φ.algebraicRealization ≅ W) (ha : a.hom ≫ T₀.toBase = H.toFanHom.algebraicMap)

local notation "Q" => Ω.algebraicRealization
local notation "P" => Ω.boundaryIdeal inferInstance

omit [Nonempty Φ.cones] [Nonempty Ω.cones] in
include a ha in
private theorem base_over :
    letI : W.Over S := ⟨T₀.toBase ≫ (Q ↘ S)⟩
    a.hom.IsOver S := by
  let : W.Over S := ⟨T₀.toBase ≫ (Q ↘ S)⟩
  exact ⟨calc
    a.hom ≫ (W ↘ S) = (a.hom ≫ T₀.toBase) ≫ (Q ↘ S) := (Category.assoc _ _ _).symm
    _ = (X ↘ S) := ha.symm ▸ comp_over H.toFanHom.algebraicMap S⟩

omit [Nonempty Φ.cones] in
include hΩ hT₀ a ha hr hcΩ in
private theorem rational_of_octagon :
    Scheme.IsRationalOver f := by
  let : SmoothOfRelativeDimension 2 (Q ↘ S) := smooth_base hΩ
  let : Scheme.IsRationalOver (Q ↘ S) :=
    Fan.isRationalOver_of_hirzebruch b₂ 0 hΩ r hr hcΩ
  let : W.Over S := ⟨T₀.toBase ≫ (Q ↘ S)⟩
  let : Scheme.IsRationalOver (W ↘ S) := hT₀.isClosedPointTower.isRationalOver (Q ↘ S)
  let : a.hom.IsOver S := base_over a ha
  exact Scheme.BirationalOver.isRationalOver f (W ↘ S)
    (a.hom.birationalOver _ _ (comp_over a.hom S))

include hΦ hΩ hcΩ hr a ha hT₀ in
private theorem canonical_octagon (hD : (D₀).IsEffectiveCartier)
    (hB : ((P).comap T₀.toBase).radical.comap a.hom = D₀) :
    let := smooth_base hΦ
    mk hD.toInvertibleSheaf = K(X) := by
  intro _
  let : (Q).IsProjectiveOver ℂ := Ω.isProjectiveOver_algebraicRealization_of_isComplete hΩ hcΩ b₂
  let : SmoothOfRelativeDimension 2 (Q ↘ S) := smooth_base hΩ
  have hq : (Q ↘ S) = Ω.algebraicRealizationStructureMap :=
    Ω.algebraicRealization_over
  let : IsNoetherian Q := isNoetherian_of_finiteType (Q ↘ S)
  have hnod : IsNodalBoundaryTower P (Q ↘ S) (𝟙 _) T₀ := hq.symm ▸ hT₀
  let hP := Ω.isEffectiveCartier_boundaryIdeal hΩ hcΩ rank_two
  have hN : AtWorstNodalOfRelativeDimensionOne ((P).subschemeι ≫ (Q ↘ S)) := by
    rw [hq]
    exact Ω.atWorstNodalOfRelativeDimensionOne_boundary hΩ hcΩ rank_two
  let hE := (hnod.radical_comap_toBase hP hN).1
  let : W.Over S := ⟨T₀.toBase ≫ (Q ↘ S)⟩
  let : SmoothOfRelativeDimension 2 (W ↘ S) := hnod.isClosedPointTower.smoothOfRelativeDimension _
  let : a.hom.IsOver S := base_over a ha
  have hKE : mk hE.toInvertibleSheaf = K(W) :=
    (hnod.canonicalClass_radical_comap_toBase_iff hP hN).mpr
      (Fan.mk_toInvertibleSheaf_boundaryIdeal_eq_mk_canonicalBundle_of_hirzebruch
        b₂ 0 hΩ hcΩ r hr hP)
  rw [mk_toInvertibleSheaf_congr hD (hE.comap a.hom) hB.symm,
    ← hE.pullback_mk_toInvertibleSheaf (hE.comap a.hom), hKE, pullback_mk,
    mk_pullback_canonicalBundle]

end Canonical

local notation "Cycle(" C ")" =>
  Scheme.NodalCycleNumbering (Empty.elim : Empty → Scheme.Hom.smoothLocus (C ↘ S)) 8

include hnext hc in
private theorem exists_numbering_matching_primes (hD : (D).IsEffectiveCartier) :
    let : (Y).Over S := ⟨g⟩
    let : IsNoetherian Y := (T).isNoetherian
    let := prestable_boundary v hΦ hc c
    ∃ A : Cycle((D).subscheme), ∀ j,
      A.boundaryPrimeEquiv hD j = Fan.internalBlowupBoundaryPrimeEquiv hΦ b₂ s c (v j) := by
  intros
  let : (X).IsProjectiveOver ℂ := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b₂
  let : IsProper Φ.algebraicRealizationStructureMap := by
    rw [← Fan.algebraicRealization_over]
    infer_instance
  let := Φ.prestableFamily_boundary hΦ hc rank_two
  let : ((U).2.boundaryι).IsOver S := isOver_boundaryι v c
  let e : (Φ.boundaryIdeal inferInstance).subscheme ≅ (D).subscheme :=
    asIso (U).2.boundaryι.toImage
  obtain ⟨edge, order, vertex, hend, hcomp, -⟩ :=
    Φ.exists_toric_boundary_dualGraph_cycle hΦ hc Empty.elim b₂ v hnext
  let P : Cycle((Φ.boundaryIdeal inferInstance).subscheme) := ⟨vertex, edge, order, hend⟩
  let A : Cycle((D).subscheme) := e.mapNodalCycleNumbering P
  refine ⟨A, fun j ↦ Subtype.ext ?_⟩
  have hl := e.apply_componentGenericPoint P A j
  have hact : e.boundaryCycleAction P A = 1 :=
    e.boundaryCycleAction_mapNodalCycleNumbering P
  rw [hact, map_one, Equiv.Perm.one_apply] at hl
  have hh : P.component j = Φ.boundaryNormalizationComponentEquiv hΦ (v j) := by
    rw [Scheme.NodalCycleNumbering.component_apply]
    exact hcomp j
  rw [Scheme.NodalCycleNumbering.boundaryPrimeEquiv_apply_val, ← hl,
    ← Scheme.Hom.comp_apply, asIso_hom, Scheme.Hom.toImage_imageι,
    Scheme.NodalCycleNumbering.componentGenericPoint_def, hh, Fan.internalBlowupBoundaryPrime_val]

open Classical in
/-- For every tuple of nonzero center parameters, the ordered blowups at the
four diagonal rays of the subdivided quadric form a smooth projective rational
surface. Its numbered strict boundary is an anticanonical eight-cycle of
`(-2)`-curves with primitive nef square-zero total class. The four charges
give the doubled-square exchange matrix and have index two. -/
theorem exists_four_vertex_internal_blowup (parameters : Fin 4 → ℂˣ) :
    ∃ (Ψ : Fan i₂) (hΨ : Ψ.IsRegular) (hcΨ : Ψ.IsComplete) (rays : ZMod 8 ≃ Ψ.Ray),
      (∀ j, (rays j).primitiveGenerator = octagonGenerator j) ∧
      let := hcΨ.nonempty_cones
      let centers := diagonalRay rays
      let P := Fan.internalBlowupTower b₂ centers parameters
      let π := P.2.toTower.toBase
      let base := Ψ.algebraicRealization ↘ S
      let projection := π ≫ base
      let boundary := P.2.boundaryι.ker
      letI : P.1.Over S := ⟨projection⟩
      letI : IsIntegral P.1 := Fan.isIntegral_internalBlowupTower b₂ centers parameters hΨ
      letI : IsNoetherian P.1 := P.2.toTower.isNoetherian
      letI : SmoothOfRelativeDimension 2 (P.1 ↘ S) := by
        have : SmoothOfRelativeDimension 2 base := by
          dsimp only [base]
          rw [Fan.algebraicRealization_over]
          simpa only [finrank_pi, Fintype.card_fin] using
            Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
        exact (Fan.isClosedPointTower_internalBlowupTower b₂ centers parameters)
          |>.smoothOfRelativeDimension base
      letI := (P.1 ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      P.1.IsProjectiveOver ℂ ∧ SmoothOfRelativeDimension 2 projection ∧
      Scheme.IsRationalOver projection ∧
      chargeExchangeMatrix (b₂).detDualEquiv.toLinearMap (Fan.rayChargeMap centers) =
        exchangeMatrix.matrix ∧
      (Fan.rayChargeMap centers).range.toAddSubgroup.index = 2 ∧
      ∃ (hD : boundary.IsEffectiveCartier) (_ : PrestableFamily (boundary.subscheme ↘ S)),
        LineBundleClass.mk hD.toInvertibleSheaf = LineBundleClass.mk (canonicalBundle ℂ P.1 2) ∧
        TauCeti.IsPrimitive (Additive.ofMul δ(hD)) ∧ δ(hD).IsNef ℂ projection ∧
        classIntersectionNumber ℂ P.1 δ(hD) δ(hD) = 0 ∧
        ∃ A : Cycle(boundary.subscheme),
          (∀ j, A.boundaryPrimeEquiv hD j =
            Fan.internalBlowupBoundaryPrimeEquiv hΨ b₂ centers parameters (rays j)) ∧
          ∀ j k : ZMod 8,
            let p l := boundary.boundaryPrimeEmbedding (A.boundaryPrimeEquiv hD l)
            classIntersectionNumber ℂ P.1 (LineBundleClass.primeDivisorClass (p j))
              (LineBundleClass.primeDivisorClass (p k)) =
              (-2 : ℤ) * (if j = k then 1 else 0) + (if k = j - 1 then 1 else 0) +
                (if k = j + 1 then 1 else 0) := by
  obtain ⟨Ω, hΩ, hcΩ, r, hr, Ψ, hΨ, hcΨ, rays, H, W, T₀, a, hT₀, ha, hB, hv, hnext, -⟩ :=
    exists_four_vertex_octagon_blowup
  let : Nonempty Ω.cones := hcΩ.nonempty_cones
  let : Nonempty Ψ.cones := hcΨ.nonempty_cones
  let M' := Fan.internalBlowupTower b₂ (diagonalRay rays) parameters
  let projection := M'.2.toTower.toBase ≫ (Ψ.algebraicRealization ↘ S)
  let : M'.1.Over S := ⟨projection⟩
  let := smooth_model rays hΨ parameters
  let : Scheme.IsRationalOver (Ψ.algebraicRealization ↘ S) :=
    rational_of_octagon hΩ hcΩ r hr hT₀ a ha
  let := smooth_base hΨ
  let hD₀ := Ψ.isEffectiveCartier_boundaryIdeal hΨ hcΨ rank_two
  let hD := isEffectiveCartier_boundary rays hΨ parameters hD₀
  let hpre := prestable_boundary rays hΨ hcΨ parameters
  let : IsReduced M'.2.boundaryι.ker.subscheme := hpre.atWorstNodalOfRelativeDimensionOne.isReduced
  have hK := canonical_internal rays hΨ parameters hD₀ hD
    (canonical_octagon hΨ hΩ hcΩ r hr hT₀ a ha hD₀ hB)
  obtain ⟨hprim, hnef, hsq⟩ := primitive_nef_square_zero rays hv hΨ hcΨ hnext parameters hD
  obtain ⟨A, hA⟩ := exists_numbering_matching_primes rays hΨ hcΨ hnext parameters hD
  have hclosed := Fan.isClosedPointTower_internalBlowupTower b₂ (diagonalRay rays) parameters
  refine ⟨Ψ, hΨ, hcΨ, rays, hv, isProjectiveOver_model rays hΨ hcΨ parameters,
    smooth_model rays hΨ parameters, hclosed.isRationalOver _,
    chargeExchangeMatrix_diagonalRay rays hv, chargeIndex_diagonalRay rays hv,
    hD, hpre, hK, hprim, hnef, hsq, A, hA, fun j k ↦ ?_⟩
  simpa only [hA] using intersection_boundaryPrime rays hv hΨ hcΨ hnext parameters j k

end QPainleve.FourVertex
