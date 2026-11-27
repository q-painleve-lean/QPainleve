/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.StrictTransform
public import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Intersection
public import QPainleve.SignedClusterModularGroup.Examples.ElevenVertex
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic

import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Numerical
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.Geometry.Toric.Fan.Boundary.ProjectiveLine
import QPainleve.Geometry.Toric.Fan.Boundary.StrictTransform
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective

/-!
# The plane blowup for the eleven-vertex seed

Blow up two, three, and six internal centers along the three rays of the
coordinate triangle. The strict boundary has diagonal intersections
`-1, -2, -5` and all three off-diagonal intersections equal to one.
The order of the internal blowups is the order of the seed labels.
The intersection calculations use `Fan.picardHom_markedBoundaryMap_single_internalBlowupTower`
and `BlowupTower.classIntersectionNumber_picardMarking`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open TauCeti.Toric TauCeti.Toric.Fan

namespace QPainleve.ElevenVertex

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

local notation "b" => Pi.basisFun ℤ (Fin 2)
local notation "hi" => isIntegralLattice_intCast 2
local notation "Φ" => projectiveSpace b hi
local notation "hΦ" => isRegular_projectiveSpace b hi
local notation "hc" => isComplete_projectiveSpace b hi
local notation "P" => Fan.finiteFanScheme k₀ Φ
local notation "S" => Spec (CommRingCat.of k₀)

local instance : Nonempty (Φ).cones := Fan.IsComplete.nonempty_cones hc

/-- The three boundary rays, in order `(1,0), (0,1), (-1,-1)`. -/
def planeBoundaryRay : Fin 3 ≃ (Φ).Ray :=
  (finSuccEquivLast (n := 2)).trans (projectivePlaneRayEquiv b hi)

/-- The primitive vectors in the plane marking are the charges of the three blocks. -/
@[simp]
theorem primitiveGenerator_planeBoundaryRay (j : Fin 3) :
    (planeBoundaryRay j).primitiveGenerator = ![![1, 0], ![0, 1], ![-1, -1]] j := by
  have h (k : Fin 3) : finSuccEquivLast (n := 2) k = ![some 0, some 1, none] k := by
    revert k
    decide
  simp only [planeBoundaryRay, Equiv.trans_apply, primitiveGenerator_projectivePlaneRayEquiv, h]
  fin_cases j <;> ext x <;> fin_cases x <;>
    simp [projectiveSpaceGenerator_none, Fin.sum_univ_two, Pi.basisFun_apply]

/-- The first two labels lie on the first ray, the next three on the second,
and the last six on the third. -/
def planeCenterRay (j : Fin 11) : (Φ).Ray :=
  planeBoundaryRay (if j.val < 2 then 0 else if j.val < 5 then 1 else 2)

/-- The ordered assignment of center rays in the plane model. -/
@[simp]
theorem planeCenterRay_apply (j : Fin 11) :
    planeCenterRay j = planeBoundaryRay (if j.val < 2 then 0 else if j.val < 5 then 1 else 2) :=
  (rfl)

/-- The ordered centers of the plane presentation have the charges of the
eleven-vertex seed in the standard lattice basis. -/
@[simp]
theorem rayChargeMap_planeCenterRay : Fan.rayChargeMap planeCenterRay = chargeMap := by
  apply (Pi.basisFun ℤ (Fin 11)).ext
  intro j
  simp only [Pi.basisFun_apply, rayChargeMap_single, chargeMap_single, charge_apply,
    planeCenterRay_apply, primitiveGenerator_planeBoundaryRay, rayIndex_eq_ite]

/-- The internal blowups of the plane in seed-label order, with the strict boundary. -/
abbrev planeBlowup (c : Fin 11 → k₀ˣ) :
    Σ Y, WithBoundary ((Φ).toricBoundaryIdeal k₀ inferInstance).subschemeι 11 Y :=
  internalBlowupTower k₀ b planeCenterRay c

local notation "T(" c ")" => WithBoundary.toTower (Sigma.snd (planeBlowup c))
local notation "Y(" c ")" => Sigma.fst (planeBlowup c)
local notation "hT(" c ")" => isClosedPointTower_internalBlowupTower k₀ b planeCenterRay c
local notation "f" => Fan.finiteFanSchemeToSpec k₀ Φ

private theorem projective_planeBlowup (c : Fin 11 → k₀ˣ) :
    let : Y(c).Over S := ⟨T(c).toBase ≫ (P ↘ S)⟩
    Scheme.IsProjectiveOver (X := Y(c)) k₀ := by
  intro _
  let : Scheme.IsProjectiveOver (X := P) k₀ :=
    (Φ).isProjectiveOver_finiteFanScheme_of_isComplete k₀ hΦ hc b
  exact (T(c)).isProjectiveOver k₀

variable [PerfectField k₀] in
omit [IsAlgClosed k₀] in
private theorem smooth_planeBlowup (c : Fin 11 → k₀ˣ) :
    let : Y(c).Over S := ⟨T(c).toBase ≫ (P ↘ S)⟩
    SmoothOfRelativeDimension 2 (Y(c) ↘ S) := by
  intro _
  have hover : (Y(c) ↘ S) = T(c).toBase ≫ (P ↘ S) := rfl
  rw [hover, finiteFanScheme_over]
  exact smoothOfRelativeDimension_internalBlowupTower k₀ b planeCenterRay c hΦ

variable [Infinite k₀] in
omit [IsAlgClosed k₀] in
/-- There are parameters for which all eleven binomial centers have disjoint supports. -/
theorem exists_disjoint_planeBlowup_centers :
    ∃ c : Fin 11 → k₀ˣ, Pairwise fun j k ↦
      Disjoint ((((planeCenterRay j).internalCenter k₀ b (c j)).val.map
        ((Φ).toricBoundaryIdeal k₀ inferInstance).subschemeι).support : Set P)
        (((planeCenterRay k).internalCenter k₀ b (c k)).val.map
          ((Φ).toricBoundaryIdeal k₀ inferInstance).subschemeι).support := by
  let e : ℕ ↪ {x : k₀ // x ≠ 0} := (Set.finite_singleton (0 : k₀)).infinite_compl.natEmbedding
  let c : Fin 11 ↪ k₀ˣ := (Fin.valEmbedding.trans e).trans unitsEquivNeZero.symm.toEmbedding
  refine ⟨c, fun j k hjk ↦ ?_⟩
  exact (disjoint_support_map_internalCenter_iff k₀ b _ _ _ _ _).mpr
    fun he ↦ hjk (c.injective (congrArg Prod.snd he))

local notation "L(" c ", " j ")" => strictRayBoundaryClass k₀ hΦ (by simp)
  (T(c)) (hT(c)) (planeBoundaryRay j)

private theorem strictClass_dot (j k : Fin 3) :
    (∑ l : Fin 11, (if (if l.val < 2 then 0 else if l.val < 5 then 1 else 2) = j
        then (-1 : ℤ) else 0) *
      (if (if l.val < 2 then 0 else if l.val < 5 then 1 else 2) = k
        then (-1 : ℤ) else 0)) =
      if j = k then (![2, 3, 6] : Fin 3 → ℤ) j else 0 := by
  revert j k
  decide

/-- The strict lines form a triangle with self-intersections `-1, -2, -5`.
Their intersection matrix is independent of the center parameters. -/
theorem classIntersectionNumber_planeBlowup_boundary (c : Fin 11 → k₀ˣ) (j k : Fin 3) :
    let : Y(c).Over S := ⟨T(c).toBase ≫ (P ↘ S)⟩
    Chow.classIntersectionNumber k₀ Y(c) (L(c, j)).toMul (L(c, k)).toMul =
      if j = k then (![(-1 : ℤ), -2, -5] : Fin 3 → ℤ) j else 1 := by
  classical
  intro _
  let : Scheme.IsProjectiveOver (X := P) k₀ :=
    (Φ).isProjectiveOver_finiteFanScheme_of_isComplete k₀ hΦ hc b
  let : SmoothOfRelativeDimension 2 (P ↘ S) := by
    rw [finiteFanScheme_over]
    simpa using (Φ).smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
  let : IsNoetherian P := isNoetherian_of_finiteType (P ↘ S)
  let a (l : Fin 3) := markedBoundaryMap k₀ hΦ planeCenterRay (Pi.single (planeBoundaryRay l) 1)
  have hmk (l : Fin 3) : (internalBlowupTower k₀ b planeCenterRay c).2.toTower.picardHom (a l) =
      L(c, l) := picardHom_markedBoundaryMap_single_internalBlowupTower k₀ hΦ b planeCenterRay c
        (planeBoundaryRay l)
  rw [← hmk j, ← hmk k, ← picardMarking_apply (T(c)) (hT(c)) (P ↘ S),
    ← picardMarking_apply (T(c)) (hT(c)) (P ↘ S), classIntersectionNumber_picardMarking k₀ (hT(c))]
  have ha (q : Fin 3) (l : Fin 11) :
      (a q).2 l = if (if l.val < 2 then 0 else if l.val < 5 then 1 else 2) = q
        then -1 else 0 := by
    simp only [a, markedBoundaryMap_apply, Pi.single_apply, planeCenterRay_apply,
      planeBoundaryRay.injective.eq_iff]
    rw [apply_ite (fun a : ℤ ↦ -a), neg_zero]
  have hp : Chow.classIntersectionNumber k₀ P (a j).1.toMul (a k).1.toMul = 1 := by
    simpa only [a, markedBoundaryMap_apply, rayChartDivisorToPicard_single, one_smul, toMul_ofMul]
      using classIntersectionNumber_projectivePlane_rayBoundaryPoint k₀ b hi
        (planeBoundaryRay j) (planeBoundaryRay k)
  simp only [hp, ha, strictClass_dot]
  fin_cases j <;> fin_cases k <;> decide

local notation "ι(" c ")" => WithBoundary.boundaryι (Sigma.snd (planeBlowup c))
local notation "D(" c ", " j ")" =>
  BlowupTower.strictTransform (Fan.rayDivisorIdeal k₀ Φ hΦ (planeBoundaryRay j)) (T(c))

/-- Each strict boundary component is a projective line over the coefficient field. -/
theorem exists_iso_projectiveLine_planeBlowup_boundary (c : Fin 11 → k₀ˣ) (j : Fin 3) :
    let : Y(c).Over S := ⟨T(c).toBase ≫ (P ↘ S)⟩
    ∃ e : (D(c, j)).subscheme ≅ projectiveLine k₀, e.hom.IsOver S := by
  intro _
  let ρ := planeBoundaryRay j
  let B := (Φ).rayDivisorIdeal k₀ hΦ ρ
  let g := ρ.boundaryComponentι k₀ hΦ ≫ ι(c)
  have hg : g.ker = D(c, j) :=
    ker_boundaryComponentι_internalBlowupTower k₀ b planeCenterRay c hΦ ρ
  obtain ⟨e, he⟩ := (D(c, j)).exists_iso_of_comap_eq_ker (Iso.refl _) g
    (by simpa only [Iso.refl_hom, Scheme.IdealSheafData.comap_id] using hg.symm)
  rw [Iso.refl_hom, Category.comp_id] at he
  have hover : (Y(c) ↘ S) = T(c).toBase ≫ (P ↘ S) := rfl
  have hπ : g ≫ (Y(c) ↘ S) = B.subschemeι ≫ (P ↘ S) := by
    dsimp only [g]
    rw [hover, Category.assoc, WithBoundary.boundaryι_toBase_assoc,
      Ray.boundaryComponentι_subschemeι_assoc]
  have : e.hom.IsOver S := ⟨by
    rw [Scheme.IdealSheafData.over_eq_subschemeι_comp, ← Category.assoc, he, hπ,
      ← Scheme.IdealSheafData.over_eq_subschemeι_comp]⟩
  let : Scheme.IsProjectiveOver (X := P) k₀ :=
    (Φ).isProjectiveOver_finiteFanScheme_of_isComplete k₀ hΦ hc b
  let : IsProper (B.subscheme ↘ S) := by
    rw [Scheme.IdealSheafData.over_eq_subschemeι_comp]
    infer_instance
  let p := ρ.boundaryIsoProjectiveLine k₀ hΦ (by simp) (Basis.detDualEquiv_self b
    ρ.primitiveGenerator)
    (ρ.surjective_detCharacter b)
  have : p.hom.IsOver S := by
    dsimp only [p]
    apply Ray.isOver_boundaryIsoProjectiveLine_hom
  have : e.inv.IsOver S := ⟨by rw [← comp_over e.hom S, Iso.inv_hom_id_assoc]⟩
  exact ⟨e.symm ≪≫ p, inferInstanceAs ((e.inv ≫ p.hom).IsOver S)⟩

/-- The strict transform of the line carrying two internal centers is an
exceptional curve of the first kind, so it admits a smooth projective contraction. -/
theorem isExceptionalCurveOfFirstKind_planeBlowup_first (c : Fin 11 → k₀ˣ) :
    (D(c, 0)).IsExceptionalCurveOfFirstKind := by
  let : Y(c).Over S := ⟨T(c).toBase ≫ (P ↘ S)⟩
  let : Scheme.IsProjectiveOver (X := Y(c)) k₀ := projective_planeBlowup c
  let : SmoothOfRelativeDimension 2 (Y(c) ↘ S) := smooth_planeBlowup c
  let C := D(c, 0)
  obtain ⟨e, he⟩ := exists_iso_projectiveLine_planeBlowup_boundary c 0
  let : e.hom.IsOver S := he
  let : C.subscheme.IsCurveOver k₀ := Scheme.isCurveOver_iff.mpr
    ⟨IsIntegral.of_isIso e.inv, by rw [← comp_over e.hom S]; infer_instance,
      e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
        (Scheme.IsCurveOver.topologicalKrullDim_eq_one k₀)⟩
  have hf : SmoothOfRelativeDimension 2 f := by
    simpa using (Φ).smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
  have hC : C.IsEffectiveCartier := (hT(c)).isEffectiveCartier_strictTransform f
    ((Φ).isEffectiveCartier_rayDivisorIdeal k₀ hΦ (planeBoundaryRay 0))
  let : IsIntegral (Y(c)) := isIntegral_internalBlowupTower k₀ b planeCenterRay c hΦ
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y(c) ↘ S) (n := 2)
  apply (hC.isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_classIntersectionNumber
    (k := k₀) hdim.le).mpr
  refine ⟨Scheme.genus_eq_zero_iff_exists_iso_projectiveLine.mpr ⟨e, he⟩, ?_⟩
  have h := classIntersectionNumber_planeBlowup_boundary c 0 0
  dsimp only at h
  rw [strictRayBoundaryClass_eq k₀ _ _ _ _ _ hC] at h
  simpa using h

/-- The strict-boundary class with weights `3, 2, 1`, which make it orthogonal
to the three strict boundary components. -/
def weightedBoundaryClass (c : Fin 11 → k₀ˣ) : Additive (LineBundleClass Y(c)) :=
  3 • L(c, 0) + 2 • L(c, 1) + L(c, 2)

/-- The weighted boundary class is the indicated combination of the three strict lines. -/
theorem weightedBoundaryClass_def (c : Fin 11 → k₀ˣ) :
    weightedBoundaryClass c = 3 • L(c, 0) + 2 • L(c, 1) + L(c, 2) := (rfl)

/-- The degree of the weighted boundary class on the total exceptional class
reads the weight of the ray carrying that center. -/
theorem classIntersectionNumber_weightedBoundaryClass_exceptionalClass
    (c : Fin 11 → k₀ˣ) (j : Fin 11) :
    let : Y(c).Over S := ⟨T(c).toBase ≫ (P ↘ S)⟩
    Chow.classIntersectionNumber k₀ Y(c) (weightedBoundaryClass c).toMul
      (T(c).exceptionalClass j) =
        if j.val < 2 then 3 else if j.val < 5 then 2 else 1 := by
  classical
  intro _
  let : Scheme.IsProjectiveOver (X := P) k₀ :=
    (Φ).isProjectiveOver_finiteFanScheme_of_isComplete k₀ hΦ hc b
  let : SmoothOfRelativeDimension 2 (P ↘ S) := by
    rw [finiteFanScheme_over]
    simpa using (Φ).smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
  let a (l : Fin 3) := markedBoundaryMap k₀ hΦ planeCenterRay (Pi.single (planeBoundaryRay l) 1)
  have hmk (l : Fin 3) : (T(c)).picardHom (a l) = L(c, l) :=
    picardHom_markedBoundaryMap_single_internalBlowupTower k₀
      hΦ b planeCenterRay c (planeBoundaryRay l)
  have hweight : weightedBoundaryClass c = (T(c)).picardHom (3 • a 0 + 2 • a 1 + a 2) := by
    simp only [weightedBoundaryClass_def, map_add, map_nsmul, hmk]
  rw [hweight, classIntersectionNumber_picardHom_exceptionalClass (hT(c))]
  simp only [a, two_nsmul, three_nsmul, Prod.snd_add, Pi.add_apply, markedBoundaryMap_apply,
    Pi.single_apply, planeCenterRay_apply, planeBoundaryRay.injective.eq_iff]
  fin_cases j <;> decide

/-- In the plane marking, the total exceptional coefficients of the weighted
strict triangle are the negatives of the boundary Casimir exponent. -/
theorem internalBlowupPicardMarking_symm_weightedBoundaryClass_snd (c : Fin 11 → k₀ˣ) :
    ((internalBlowupPicardMarking k₀ b planeCenterRay c hΦ).symm (weightedBoundaryClass c)).2 =
      -boundaryExponent := by
  let : Scheme.IsProjectiveOver (X := P) k₀ :=
    (Φ).isProjectiveOver_finiteFanScheme_of_isComplete k₀ hΦ hc b
  let : SmoothOfRelativeDimension 2 (P ↘ S) := by
    rw [finiteFanScheme_over]
    simpa using (Φ).smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
  funext j
  have h := classIntersectionNumber_picardHom_exceptionalClass (k := k₀)
    (isClosedPointTower_internalBlowupTower k₀ b planeCenterRay c)
    ((internalBlowupPicardMarking k₀ b planeCenterRay c hΦ).symm (weightedBoundaryClass c)) j
  dsimp only at h
  rw [← internalBlowupPicardMarking_apply k₀ b planeCenterRay c hΦ, LinearEquiv.apply_symm_apply,
    classIntersectionNumber_weightedBoundaryClass_exceptionalClass] at h
  have hexp : (if j.val < 2 then (3 : ℤ) else if j.val < 5 then 2 else 1) = boundaryExponent j := by
    simp only [boundaryExponent_apply, rayIndex_eq_ite]
    fin_cases j <;> decide
  exact (neg_eq_iff_eq_neg.mp (h.symm.trans hexp))

/-- The weighted class pairs to zero with each strict line. -/
theorem classIntersectionNumber_weightedBoundaryClass_boundary (c : Fin 11 → k₀ˣ) (j : Fin 3) :
    let : Y(c).Over S := ⟨T(c).toBase ≫ (P ↘ S)⟩
    Chow.classIntersectionNumber k₀ Y(c) (weightedBoundaryClass c).toMul (L(c, j)).toMul = 0 := by
  intro _
  let : IsIntegral (Y(c)) := isIntegral_internalBlowupTower k₀ b planeCenterRay c hΦ
  let : Scheme.IsProjectiveOver (X := Y(c)) k₀ := projective_planeBlowup c
  let : SmoothOfRelativeDimension 2 (Y(c) ↘ S) := smooth_planeBlowup c
  let B := Chow.intersectionBilinForm k₀ Y(c)
  have h (i : Fin 3) :
      B (L(c, i)) (L(c, j)) = if i = j then (![(-1 : ℤ), -2, -5] : Fin 3 → ℤ) i else 1 := by
    rw [Chow.intersectionBilinForm_apply]
    exact classIntersectionNumber_planeBlowup_boundary c i j
  have hz : B (weightedBoundaryClass c) (L(c, j)) = 0 := by
    simp only [weightedBoundaryClass_def, two_nsmul, three_nsmul, map_add, LinearMap.add_apply, h]
    fin_cases j <;> decide
  simpa only [B, Chow.intersectionBilinForm_apply] using hz

/-- The weighted boundary class is primitive, as its pairing with the
exceptional class over label five is one. -/
theorem isPrimitive_weightedBoundaryClass (c : Fin 11 → k₀ˣ) :
    TauCeti.IsPrimitive (weightedBoundaryClass c) := by
  let : Y(c).Over S := ⟨T(c).toBase ≫ (P ↘ S)⟩
  let : IsIntegral (Y(c)) := isIntegral_internalBlowupTower k₀ b planeCenterRay c hΦ
  let : Scheme.IsProjectiveOver (X := Y(c)) k₀ := projective_planeBlowup c
  let : SmoothOfRelativeDimension 2 (Y(c) ↘ S) := smooth_planeBlowup c
  refine TauCeti.isPrimitive_def.mpr
    ⟨(Chow.intersectionBilinForm k₀ Y(c)).flip (Additive.ofMul ((T(c)).exceptionalClass 5)), ?_⟩
  have h := classIntersectionNumber_weightedBoundaryClass_exceptionalClass c 5
  dsimp only at h
  rw [LinearMap.BilinForm.flip_apply, Chow.intersectionBilinForm_apply]
  exact h.trans (by decide)

/-- The weighted boundary class has square zero on the auxiliary surface. -/
theorem classIntersectionNumber_weightedBoundaryClass_self (c : Fin 11 → k₀ˣ) :
    let : Y(c).Over S := ⟨T(c).toBase ≫ (P ↘ S)⟩
    Chow.classIntersectionNumber k₀ Y(c) (weightedBoundaryClass c).toMul
      (weightedBoundaryClass c).toMul = 0 := by
  intro _
  let : IsIntegral (Y(c)) := isIntegral_internalBlowupTower k₀ b planeCenterRay c hΦ
  let : Scheme.IsProjectiveOver (X := Y(c)) k₀ := projective_planeBlowup c
  let : SmoothOfRelativeDimension 2 (Y(c) ↘ S) := smooth_planeBlowup c
  let B := Chow.intersectionBilinForm k₀ Y(c)
  have h (j : Fin 3) : B (weightedBoundaryClass c) (L(c, j)) = 0 :=
    (Chow.intersectionBilinForm_apply _ _ _ _).trans
      (classIntersectionNumber_weightedBoundaryClass_boundary c j)
  have hz : B (weightedBoundaryClass c) (weightedBoundaryClass c) = 0 := by
    nth_rewrite 2 [weightedBoundaryClass_def]
    simp only [map_add, map_nsmul, h, nsmul_zero, add_zero]
  simpa only [B, Chow.intersectionBilinForm_apply] using hz

end QPainleve.ElevenVertex
