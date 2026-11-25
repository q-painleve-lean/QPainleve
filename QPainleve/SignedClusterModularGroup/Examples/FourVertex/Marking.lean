/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Basic
public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.InternalBlowup

import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
import QPainleve.SignedClusterModularGroup.Examples.FourVertex.AffineA1

/-!
# The Picard marking of the four-vertex octagon

The two rulings and the four corner classes of the toric octagon, followed
by the four internal exceptional classes, give an integral intersection
marking. It identifies the numbered boundary and the two charge-kernel
generators with their geometric classes.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory LinearMap Module QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Chow TauCeti.Toric

namespace QPainleve.FourVertex

local notation "N" => (Fin 2 → ℤ)
local notation "i₂" => AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin 2)
local notation "b₂" => Pi.basisFun ℤ (Fin 2)
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "L" => (Fin 10 → ℤ)
local notation "E" => (Fin 4 → ℤ)

variable {Φ : Fan i₂} [Nonempty Φ.cones] (hΦ : Φ.IsRegular) (v : ZMod 8 ≃ Φ.Ray)

local notation "X" => Φ.algebraicRealization
local notation "Pic" => Additive (LineBundleClass X)
local notation "R" j:arg => Φ.rayDivisorToPicard hΦ (Pi.single (v j) 1)
local notation "β" => Pi.basisFun ℤ (Fin 10)

local notation "ζ" => (ZMod.finEquiv 8)

-- The two rulings are obtained by adding the neighboring corner rays
-- to the first two axial rays.
private def rayCoefficients : Fin 10 → Fin 8 → ℤ :=
  ![![1, 1, 0, 0, 0, 0, 0, 1], ![0, 1, 1, 1, 0, 0, 0, 0],
    Pi.single 1 1, Pi.single 3 1, Pi.single 5 1, Pi.single 7 1, 0, 0, 0, 0]

private def rayClassMap : (Fin 8 → ℤ) →ₗ[ℤ] Pic :=
  (Pi.basisFun ℤ (Fin 8)).constr ℤ fun j ↦ R (ζ j)

private theorem rayClassMap_single (j : Fin 8) :
    rayClassMap hΦ v (Pi.single j 1) = R (ζ j) := by
  rw [← Pi.basisFun_apply, rayClassMap, Basis.constr_basis]

private def auxiliaryPicardMap : L →ₗ[ℤ] Pic × E :=
  ((β).constr ℤ (fun j ↦ rayClassMap hΦ v (rayCoefficients j))).prod
    (LinearMap.funLeft ℤ ℤ (Fin.natAdd 6))

private theorem auxiliaryPicardMap_apply (x : L) :
    auxiliaryPicardMap hΦ v x =
      (rayClassMap hΦ v (∑ j, x j • rayCoefficients j), fun j ↦ x (j.natAdd 6)) := by
  simp only [auxiliaryPicardMap, LinearMap.prod_apply, Function.prod_apply,
    Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply, map_sum, map_smul]
  rfl

private theorem auxiliaryPicardMap_single (j : Fin 10) :
    auxiliaryPicardMap hΦ v (Pi.single j 1) =
      (rayClassMap hΦ v (rayCoefficients j), fun k : Fin 4 ↦
        (Pi.single j 1 : L) (k.natAdd 6)) := by
  rw [auxiliaryPicardMap, LinearMap.prod_apply, Function.prod_apply]
  congr 1
  rw [← Pi.basisFun_apply, Basis.constr_basis]

private theorem auxiliaryPicardMap_single_natAdd (j : Fin 4) :
    auxiliaryPicardMap hΦ v (Pi.single (j.natAdd 6) 1) = (0, Pi.single j 1) := by
  rw [auxiliaryPicardMap_single]
  have h : ∀ j : Fin 4, rayCoefficients (j.natAdd 6) = 0 ∧
      (fun k : Fin 4 ↦ (Pi.single (j.natAdd 6) 1 : L) (k.natAdd 6)) = Pi.single j 1 := by
    decide
  rw [(h j).1, (h j).2, map_zero]

variable (hv : ∀ j, (v j).primitiveGenerator = octagonGenerator j)

private def characterCoefficients (k : Fin 2) : Fin 8 → ℤ :=
  ![![1, 1, 0, -1, -1, -1, 0, 1], ![0, 1, 1, 1, 0, -1, -1, -1]] k

private theorem characterCoefficients_apply (k : Fin 2) (j : Fin 8) :
    characterCoefficients k j = octagonGenerator (ζ j) k := by
  rw [octagonGenerator_apply, RingEquiv.symm_apply_apply]
  revert k j
  decide

include hv in
open Classical in
private theorem rayClassMap_characterCoefficients (k : Fin 2) :
    rayClassMap hΦ v (characterCoefficients k) = 0 := by
  let : Fintype Φ.Ray := Fintype.ofFinite Φ.Ray
  let m : N →+ ℤ := (LinearMap.proj k : N →ₗ[ℤ] ℤ).toAddMonoidHom
  have h := (Φ.exact_characterToRayDivisor_rayDivisorToPicard hΦ _).mpr ⟨m, rfl⟩
  rw [Φ.rayDivisorToPicard_apply hΦ, ← ((ζ).toEquiv.trans v).sum_comp] at h
  simpa only [rayClassMap, Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply,
    characterCoefficients_apply, Equiv.trans_apply, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    Fan.characterToRayDivisor_apply, hv, m, LinearMap.toAddMonoidHom_coe, LinearMap.proj_apply,
    Fan.rayDivisorToPicard_single, one_zsmul] using h

include hv in
open Classical in
private theorem auxiliaryPicardMap_boundaryClass (j : ZMod 8) :
    auxiliaryPicardMap hΦ v (boundaryClass j) =
      Φ.markedBoundaryMap hΦ (diagonalRay v) (Pi.single (v j) 1) := by
  apply Prod.ext
  · obtain ⟨j, rfl⟩ := (ζ).surjective j
    -- The opposite axial rays use the two character divisor relations.
    have h : ∀ j : Fin 8, (∑ k, boundaryClass (ζ j) k • rayCoefficients k) =
        Pi.single j 1 + (if j = 4 then 1 else 0 : ℤ) • characterCoefficients 0 +
          (if j = 6 then 1 else 0 : ℤ) • characterCoefficients 1 := by
      decide
    rw [auxiliaryPicardMap_apply, Fan.markedBoundaryMap_apply, Prod.fst, Prod.fst, h]
    simp only [map_add, map_smul, rayClassMap_characterCoefficients hΦ v hv, smul_zero, add_zero,
      rayClassMap_single]
  · rw [auxiliaryPicardMap_apply, Fan.markedBoundaryMap_apply]
    funext k
    simp only [diagonalRay_apply, Pi.single_apply, Equiv.apply_eq_iff_eq]
    revert j k
    decide

include hv in
open Classical in
private theorem auxiliaryPicardMap_surjective :
    Function.Surjective (auxiliaryPicardMap hΦ v) := by
  let A := auxiliaryPicardMap hΦ v
  have hE' (x : E) : (0, x) ∈ A.range := by
    let f : E →ₗ[ℤ] Pic × E := LinearMap.inr ℤ Pic E
    have hs : ⊤ ≤ A.range.comap f := by
      rw [← (Pi.basisFun ℤ (Fin 4)).span_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨_, by simpa only [f, LinearMap.inr_apply, Pi.basisFun_apply]
        using auxiliaryPicardMap_single_natAdd hΦ v j⟩
    exact hs (Submodule.mem_top (x := x))
  have hR (j : ZMod 8) : (R j, 0) ∈ A.range := by
    have hj : Φ.markedBoundaryMap hΦ (diagonalRay v) (Pi.single (v j) 1) ∈ A.range :=
      ⟨_, auxiliaryPicardMap_boundaryClass hΦ v hv j⟩
    rw [Fan.markedBoundaryMap_apply] at hj
    have hx := hE' (fun k ↦ -(Pi.single (v j) 1 : Φ.Ray → ℤ) (diagonalRay v k))
    simpa only [Prod.mk_sub_mk, sub_zero, sub_self] using A.range.sub_mem hj hx
  rintro ⟨y, x⟩
  obtain ⟨a, rfl⟩ := Φ.rayDivisorToPicard_surjective hΦ y
  let : Fintype Φ.Ray := Fintype.ofFinite Φ.Ray
  have hy : (Φ.rayDivisorToPicard hΦ a, (0 : E)) ∈ A.range := by
    let f : Pic →ₗ[ℤ] Pic × E := LinearMap.inl ℤ Pic E
    have he : f (Φ.rayDivisorToPicard hΦ a) ∈ A.range := by
      rw [Φ.rayDivisorToPicard_apply hΦ, ← v.sum_comp, map_sum]
      simp only [map_smul]
      exact A.range.sum_mem fun j _ ↦ A.range.smul_mem (a (v j))
        (by simpa only [f, LinearMap.inl_apply, Fan.rayDivisorToPicard_single, one_zsmul]
          using hR j)
    exact he
  simpa using A.range.add_mem hy (hE' x)

variable (hc : Φ.IsComplete)
  (hnext : ∀ j, (b₂).detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
    ∃ σ : Φ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ)
  [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ))]

local notation "B" => intersectionBilinForm ℂ X
local notation "Aux" =>
  LinearMap.BilinForm.prod B (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ E))

include hv hc hnext in
open Classical in
private theorem auxiliaryPicardMap_isometry :
    (Aux).comp (auxiliaryPicardMap hΦ v) (auxiliaryPicardMap hΦ v) = intersectionForm := by
  apply BilinForm.ext_basis β
  intro j k
  simp only [BilinForm.comp_apply, Pi.basisFun_apply, auxiliaryPicardMap_single,
    BilinForm.prod_apply, LinearMap.neg_apply, dotProductBilin_apply_apply]
  simp only [rayClassMap, Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply]
  simp_rw [BilinForm.sum_left, BilinForm.sum_right, BilinForm.smul_left, BilinForm.smul_right,
    intersectionBilinForm_octagon_rayClasses hΦ hc v hv hnext]
  rw [intersectionForm_apply]
  revert j k
  decide

/-- The Picard coordinates of the octagon and its four ordered internal blowups.
The first two coordinate classes are the pullbacks of the rulings, the next four
are the diagonal ray classes, and the last four are the internal exceptional classes. -/
def picardCoordinateIsometry : intersectionForm.IsometryEquiv Aux := by
  let A := auxiliaryPicardMap hΦ v
  have hB := auxiliaryPicardMap_isometry hΦ v hv hc hnext
  have hpair (x y : L) : Aux (A x) (A y) = intersectionForm x y :=
    BilinForm.congr_fun hB x y
  refine ⟨LinearEquiv.ofBijective A ⟨?_, auxiliaryPicardMap_surjective hΦ v hv⟩, hpair⟩
  intro x y hxy
  apply sub_eq_zero.mp
  apply intersectionForm_nondegenerate.1
  intro z
  rw [← hpair, map_sub, hxy, sub_self, map_zero₂]

/-- The numbered lattice boundary class maps to the strict ray class in the
ordered toric Picard coordinates. -/
@[simp]
theorem picardCoordinateIsometry_boundaryClass (j : ZMod 8) :
    picardCoordinateIsometry hΦ v hv hc hnext (boundaryClass j) =
      Φ.markedBoundaryMap hΦ (diagonalRay v) (Pi.single (v j) 1) :=
  auxiliaryPicardMap_boundaryClass hΦ v hv j

/-- The final four coordinate vectors are the ordered internal exceptional classes. -/
@[simp]
theorem picardCoordinateIsometry_single_natAdd (j : Fin 4) :
    picardCoordinateIsometry hΦ v hv hc hnext (Pi.single (j.natAdd 6) 1) =
      (0, Pi.single j 1) :=
  auxiliaryPicardMap_single_natAdd hΦ v j

local notation "K" => intersectionForm.orthogonal (Submodule.span ℤ (Set.range boundaryClass))

/-- In the geometric marking, the negative exceptional coefficients of every
boundary orthogonal vector are its exchange-kernel coordinates. This identifies
the lattice and Casimir actions in the same ordered basis. -/
theorem neg_snd_picardCoordinateIsometry (x : K) :
    -(picardCoordinateIsometry hΦ v hv hc hnext x).2 =
      (exchangeKernelEquiv (boundaryOrthogonalBasis.equivFun x) : Fin 4 → ℤ) := by
  rw [← boundaryOrthogonalEquivExchangeKernel_apply,
    coe_boundaryOrthogonalEquivExchangeKernel_apply]
  funext j
  simpa only [picardCoordinateIsometry_single_natAdd, BilinForm.prod_apply, Prod.fst,
    Prod.snd, map_zero, zero_add, LinearMap.neg_apply, dotProductBilin_apply_apply,
    dotProduct_single_one, Pi.neg_apply] using
    (picardCoordinateIsometry hΦ v hv hc hnext).map_app (Pi.single (j.natAdd 6) 1) x.val

section InternalBlowup

variable (c : Fin 4 → ℂˣ)

local notation "model" => Fan.internalBlowupTower b₂ (diagonalRay v) c
local notation "Y" => Sigma.fst model
local notation "T" => WithBoundary.toTower (Sigma.snd model)
local notation "hT" => Fan.isClosedPointTower_internalBlowupTower b₂ (diagonalRay v) c
local notation "f" => Φ.algebraicRealization ↘ S
local notation "M" => Fan.internalBlowupPicardMarking b₂ (diagonalRay v) c hΦ
local notation "I" => picardCoordinateIsometry hΦ v hv hc hnext

include hv hc hnext in
/-- The integral marking of the actual four-vertex blowup surface, for every
choice of the four nonzero center parameters. -/
def internalBlowupPicardIsometry :
    letI : IsIntegral Y := Fan.isIntegral_internalBlowupTower b₂ (diagonalRay v) c hΦ
    letI : (Y).Over S := ⟨(T).toBase ≫ f⟩
    letI : (Y).IsProjectiveOver ℂ := (T).isProjectiveOver ℂ
    letI : SmoothOfRelativeDimension 2 (Y ↘ S) := (hT).smoothOfRelativeDimension f
    intersectionForm.IsometryEquiv (intersectionBilinForm ℂ Y) := by
  let A := I
  letI : IsIntegral Y := Fan.isIntegral_internalBlowupTower b₂ (diagonalRay v) c hΦ
  letI : (Y).Over S := ⟨(T).toBase ≫ f⟩
  letI : (Y).IsProjectiveOver ℂ := (T).isProjectiveOver ℂ
  letI : SmoothOfRelativeDimension 2 (Y ↘ S) := (hT).smoothOfRelativeDimension f
  refine { A.toLinearEquiv.trans M with map_app' := fun x y ↦ ?_ }
  have h := classIntersectionNumber_picardMarking ℂ (hT) (A x) (A y)
  have h' : classIntersectionNumber ℂ X (A x).1.toMul (A y).1.toMul -
      ∑ j, (A x).2 j * (A y).2 j = intersectionForm x y := by
    simpa only [BilinForm.prod_apply, LinearMap.map_neg₂, LinearMap.neg_apply,
      dotProductBilin_apply_apply, intersectionBilinForm_apply, dotProduct, ← sub_eq_add_neg]
      using A.map_app y x
  have he := intersectionBilinForm_apply ℂ Y (M (A x)) (M (A y))
  refine he.trans ?_
  simpa only [Fan.internalBlowupPicardMarking_apply, picardMarking_apply] using h.trans h'

/-- The surface marking is the octagon lattice marking in the ordered
toric and exceptional coordinates. -/
theorem internalBlowupPicardIsometry_apply (x : L) :
    internalBlowupPicardIsometry hΦ v c (hv := hv) (hc := hc) (hnext := hnext) x = M (I x) :=
  (rfl)

/-- The marked boundary vector is the Picard class of the scheme-theoretic
strict transform of the corresponding octagon boundary component. -/
@[simp]
theorem internalBlowupPicardIsometry_boundaryClass (j : ZMod 8) :
    internalBlowupPicardIsometry hΦ v c (hv := hv) (hc := hc) (hnext := hnext) (boundaryClass j) =
      Fan.strictRayBoundaryClass hΦ (by simp : Module.finrank ℤ N = 2) T hT (v j) := by
  classical
  rw [internalBlowupPicardIsometry_apply, picardCoordinateIsometry_boundaryClass,
    Fan.internalBlowupPicardMarking_apply]
  exact Fan.picardHom_markedBoundaryMap_single_internalBlowupTower hΦ b₂ (diagonalRay v) c (v j)

end InternalBlowup

end QPainleve.FourVertex
