/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Numerical
public import QPainleve.AlgebraicGeometry.Chow.ProjectivePlane
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Smooth
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic

/-!
# Signature of the real Picard intersection form

A closed point blowup adds one negative square to the Picard intersection form, in the
coordinates given by the total transforms of its exceptional divisors. A pair of towers
with isomorphic final surfaces identifies the two stabilized real forms. For a common
resolution with the projective plane this gives signature `(1, ρ - 1)`, where `ρ` is the
dimension of the real Picard space.

The comparison uses `QPainleve.BlowupTower.classIntersectionNumber_picardEquivOfCommonResolution`
and `TauCeti.bilinFormBaseChangeProdIsometry`. For the Picard decomposition of a point blowup,
see Hacking, *Compact Complex Surfaces*, Proposition 7.1.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower QuadraticMap
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry.Chow

universe u

local notation "Pic(" X ")" => Additive (LineBundleClass X)

section RealForm

variable (k : Type u) [Field k] [Infinite k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [IsIntegral X] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "f" => (X ↘ Spec (CommRingCat.of k))

private def intersectionBilinForm : LinearMap.BilinForm ℤ (Pic(X)) :=
  let hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  let : IsNoetherian X := isNoetherian_of_finiteType f
  let : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  let : IsRegular X := IsRegular.of_smooth f
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    fun x ↦ IsRegular.uniqueFactorizationMonoid_stalk x
      (WithBot.coe_le_coe.mp ((coheight_le_topologicalKrullDim x).trans_eq hX))
  classIntersectionBilinForm k hX

private theorem intersectionBilinForm_apply (x y : Pic(X)) :
    intersectionBilinForm k X x y = classIntersectionNumber k X x.toMul y.toMul := by
  simp only [intersectionBilinForm, classIntersectionBilinForm_apply]

/-- The scalar extension of the surface intersection pairing to the real Picard space. -/
def realIntersectionBilinForm : LinearMap.BilinForm ℝ (ℝ ⊗[ℤ] Pic(X)) :=
  (intersectionBilinForm k X).baseChange ℝ

/-- On pure tensors, the real pairing multiplies the integral intersection by both scalars. -/
@[simp]
theorem realIntersectionBilinForm_tmul (r s : ℝ) (x y : Pic(X)) :
    realIntersectionBilinForm k X (r ⊗ₜ x) (s ⊗ₜ y) =
      (r * s) * (classIntersectionNumber k X x.toMul y.toMul : ℝ) := by
  simp only [realIntersectionBilinForm, LinearMap.BilinForm.baseChange_tmul,
    intersectionBilinForm_apply, ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul, mul_comm]

/-- The real intersection form of a smooth integral projective surface is symmetric. -/
theorem isSymm_realIntersectionBilinForm : (realIntersectionBilinForm k X).IsSymm := by
  have h : LinearMap.IsSymm (intersectionBilinForm k X) := by
    refine ⟨fun x y ↦ ?_⟩
    simpa only [RingHom.id_apply, intersectionBilinForm_apply] using
      (classIntersectionNumber_comm (k := k) x.toMul y.toMul)
  exact LinearMap.BilinForm.isSymm_iff.mpr (LinearMap.BilinForm.IsSymm.baseChange ℝ h)

end RealForm

local notation "negDot(" d ")" => (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin d → ℤ)))
local notation "Qℝ(" K ", " S ")" =>
  LinearMap.BilinMap.toQuadraticMap (realIntersectionBilinForm K S)
local notation "negReal(" d ")" => LinearMap.BilinForm.baseChange ℝ negDot(d)
local notation "N(" d ")" => LinearMap.BilinMap.toQuadraticMap negReal(d)

private theorem equivalent_negDot (d : ℕ) :
    (N(d)).Equivalent (weightedSumSquares ℝ (-1 : Fin d → ℝ)) := by
  let b := (Pi.basisFun ℤ (Fin d)).baseChange ℝ
  have h : (negReal(d)).toMatrix b = Matrix.diagonal (-1 : Fin d → ℝ) := by
    rw [LinearMap.BilinForm.toMatrix_baseChange]
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, dotProductBilin_apply_apply, dotProduct,
      Pi.basisFun_apply, Pi.single_apply, Matrix.diagonal_apply, apply_ite, eq_comm]
  have eqv := (negReal(d)).equivalent_toQuadraticForm'_toMatrix b
  rw [h, Matrix.toQuadraticForm'_diagonal] at eqv
  exact eqv.symm

section CommonResolution

variable (k : Type u) [Field k] [IsAlgClosed k]
  {X Z Y W : Scheme.{u}} {m n : ℕ}
  [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [Z.IsProjectiveOver k] [IsIntegral X] [IsIntegral Z]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k))]
  {T : BlowupTower X m Y} {U : BlowupTower Z n W}
  (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Z U)
  (e : W ≅ Y)
  (he : e.hom ≫ T.toBase ≫ (X ↘ Spec (.of k)) = U.toBase ≫ (Z ↘ Spec (.of k)))

local notation "Bℤ(" S ")" => intersectionBilinForm k S

include hT hU he in
private theorem equivalent_realIntersectionForm_prod_of_common_resolution :
    ((Qℝ(k, X)).prod N(m)).Equivalent ((Qℝ(k, Z)).prod N(n)) := by
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  have : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ Spec (.of k))
  let E : ((Bℤ(X)).prod negDot(m)).IsometryEquiv ((Bℤ(Z)).prod negDot(n)) :=
    { toLinearEquiv := picardEquivOfCommonResolution k hT hU e
      map_app' := fun a b ↦ by
        simpa only [LinearMap.BilinForm.prod_apply, intersectionBilinForm_apply,
          LinearMap.neg_apply, dotProductBilin_apply_apply, dotProduct, ← sub_eq_add_neg,
          LinearMap.toFun_eq_coe, LinearEquiv.coe_coe] using
          classIntersectionNumber_picardEquivOfCommonResolution k hT hU e he a b }
  let left := TauCeti.bilinFormBaseChangeProdIsometry ℝ Bℤ(X) negDot(m)
  let right := TauCeti.bilinFormBaseChangeProdIsometry ℝ Bℤ(Z) negDot(n)
  let realE := left.symm.trans ((E.baseChange ℝ).trans right)
  simpa only [realIntersectionBilinForm, LinearMap.BilinForm.toQuadraticMap_prod] using
    LinearMap.BilinForm.Equivalent.toQuadraticMap ⟨realE⟩

include hT hU he in
/-- The positive index of the real Picard form is independent of the base of a common
point-blowup resolution. The negative index changes by the difference of the tower lengths. -/
theorem signature_realIntersectionBilinForm_of_common_resolution
    [Module.Finite ℝ (ℝ ⊗[ℤ] Pic(X))] :
    sigPos Qℝ(k, X) = sigPos Qℝ(k, Z) ∧ sigNeg Qℝ(k, X) + m = sigNeg Qℝ(k, Z) + n := by
  have E := equivalent_realIntersectionForm_prod_of_common_resolution k hT hU e he
  let eℝ := Classical.choice E
  have : Module.Finite ℝ ((ℝ ⊗[ℤ] Pic(Z)) × (ℝ ⊗[ℤ] (Fin n → ℤ))) :=
    Module.Finite.of_surjective eℝ.toLinearEquiv.toLinearMap eℝ.surjective
  have : Module.Finite ℝ (ℝ ⊗[ℤ] Pic(Z)) :=
    Module.Finite.of_surjective (LinearMap.fst ℝ (ℝ ⊗[ℤ] Pic(Z)) (ℝ ⊗[ℤ] (Fin n → ℤ)))
      Prod.fst_surjective
  constructor
  · simpa [QuadraticForm.sigPos_prod, (equivalent_negDot m).sigPos_eq,
      (equivalent_negDot n).sigPos_eq, QuadraticForm.sigPos_weightedSumSquares,
      not_lt_of_ge (zero_le_one : (0 : ℝ) ≤ 1)] using E.sigPos_eq
  · simpa [QuadraticForm.sigNeg_prod, (equivalent_negDot m).sigNeg_eq,
      (equivalent_negDot n).sigNeg_eq, QuadraticForm.sigNeg_weightedSumSquares] using E.sigNeg_eq

end CommonResolution

section ProjectivePlane

open TauCeti.SymmetricAlgebra

variable (k : Type u) [Field k]

local notation "Plane(" K ")" => Proj (homogeneousSubmodule K (Fin 3 → K))
local notation "degree(" K ")" => AddEquiv.toIntLinearEquiv
  (Module.Basis.picardTwistEquiv (Pi.basisFun K (Fin 3)))

variable [Infinite k] in
/-- The real Picard form of the projective plane is a single positive square,
in the coordinate of the hyperplane class. -/
theorem equivalent_realIntersectionBilinForm_projectivePlane :
    (Qℝ(k, Plane(k))).Equivalent (weightedSumSquares ℝ (1 : Fin 1 → ℝ)) := by
  let b := ((Module.Basis.singleton (Fin 1) ℤ).map (degree(k)).symm).baseChange ℝ
  have h : (realIntersectionBilinForm k Plane(k)).toMatrix b =
      Matrix.diagonal (1 : Fin 1 → ℝ) := by
    ext i j
    simp only [b, LinearMap.BilinForm.toMatrix_apply, Module.Basis.baseChange_apply,
      Module.Basis.map_apply, Module.Basis.singleton_apply, realIntersectionBilinForm_tmul,
      classIntersectionNumber_projectivePlane, Matrix.diagonal_apply, Subsingleton.elim i j]
    norm_num
  have eqv := (realIntersectionBilinForm k Plane(k)).equivalent_toQuadraticForm'_toMatrix b
  rw [h, Matrix.toQuadraticForm'_diagonal] at eqv
  exact eqv.symm

variable [IsAlgClosed k]
  {X Y W : Scheme.{u}} {m n : ℕ}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {T : BlowupTower X m Y} {U : BlowupTower Plane(k) n W}
  (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Plane(k) U) (e : W ≅ Y)
  (he : e.hom ≫ T.toBase ≫ (X ↘ Spec (.of k)) = U.toBase ≫ (Plane(k) ↘ Spec (.of k)))

include hT hU he in
/-- A smooth integral projective surface with a common point-blowup resolution with
the projective plane has a nondegenerate real Picard form of signature `(1, ρ - 1)`. -/
theorem signature_realIntersectionBilinForm_of_common_resolution_projectivePlane :
    (Qℝ(k, X)).Nondegenerate ∧ sigPos Qℝ(k, X) = 1 ∧
      sigNeg Qℝ(k, X) = Module.finrank ℝ (ℝ ⊗[ℤ] Pic(X)) - 1 := by
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  have : IsNoetherian Plane(k) := isNoetherian_of_finiteType (Plane(k) ↘ Spec (.of k))
  have : Module.Finite ℤ (Pic(Plane(k))) := Module.Finite.of_surjective (degree(k)).symm.toLinearMap
    (degree(k)).symm.surjective
  have : Module.Finite ℤ (Pic(X)) := (finite_picard_iff_of_common_resolution k hT hU e).mpr ‹_›
  have hplane := equivalent_realIntersectionBilinForm_projectivePlane k
  have ⟨hp, hn⟩ := signature_realIntersectionBilinForm_of_common_resolution k hT hU e he
  have hp₀ : sigPos Qℝ(k, Plane(k)) = 1 := by
    simp [hplane.sigPos_eq, QuadraticForm.sigPos_weightedSumSquares]
  have hn₀ : sigNeg Qℝ(k, Plane(k)) = 0 := by
    simp [hplane.sigNeg_eq, QuadraticForm.sigNeg_weightedSumSquares,
      not_lt_of_ge (zero_le_one : (0 : ℝ) ≤ 1)]
  rw [hp₀] at hp
  rw [hn₀, zero_add] at hn
  obtain ⟨E⟩ := equivalent_realIntersectionForm_prod_of_common_resolution k hT hU e he
  obtain ⟨ep⟩ := hplane
  have hr := E.toLinearEquiv.finrank_eq
  have hrP := ep.toLinearEquiv.finrank_eq
  have hfin (d : ℕ) : Module.finrank ℝ (ℝ ⊗[ℤ] (Fin d → ℤ)) = d := by
    simp only [Module.finrank_baseChange, Module.finrank_pi, Fintype.card_fin]
  simp only [Module.finrank_prod, hfin] at hr
  simp only [Module.finrank_pi, Fintype.card_fin] at hrP
  have hdim := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Qℝ(k, X))
  let : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  exact ⟨QuadraticMap.nondegenerate_iff_radical_eq_bot.mpr
    (Submodule.finrank_eq_zero.mp (by omega)), hp, by omega⟩

end ProjectivePlane

end TauCeti.AlgebraicGeometry.Chow
