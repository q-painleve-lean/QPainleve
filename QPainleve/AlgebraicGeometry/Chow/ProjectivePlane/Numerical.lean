/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.ProjectivePlane.Basic
public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Canonical
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Integral
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
import TauCeti.LinearAlgebra.Matrix.Dual

/-!
# Numerical invariants of the projective plane

The canonical class has Picard coordinate `-3`. With the intersection pairing and Euler
characteristic in the hyperplane coordinate, this gives the canonical square and the
projective-plane case of Riemann–Roch ([Hacking, *Compact Complex Surfaces*, Theorem 5.2][Hacking]).
The rank-one Picard pairing is unimodular, and the structure sheaf has no higher cohomology.

The canonical class comparison uses `Proj.differentialFormsTwoIsoTwistingSheaf` and the
basis-induced comparison of polynomial and symmetric-algebra twists.

[Hacking]: https://paulhacking.github.io/surfaces.pdf#page=30
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve
open TauCeti.SymmetricAlgebra
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u)

local notation "𝒮" => homogeneousSubmodule k (Fin 3 → k)
local notation "P" => Proj 𝒮
local notation "f" => P ↘ Spec (CommRingCat.of k)
local notation "basis" => Pi.basisFun k (Fin 3)
local notation "degree" => Module.Basis.picardTwistEquiv (Pi.basisFun k (Fin 3))
local notation "K" => LineBundleClass.mk (canonicalBundle k P 2)

local instance planeSmooth [CommRing k] : SmoothOfRelativeDimension 2 f :=
  (basis).smoothOfRelativeDimension_projToSpec (n := 2)

section

variable [CommRing k]

/-- The projective plane has vanishing structure-sheaf cohomology in positive degrees. -/
theorem subsingleton_cohomology_trivial_projectivePlane {i : ℕ} (hi : 0 < i) :
    Subsingleton (Cohomology (InvertibleSheaf.trivial P).obj i) := by
  have : Subsingleton (Cohomology (Proj.twistingSheaf 𝒮 0) i) :=
    (basis).subsingleton_cohomology_twistingSheaf_of_neg_card_lt (by decide) hi
  let e := InvertibleSheaf.trivialObjIsoUnit P ≪≫ Proj.unitIsoTwistingSheafZero 𝒮
  exact (cohomologyBaseLinearEquivOfIso k e i).injective.subsingleton

/-- The canonical class of the projective plane is the class of the twist `𝒪(-3)`. -/
theorem LineBundleClass.mk_canonicalBundle_projectivePlane :
    K = mk (Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) (-3)) := by
  let A := MvPolynomial.homogeneousSubmodule (Fin 3) k
  let : (Proj A).Over (Spec (.of k)) := ⟨Proj.toSpecCoeff A⟩
  let : SmoothOfRelativeDimension 2 (Proj A ↘ Spec (.of k)) :=
    Proj.smoothOfRelativeDimension_polynomial k
  let e := (basis).polynomialProjIso
  let : e.hom.IsOver (Spec (.of k)) := ⟨(basis).polynomialProjIso_hom_over⟩
  apply (pullbackEquiv e).injective
  simp only [pullbackEquiv_apply, pullback_mk, mk_pullback_canonicalBundle, mk_eq_mk_iff,
    canonicalBundle_obj, differentialForms_def, InvertibleSheaf.pullback_obj_obj,
    Proj.symmetricAlgebraTwistingBundle_obj]
  exact ⟨(Proj.differentialFormsTwoIsoTwistingSheaf k).trans
    ((basis).polynomialProjIsoPullbackTwistingSheafIso (-3)).symm⟩

end

variable [Field k]

/-- The structure sheaf of the projective plane has Euler characteristic one. -/
theorem LineBundleClass.eulerCharBelow_one_projectivePlane :
    eulerCharBelow k (1 : LineBundleClass P) 3 = 1 := by
  rw [eulerCharBelow_projectivePlane]
  norm_num

local instance planeIntegral : IsIntegral P := by
  let := Proj.isIntegral_polynomialProj (R := k) (σ := Fin 3)
  exact IsIntegral.of_isIso (basis).polynomialProjIso.hom

local instance planeRegular : IsRegular P :=
  let := SmoothOfRelativeDimension.smooth 2 f
  IsRegular.of_smooth f

/-- In the hyperplane coordinate, the integral intersection pairing of the projective plane
is perfect. -/
theorem Chow.isPerfPair_classIntersectionBilinForm_projectivePlane [Infinite k] :
    let hP : topologicalKrullDim P = 2 := topologicalKrullDim_eq_of_smoothOfRelativeDimension f
    let : ∀ x : P, UniqueFactorizationMonoid ((P).presheaf.stalk x) := fun x ↦
      IsRegular.uniqueFactorizationMonoid_stalk x
        (WithBot.coe_le_coe.mp ((coheight_le_topologicalKrullDim x).trans_eq hP))
    (classIntersectionBilinForm k hP).IsPerfPair := by
  intro hP _
  let e : Additive (LineBundleClass P) ≃ₗ[ℤ] (Fin 1 → ℤ) :=
    (degree).toIntLinearEquiv.trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  let D : LinearMap.BilinForm ℤ (Fin 1 → ℤ) := dotProductBilin ℤ ℤ
  have : D.IsPerfPair := inferInstanceAs (dotProductBilin ℤ ℤ).IsPerfPair
  refine LinearMap.IsPerfPair.congr D e e _ (LinearMap.ext₂ fun x y ↦ ?_)
  simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, classIntersectionBilinForm_apply,
    classIntersectionNumber_projectivePlane, ofMul_toMul, D, dotProductBilin_apply_apply,
    dotProduct, Fin.sum_univ_one]
  simp [e, LinearEquiv.funUnique_apply]

/-- The canonical class of the projective plane has self-intersection nine. -/
theorem Chow.classIntersectionNumber_canonicalBundle_projectivePlane :
    classIntersectionNumber k P K K = 9 := by
  rw [classIntersectionNumber_projectivePlane, LineBundleClass.mk_canonicalBundle_projectivePlane]
  norm_num

/-- The projective-plane Riemann–Roch formula, multiplied by two to retain the parity
of the intersection numerator. -/
theorem LineBundleClass.eulerCharBelow_eq_riemannRoch_projectivePlane
    (a : LineBundleClass P) :
    2 * (eulerCharBelow k a 3 - 1) =
      Chow.classIntersectionNumber k P a a - Chow.classIntersectionNumber k P a K := by
  rw [eulerCharBelow_projectivePlane, Chow.classIntersectionNumber_projectivePlane,
    Chow.classIntersectionNumber_projectivePlane, mk_canonicalBundle_projectivePlane,
    (basis).picardTwistEquiv_apply_twist]
  let d := degree (Additive.ofMul a)
  have hd : 2 ∣ (d + 1) * (d + 2) := by
    convert Int.two_dvd_mul_add_one (d + 1) using 2
    ring
  have h := Int.ediv_mul_cancel hd
  nlinarith only [h]

end TauCeti.AlgebraicGeometry
