/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Topology.Algebra.Module.PerfectPairing
public import QPainleve.AlgebraicGeometry.AffineSpace.Dimension
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Factorization
public import QPainleve.AlgebraicGeometry.Chow.Adjunction
public import QPainleve.AlgebraicGeometry.Chow.ProjectivePlane.Numerical
public import QPainleve.AlgebraicGeometry.Chow.Signature
public import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
public import TauCeti.LinearAlgebra.BilinearForm.Characteristic

import QPainleve.AlgebraicGeometry.Blowup.Tower.Cohomology
import QPainleve.AlgebraicGeometry.Blowup.Tower.RiemannRoch
import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Rationality
import QPainleve.Topology.Algebra.Module.PerfectPairing
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear

/-!
# Numerical invariants of smooth projective rational surfaces

A common resolution with the projective plane transports structure-sheaf cohomology,
the integral Picard pairing, and Riemann–Roch to any smooth projective rational surface.
In particular, the Picard group is finite free with perfect intersection pairing,
the Picard rank plus the canonical square is ten, and the canonical class is
characteristic. The Riemann–Roch formula gives arithmetic adjunction for every closed
integral curve on the surface.

See [Hacking, *Compact Complex Surfaces*, §5.2][Hacking] for the
numerical formulas and adjunction.

[Hacking]: https://paulhacking.github.io/surfaces.pdf#page=30
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower QuadraticMap
open TauCeti.AlgebraicGeometry TauCeti.SymmetricAlgebra
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.LineBundleClass
open scoped TensorProduct

universe u

variable (k : Type u) [Field k] [algClosed : IsAlgClosed k]
local notation "S" => Spec (CommRingCat.of k)
local notation "P" => Proj (homogeneousSubmodule k (Fin 3 → k))
local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "K[" X "]" => mk (canonicalBundle k X 2)

variable (X : Scheme.{u}) [X.Over (Spec (.of k))] [projective : X.IsProjectiveOver k]
local notation "f" => (X ↘ S)
local notation "dim₂" => topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
local notation "smooth₂" => SmoothOfRelativeDimension.smooth 2 f

variable [smoothSurface : SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [rational : Scheme.IsRationalOver (X ↘ Spec (.of k))]

include algClosed projective smoothSurface rational

namespace AlgebraicGeometry.Scheme

/-- A smooth projective rational surface over an algebraically closed field and the
projective plane have a common resolution by towers of closed point blowups. -/
theorem exists_common_pointBlowup_resolution_projectivePlane :
    ∃ (m n : ℕ) (V W : Scheme.{u}) (T : BlowupTower X m V) (U : BlowupTower P n W)
      (e : W ≅ V), IsClosedPointTower X T ∧ IsClosedPointTower P U ∧
        e.hom ≫ T.toBase ≫ f = U.toBase ≫ (P ↘ S) := by
  have : Smooth f := smooth₂
  have : IsIntegral X := rational.isIntegral_of_smooth
  obtain ⟨a, ha⟩ :=
    (isRationalOver_iff_birationalOver_symmetricAlgebra_of_smoothOfRelativeDimension f
      (d := 2) (Pi.basisFun k (Fin 3))).mp inferInstance
  obtain ⟨m, n, V, W, T, U, e, _, _, hT, hU, he, _⟩ :=
    a.exists_common_pointBlowup_resolution (k := k) ha
  exact ⟨m, n, V, W, T, U, e.symm, hT, hU, (Iso.inv_comp_eq e).mpr he.symm⟩

/-- The structure-sheaf cohomology of a smooth projective rational surface
agrees with that of the projective plane in every degree. -/
theorem nonempty_cohomologyTrivialLinearEquiv_projectivePlane_of_isRationalOver (i : ℕ) :
    Nonempty (Cohomology (InvertibleSheaf.trivial X).obj i ≃ₗ[k]
      Cohomology (InvertibleSheaf.trivial P).obj i) := by
  obtain ⟨_, _, V, W, T, U, e, hT, hU, he⟩ :=
    X.exists_common_pointBlowup_resolution_projectivePlane k
  let : V.Over S := ⟨T.toBase ≫ f⟩
  let : W.Over S := ⟨U.toBase ≫ (P ↘ S)⟩
  have : T.toBase.IsOver S := ⟨rfl⟩
  have : U.toBase.IsOver S := ⟨rfl⟩
  have : e.hom.IsOver S := ⟨he⟩
  obtain ⟨eT⟩ := hT.nonempty_cohomologyTrivialLinearEquiv k i
  obtain ⟨eU⟩ := hU.nonempty_cohomologyTrivialLinearEquiv k i
  exact ⟨eT.trans ((e.hom.cohomologyTrivialBaseLinearEquivOfIsIso k i).symm.trans eU.symm)⟩

/-- The structure sheaf of a smooth projective rational surface has no
positive-degree cohomology. -/
theorem subsingleton_cohomology_trivial_of_isRationalOver {i : ℕ} (hi : 0 < i) :
    Subsingleton (Cohomology (InvertibleSheaf.trivial X).obj i) := by
  obtain ⟨e⟩ := X.nonempty_cohomologyTrivialLinearEquiv_projectivePlane_of_isRationalOver k i
  let := subsingleton_cohomology_trivial_projectivePlane k hi
  exact e.injective.subsingleton

/-- The Picard group of a smooth projective rational surface is finitely generated. -/
theorem finite_picard_of_isRationalOver : Module.Finite ℤ (Pic(X)) := by
  have : Smooth f := smooth₂
  have : IsIntegral X := rational.isIntegral_of_smooth
  have : IsNoetherian X := isNoetherian_of_finiteType f
  have : IsNoetherian P := isNoetherian_of_finiteType (P ↘ S)
  obtain ⟨_, _, _, _, _, _, e, hT, hU, _⟩ :=
    X.exists_common_pointBlowup_resolution_projectivePlane k
  exact (finite_picard_iff_of_common_resolution k hT hU e).mpr inferInstance

/-- The Picard group of a smooth projective rational surface is free over the integers. -/
theorem free_picard_of_isRationalOver : Module.Free ℤ (Pic(X)) := by
  have : Smooth f := smooth₂
  have : IsIntegral X := rational.isIntegral_of_smooth
  have : IsNoetherian X := isNoetherian_of_finiteType f
  have : IsNoetherian P := isNoetherian_of_finiteType (P ↘ S)
  obtain ⟨_, _, _, _, _, _, e, hT, hU, _⟩ :=
    X.exists_common_pointBlowup_resolution_projectivePlane k
  exact (free_picard_iff_of_common_resolution k hT hU e).mpr inferInstance

end AlgebraicGeometry.Scheme

namespace TauCeti.AlgebraicGeometry.LineBundleClass

/-- The structure sheaf of a smooth projective rational surface has Euler characteristic one. -/
theorem eulerCharBelow_one_of_isRationalOver :
    eulerCharBelow k (1 : LineBundleClass X) 3 = 1 := by
  have h (i : ℕ) : Module.finrank k (Cohomology (InvertibleSheaf.trivial X).obj i) =
      Module.finrank k (Cohomology (InvertibleSheaf.trivial P).obj i) := by
    obtain ⟨e⟩ := X.nonempty_cohomologyTrivialLinearEquiv_projectivePlane_of_isRationalOver k i
    exact e.finrank_eq
  have hχ := eulerCharBelow_one_projectivePlane k
  rw [← mk_trivial, eulerCharBelow_mk] at hχ ⊢
  simpa only [Scheme.Modules.eulerCharBelow_succ, Scheme.Modules.eulerCharBelow_zero, h]
    using hχ

variable {X} in
/-- Riemann–Roch for any line bundle on a smooth projective rational surface over
an algebraically closed field, in the integral form `2(χ(L) - 1) = L² - L·K`. -/
theorem eulerCharBelow_eq_riemannRoch_of_isRationalOver (a : LineBundleClass X) :
    2 * (eulerCharBelow k a 3 - 1) =
      Chow.classIntersectionNumber k X a a - Chow.classIntersectionNumber k X a K[X] := by
  have : Smooth f := smooth₂
  have : IsIntegral X := rational.isIntegral_of_smooth
  obtain ⟨_, _, V, W, T, U, e, hT, hU, he⟩ :=
    X.exists_common_pointBlowup_resolution_projectivePlane k
  let : V.Over S := ⟨T.toBase ≫ f⟩
  let : W.Over S := ⟨U.toBase ≫ (P ↘ S)⟩
  have : SmoothOfRelativeDimension 2 (V ↘ S) := hT.smoothOfRelativeDimension f
  have : SmoothOfRelativeDimension 2 (W ↘ S) := hU.smoothOfRelativeDimension (P ↘ S)
  have : e.hom.IsOver S := ⟨he⟩
  have hW := (hU.forall_eulerCharBelow_eq_riemannRoch_iff k).mpr
    (fun b ↦ (eulerCharBelow_one_projectivePlane k).symm ▸
      eulerCharBelow_eq_riemannRoch_projectivePlane k b)
  have hV (b : LineBundleClass V) :=
    (eulerCharBelow_eq_riemannRoch_pullback_iff_of_isIso k e.hom b).mp (hW (pullback e.hom b))
  rw [← eulerCharBelow_one_of_isRationalOver k X]
  exact (hT.forall_eulerCharBelow_eq_riemannRoch_iff k).mp hV a

end TauCeti.AlgebraicGeometry.LineBundleClass

namespace TauCeti.AlgebraicGeometry.Chow

/-- On a smooth projective rational surface the Picard rank plus the canonical
self-intersection equals ten. -/
theorem finrank_picard_add_canonical_square_of_isRationalOver :
    (Module.finrank ℤ (Pic(X)) : ℤ) + classIntersectionNumber k X K[X] K[X] = 10 := by
  have : Smooth f := smooth₂
  have : IsIntegral X := rational.isIntegral_of_smooth
  have : Module.Finite ℤ (Pic(X)) := X.finite_picard_of_isRationalOver k
  have : Module.Free ℤ (Pic(X)) := X.free_picard_of_isRationalOver k
  obtain ⟨_, _, _, _, _, _, e, hT, hU, he⟩ :=
    X.exists_common_pointBlowup_resolution_projectivePlane k
  rw [finrank_picard_add_canonical_square_of_common_resolution k hT hU e he,
    finrank_projectivePlane, classIntersectionNumber_canonicalBundle_projectivePlane]
  norm_num

/-- The integral Picard intersection pairing of a smooth projective rational surface is
perfect. -/
theorem isPerfPair_classIntersectionBilinForm_of_isRationalOver :
    let : Smooth f := smooth₂
    let : IsIntegral X := rational.isIntegral_of_smooth
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (classIntersectionBilinForm k dim₂).IsPerfPair := by
  intro _ _ _
  obtain ⟨_, _, _, _, _, _, e, hT, hU, he⟩ :=
    X.exists_common_pointBlowup_resolution_projectivePlane k
  exact (isPerfPair_classIntersectionBilinForm_iff_of_common_resolution k hT hU e he).mpr
    (isPerfPair_classIntersectionBilinForm_projectivePlane k)

/-- The canonical class of a smooth projective rational surface is characteristic for
the integral Picard form. -/
theorem isCharacteristic_canonicalBundle_of_isRationalOver :
    let : Smooth f := smooth₂
    let : IsIntegral X := rational.isIntegral_of_smooth
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (classIntersectionBilinForm k dim₂).IsCharacteristic (Additive.ofMul K[X]) := by
  intro _ _ _
  rw [LinearMap.BilinForm.isCharacteristic_iff]
  intro a
  rw [classIntersectionBilinForm_apply, classIntersectionBilinForm_apply, toMul_ofMul,
    classIntersectionNumber_comm K[X] a.toMul]
  have h := eulerCharBelow_eq_riemannRoch_of_isRationalOver k a.toMul
  exact ⟨1 - eulerCharBelow k a.toMul 3, by omega⟩

/-- The real Picard intersection form of a smooth projective rational surface is
nondegenerate, with one positive square and all remaining squares negative. -/
theorem signature_realIntersectionBilinForm_of_isRationalOver :
    let : Smooth f := smooth₂
    let : IsIntegral X := rational.isIntegral_of_smooth
    (realIntersectionBilinForm k X).toQuadraticMap.Nondegenerate ∧
      sigPos (realIntersectionBilinForm k X).toQuadraticMap = 1 ∧
      sigNeg (realIntersectionBilinForm k X).toQuadraticMap =
        Module.finrank ℝ (ℝ ⊗[ℤ] Pic(X)) - 1 := by
  intro _ _
  obtain ⟨_, _, _, _, _, _, e, hT, hU, he⟩ :=
    X.exists_common_pointBlowup_resolution_projectivePlane k
  exact signature_realIntersectionBilinForm_of_common_resolution_projectivePlane k hT hU e he

variable {X} in
/-- The real intersection pairing of a smooth projective rational surface over an
algebraically closed field is a continuous perfect pairing. -/
theorem isContPerfPair_realIntersectionBilinForm_of_isRationalOver [Infinite k] [IsIntegral X]
    [TopologicalSpace (ℝ ⊗[ℤ] Pic(X))] [IsTopologicalAddGroup (ℝ ⊗[ℤ] Pic(X))]
    [ContinuousSMul ℝ (ℝ ⊗[ℤ] Pic(X))] [T2Space (ℝ ⊗[ℤ] Pic(X))] :
    (realIntersectionBilinForm k X).IsContPerfPair := by
  let : Module.Finite ℤ (Pic(X)) := X.finite_picard_of_isRationalOver k
  exact ((LinearMap.BilinForm.nondegenerate_toQuadraticMap_iff
    (isSymm_realIntersectionBilinForm k X)).mp
      (signature_realIntersectionBilinForm_of_isRationalOver k X).1).isContPerfPair

end TauCeti.AlgebraicGeometry.Chow

namespace AlgebraicGeometry.Scheme.Hom

variable {X} {C : Scheme.{u}} [C.Over (Spec (.of k))] [C.IsCurveOver k]

/-- Arithmetic adjunction for a closed integral curve on a smooth projective rational
surface. The curve can be singular, and its positive divisor class is the inverse
of the class of the Cartier ideal of the given immersion. -/
theorem two_mul_genus_sub_two_eq_intersection_of_isRationalOver (i : C ⟶ X)
    [IsClosedImmersion i] [i.IsOver S] :
    let : Smooth f := smooth₂
    let : IsIntegral X := rational.isIntegral_of_smooth
    let : IsRegular X := IsRegular.of_smooth f
    let hI := i.isEffectiveCartier_ker_of_isRegular_of_dim_eq_two k dim₂
      (IsCurveOver.topologicalKrullDim_eq_one k)
    let a := (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
    let B := Chow.classIntersectionNumber k X
    2 * (C.genus k : ℤ) - 2 = B a a + B a K[X] := by
  intro _ _ _ hI a B
  apply (i.two_mul_genus_sub_two_eq_intersection_iff_riemannRoch hI).mpr
  rw [eulerCharBelow_one_of_isRationalOver k X]
  exact eulerCharBelow_eq_riemannRoch_of_isRationalOver k _

end AlgebraicGeometry.Scheme.Hom
