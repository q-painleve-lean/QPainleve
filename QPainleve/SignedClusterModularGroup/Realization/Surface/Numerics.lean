/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Boundary

import QPainleve.AlgebraicGeometry.Chow.Nef.Boundary
import QPainleve.LinearAlgebra.BilinearForm.Primitive

/-!
# Numerical tests for marked boundaries

For a marked surface, nefness of the reduced boundary is tested by pairing
its total class with each numbered component. When the Picard pairing is
perfect, primitivity, nefness and square zero can all be tested on
representatives in a bilinear presentation of an ambient lattice.
This lets the Picard lattice be the orthogonal complement of contracted
exceptional classes and lets the intersection computations use divisor
coefficients before quotienting by linear equivalence.
-/

public section

open AlgebraicGeometry CategoryTheory
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry

namespace QPainleve.SignedClusterModularGroup.MarkedSurface

universe u

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k] {n : ℕ} [NeZero n]
  {L : Type u} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L} {X : Scheme.{u}}
  (M : MarkedSurface k n B X) (hD : M.pair.hom.left.ker.IsEffectiveCartier)

local notation "S" => Spec (CommRingCat.of k)
local notation "δ" => (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹
local notation "d" => M.boundaryClass hD

private theorem pairing_picardMarking (x y : L) :
    B x y =
      Chow.classIntersectionNumber k M.surface (M.picardMarking x).toMul
        (M.picardMarking y).toMul := by
  let : M.surface.IsProjectiveOver k := M.projective
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  exact (M.intersectionBilinForm_picardMarking x y).symm.trans
    (Chow.intersectionBilinForm_apply k M.surface _ _)

/-- The total class of a marked boundary is nef exactly when it pairs
nonnegatively with every numbered component in the Picard marking. -/
theorem isNef_iff_nonneg_boundaryClass :
    LineBundleClass.IsNef k (M.surface ↘ S) δ ↔ ∀ j, 0 ≤ B (∑ i, d i) (d j) := by
  let : M.surface.IsProjectiveOver k := M.projective
  let : IsIntegral M.surface := M.integral
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : IsNoetherian M.surface := isNoetherian_of_finiteType (M.surface ↘ S)
  let := (M.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hpair (j : ZMod n) : B (∑ i, d i) (d j) = Chow.classIntersectionNumber k M.surface δ
      (LineBundleClass.primeDivisorClass (M.boundaryPrime hD j)) := by
    rw [M.pairing_picardMarking, M.picardMarking_sum_boundaryClass, M.picardMarking_boundaryClass,
      toMul_ofMul, toMul_ofMul]
  rw [hD.isNef_inv_mk_toInvertibleSheaf_iff
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension (M.surface ↘ S) (n := 2))]
  simp only [← M.mem_range_boundaryPrime_iff hD, Set.forall_mem_range, hpair]

/-- The total reduced boundary is primitive, nef and square zero exactly when
the sum of the numbered classes satisfies the corresponding Picard lattice tests. -/
theorem primitive_nef_square_zero_iff :
    (IsPrimitive (Additive.ofMul δ) ∧ LineBundleClass.IsNef k (M.surface ↘ S) δ ∧
      Chow.classIntersectionNumber k M.surface δ δ = 0) ↔
    IsPrimitive (∑ j, d j) ∧ (∀ j, 0 ≤ B (∑ i, d i) (d j)) ∧
      B (∑ j, d j) (∑ j, d j) = 0 := by
  have hsq := M.pairing_picardMarking (∑ j, d j) (∑ j, d j)
  rw [M.picardMarking_sum_boundaryClass, toMul_ofMul] at hsq
  rw [M.isNef_iff_nonneg_boundaryClass hD, ← hsq, ← M.picardMarking_sum_boundaryClass hD,
    M.picardMarking.isPrimitive_iff]

/-- Given an isometry into an ambient bilinear space and a surjective
bilinear presentation of that space, the target conditions for the reduced
boundary can be checked on any lifts of its numbered components. The pairing
to one uses an arbitrary vector in the presenting module. -/
theorem primitive_nef_square_zero_iff_of_isometry
    [B.IsPerfPair] {A V : Type*} [AddCommGroup A] [AddCommGroup V]
    {C : LinearMap.BilinForm ℤ A} {F : LinearMap.BilinForm ℤ V}
    (e : B →bᵢ C) (q : F →bᵢ C) (hq : Function.Surjective q)
    (a : ZMod n → V) (ha : ∀ j, q (a j) = e (d j)) :
    (IsPrimitive (Additive.ofMul δ) ∧ LineBundleClass.IsNef k (M.surface ↘ S) δ ∧
      Chow.classIntersectionNumber k M.surface δ δ = 0) ↔
    (∃ x, F (∑ j, a j) x = 1) ∧ (∀ j, 0 ≤ F (∑ i, a i) (a j)) ∧
      F (∑ j, a j) (∑ j, a j) = 0 := by
  have hsum : q (∑ j, a j) = e (∑ j, d j) := by
    simp only [map_sum, ha]
  have hprim : IsPrimitive (∑ j, d j) ↔ ∃ x, F (∑ j, a j) x = 1 := by
    rw [e.isPrimitive_iff_exists_apply_eq_one (LinearMap.IsPerfPair.bijective_right B).surjective,
      ← hsum]
    simpa only [q.map_app] using (hq.exists (p := fun y ↦ C (q (∑ j, a j)) y = 1))
  have hnef (j : ZMod n) : F (∑ i, a i) (a j) = B (∑ i, d i) (d j) := by
    rw [← q.map_app, hsum, ha, e.map_app]
  have hsq : F (∑ j, a j) (∑ j, a j) = B (∑ j, d j) (∑ j, d j) := by
    rw [← q.map_app, hsum, e.map_app]
  rw [M.primitive_nef_square_zero_iff hD, hprim]
  simp only [hnef, hsq]

end QPainleve.SignedClusterModularGroup.MarkedSurface
