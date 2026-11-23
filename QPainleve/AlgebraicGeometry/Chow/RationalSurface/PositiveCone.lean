/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.CurveCone
public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Effectivity

import QPainleve.Topology.Algebra.Module.RationalDensity
import TauCeti.Topology.Algebra.QuadraticForm.Continuity

/-!
# The positive component in the closed curve cone of a rational surface

The closure of the positive component selected by an ample class is contained
in the closed curve cone. In an integral Picard basis the points with rational
coordinates are dense. Clearing denominators reduces their membership to
effectivity of sufficiently high integral powers.

This is the positive-cone inclusion in [Gross, Hacking and Keel, Lemma 2.14][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Filter TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass
open scoped TensorProduct

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable (k : Type u) [Field k] [IsAlgClosed k]
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [Scheme.IsRationalOver (X ↘ Spec (.of k))]

local notation "Pic(" Y ")" => Additive (LineBundleClass Y)
local notation "V(" Y ")" => (ℝ ⊗[ℤ] Pic(Y))
local notation "B(" Y ")" => realIntersectionBilinForm k Y
local notation "ι(" a ")" => ((1 : ℝ) ⊗ₜ[ℤ] a)

variable [TopologicalSpace V(X)] [IsTopologicalAddGroup V(X)] [ContinuousSMul ℝ V(X)] [T2Space V(X)]

omit [T2Space V(X)] in
private theorem one_tmul_mem_closedCurveCone_of_positive_square (a : LineBundleClass X)
    {h : LineBundleClass X} (hh : h.IsAmple)
    (haa : 0 < classIntersectionNumber k X a a)
    (hha : 0 < classIntersectionNumber k X h a) :
    ι(Additive.ofMul a) ∈ closedCurveCone k (X := X) := by
  obtain ⟨n, hn, I, hI, hclass⟩ :=
    (eventually_exists_effectiveCartier_pow_of_positive_cone k a hh haa hha).exists
  have hc := one_tmul_inv_mk_toInvertibleSheaf_mem_closedCurveCone k hI
  simp only [hclass, ofMul_pow, ← Nat.cast_smul_eq_nsmul ℤ, TensorProduct.tmul_smul,
    ← Int.cast_smul_eq_zsmul ℝ, Int.cast_natCast] at hc
  have hm : 0 < (n : ℝ) := by exact_mod_cast hn
  exact ((closedCurveCone k).toPointedCone.smul_mem_iff hm).mp hc

/-- The closed curve cone of a smooth projective rational surface contains the closure
of the positive-square classes pairing positively with a chosen ample class. -/
theorem closure_positive_component_subset_closedCurveCone (h : LineBundleClass X)
    (hh : h.IsAmple) :
    closure {x : V(X) | 0 < B(X) x x ∧ 0 < B(X) (ι(Additive.ofMul h)) x} ⊆
      (closedCurveCone k (X := X) : Set V(X)) := by
  let : Module.Free ℤ Pic(X) := X.free_picard_of_isRationalOver k
  let : Module.Finite ℤ Pic(X) := X.finite_picard_of_isRationalOver k
  let : IsModuleTopology ℝ V(X) := isModuleTopologyOfFiniteDimensional
  let U : Set V(X) := {x | 0 < B(X) x x ∧ 0 < B(X) (ι(Additive.ofMul h)) x}
  have hsquare : Continuous (fun x : V(X) ↦ B(X) x x) :=
    (LinearMap.BilinMap.toQuadraticMap (B(X))).continuous
  have hdegree : Continuous (B(X) (ι(Additive.ofMul h))) :=
    (B(X) (ι(Additive.ofMul h))).continuous_of_finiteDimensional
  have hU : IsOpen U := (isOpen_lt continuous_const hsquare).inter
    (isOpen_lt continuous_const hdegree)
  have hd := (Module.finBasis ℤ Pic(X)).dense_setOf_exists_pos_natCast_smul_eq_one_tmul
  apply (closedCurveCone k (X := X)).isClosed.closure_subset_iff.mpr
  intro x hx
  refine closure_minimal ?_ (closedCurveCone k (X := X)).isClosed
    (hd.open_subset_closure_inter hU hx)
  rintro q ⟨hq, ⟨n, hn, a', eq⟩⟩
  have hm : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpos : ι(a') ∈ U := by
    rw [← eq]
    obtain ⟨hr₁, hr₂⟩ := hq
    exact ⟨by simpa only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right] using
        mul_pos hm (mul_pos hm hr₁),
      by simpa only [LinearMap.BilinForm.smul_right] using mul_pos hm hr₂⟩
  obtain ⟨ha₁, ha₂⟩ := hpos
  have haCone : ι(a') ∈ closedCurveCone k (X := X) := by
    apply one_tmul_mem_closedCurveCone_of_positive_square k a'.toMul hh
    · simpa only [realIntersectionBilinForm_tmul, one_mul, Int.cast_pos] using ha₁
    · simpa only [realIntersectionBilinForm_tmul, one_mul, toMul_ofMul, Int.cast_pos] using ha₂
  rw [← eq] at haCone
  exact (closedCurveCone k).toPointedCone.smul_mem_iff hm |>.mp haCone

end TauCeti.AlgebraicGeometry.Chow
