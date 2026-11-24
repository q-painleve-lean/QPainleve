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

A Picard isometry matching nonzero nef classes of nonnegative square preserves
the ample side of the positive cone, including its square-zero boundary.

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

section Isometry

variable {Y : Scheme.{u}} [Y.Over (Spec (.of k))] [Y.IsProjectiveOver k] [IsIntegral Y]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  [Scheme.IsRationalOver (Y ↘ Spec (.of k))]

local notation "Q(" Y ")" => LinearMap.BilinMap.toQuadraticMap (B(Y))

/-- A Picard isometry of smooth projective rational surfaces which sends a nef class of
nonnegative square and nonzero real image to a nef class preserves positive ample degree
for classes of nonnegative square. -/
theorem classIntersectionNumber_pos_of_nef_isometry
    (e : (intersectionBilinForm k X).IsometryEquiv (intersectionBilinForm k Y))
    {d : LineBundleClass X} {d' : LineBundleClass Y}
    (hd : d.IsNef k (X ↘ Spec (.of k))) (hd' : d'.IsNef k (Y ↘ Spec (.of k)))
    (hd₀ : ι(Additive.ofMul d) ≠ 0)
    (hdd : 0 ≤ classIntersectionNumber k X d d)
    (hdmap : e (Additive.ofMul d) = Additive.ofMul d')
    {h a : LineBundleClass X} {h' : LineBundleClass Y}
    (hh : h.IsAmple) (hh' : h'.IsAmple) (haa : 0 ≤ classIntersectionNumber k X a a)
    (hha : 0 < classIntersectionNumber k X h a) :
    0 < classIntersectionNumber k Y h' (e (Additive.ofMul a)).toMul := by
  let : Module.Finite ℤ Pic(X) := X.finite_picard_of_isRationalOver k
  let : Module.Finite ℤ Pic(Y) := Y.finite_picard_of_isRationalOver k
  let : TopologicalSpace V(X) := moduleTopology ℝ V(X)
  let : TopologicalSpace V(Y) := moduleTopology ℝ V(Y)
  let : IsModuleTopology ℝ V(X) := ⟨rfl⟩
  let : IsModuleTopology ℝ V(Y) := ⟨rfl⟩
  let : ContinuousAdd V(Y) := IsModuleTopology.toContinuousAdd ℝ V(Y)
  obtain ⟨hQ, hsig, _⟩ := signature_realIntersectionBilinForm_of_isRationalOver k X
  obtain ⟨hQ', hsig', _⟩ := signature_realIntersectionBilinForm_of_isRationalOver k Y
  have he : classIntersectionNumber k Y d' d' = classIntersectionNumber k X d d := by
    simpa only [hdmap, intersectionBilinForm_apply, toMul_ofMul] using
      e.map_app (Additive.ofMul d) (Additive.ofMul d)
  have hdd' : 0 ≤ classIntersectionNumber k Y d' d' := he ▸ hdd
  let C := connectedComponentIn {x : V(X) | 0 < Q(X) x} (ι(Additive.ofMul h))
  let C' := connectedComponentIn {x : V(Y) | 0 < Q(Y) x} (ι(Additive.ofMul h'))
  let g := e.baseChange ℝ
  have hpair (x y : V(X)) : B(Y) (g x) (g y) = B(X) x y := by
    simpa only [g, realIntersectionBilinForm_def] using (e.baseChange ℝ).map_app y x
  have hgd : g (ι(Additive.ofMul d)) = ι(Additive.ofMul d') := by
    simp only [g, LinearMap.BilinForm.IsometryEquiv.baseChange_tmul, hdmap]
  have hd'₀ : ι(Additive.ofMul d') ≠ 0 := by
    rw [← hgd, ← map_zero g]
    exact g.injective.ne hd₀
  have hmaps : Set.MapsTo g C C' := by
    dsimp only [C, C']
    rw [connectedComponentIn_pos_eq_of_isNef k hQ hsig.le hh hd hd₀ hdd,
      connectedComponentIn_pos_eq_of_isNef k hQ' hsig'.le hh' hd' hd'₀ hdd']
    intro x hx
    simp only [Set.mem_ofPred_eq, LinearMap.BilinMap.toQuadraticMap_apply] at hx ⊢
    rwa [← hgd, hpair, hpair]
  have haC : ι(Additive.ofMul a) ∈ closure C := by
    dsimp only [C]
    rw [closure_connectedComponentIn_pos_eq_of_isAmple k hQ hsig.le hh]
    simp only [Set.mem_ofPred_eq, LinearMap.BilinMap.toQuadraticMap_apply,
      realIntersectionBilinForm_tmul, one_mul, toMul_ofMul]
    exact ⟨by exact_mod_cast haa, by exact_mod_cast hha.le⟩
  have ha₀ : ι(Additive.ofMul a) ≠ 0 := fun hzero ↦ by
    have hpos : 0 < B(X) (ι(Additive.ofMul h)) (ι(Additive.ofMul a)) := by
      simpa only [realIntersectionBilinForm_tmul, one_mul, toMul_ofMul, Int.cast_pos] using hha
    simp only [hzero, map_zero, lt_self_iff_false] at hpos
  have hx : g (ι(Additive.ofMul a)) ∈ closure C' :=
    hmaps.closure (IsModuleTopology.continuous_of_linearMap g.toLinearEquiv.toLinearMap) haC
  have hp := realIntersectionBilinForm_pos_of_mem_connectedComponentIn_pos k hQ' hsig'.le hh'
    (mem_connectedComponentIn (realIntersectionBilinForm_pos_of_isAmple k hh' hh')) hx
    (fun hz ↦ ha₀ (g.injective (hz.trans (map_zero g).symm)))
  simpa only [g, LinearMap.BilinForm.IsometryEquiv.baseChange_tmul, realIntersectionBilinForm_tmul,
    one_mul, toMul_ofMul, Int.cast_pos] using hp

end Isometry

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
