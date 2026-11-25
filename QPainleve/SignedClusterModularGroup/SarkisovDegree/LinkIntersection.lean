/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection

/-!
# Canonical intersections across resolved elementary links

The change of anticanonical degree is computed on the two base surfaces of a
resolved elementary transformation. The selected order `m` becomes `b - m`,
where `b` is the fiber degree. The other exceptional coefficients cancel in
the comparison on the common resolution. The difference is `b - 2 * m`,
the change in the secondary degree in [Lutz, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry LineBundleClass Chow

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [IsAlgClosed k]
  {X X' Y Y' : Scheme.{u}} [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X' ↘ Spec (.of k))]
  [IsIntegral X] [IsIntegral X'] [X.IsProjectiveOver k] [X'.IsProjectiveOver k]
  {n : ℕ} {T : BlowupTower X (n + 1) Y} {U : BlowupTower X' (1 + n) Y'}

local notation "S" => Spec (CommRingCat.of k)
local notation "K[" X "]" => mk (canonicalBundle k X 2)

/-- When a resolved elementary link preserves the resolved line class and replaces
the order at stage `j` by `b - m` at the first reverse center, the anticanonical
degree of the base line class changes by `b - 2 * m`. The remaining orders keep
their relative positions. The formula includes a zero pivot order and applies
regardless of the self-intersections of the two ruling sections. -/
theorem classIntersectionNumber_canonicalBundle_sub_of_elementaryTransform
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower X' U) (e : Y ≅ Y')
    (he : e.hom ≫ U.toBase ≫ (X' ↘ S) = T.toBase ≫ (X ↘ S))
    (a : Additive (LineBundleClass X)) (a' : Additive (LineBundleClass X'))
    (x : Fin (n + 1) → ℤ) (j : Fin (n + 1)) (b : ℤ)
    (hclass : pullback e.hom
      (U.picardHom (a', Fin.append (fun _ : Fin 1 ↦ -b - x j) (x ∘ j.succAbove))).toMul =
      (T.picardHom (a, x)).toMul) :
    classIntersectionNumber k X a.toMul K[X] - classIntersectionNumber k X' a'.toMul K[X'] =
      b + 2 * x j := by
  have h := hT.classIntersectionNumber_canonicalBundle_sub_of_pullback_picardHom_eq
    k hU e he _ _ hclass
  rw [Fin.sum_univ_succAbove x j] at h
  simp only [Fin.sum_univ_add, Fin.sum_univ_one, Fin.append_left, Fin.append_right,
    Function.comp_apply] at h
  omega

end QPainleve.BlowupTower.IsClosedPointTower
