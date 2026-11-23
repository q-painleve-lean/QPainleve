/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.NakaiMoishezon

import QPainleve.AlgebraicGeometry.Chow.Ample
import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.LineBundle.Ample

/-!
# Ample and nef classes on rational surfaces

A nef class on a smooth projective rational surface has nonnegative square.
Tensoring an ample class with a nef class is therefore ample by Nakai–Moishezon.
The ample twists by powers of one nef class also show that any two nef classes
have nonnegative intersection.

See [Debarre, *Introduction to Mori Theory*, §4.2]
(https://perso.imj-prg.fr/wp-content/uploads/debarre-pub/M22.pdf).
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.LineBundleClass

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [rational : Scheme.IsRationalOver (X ↘ Spec (.of k))]

local notation "f" => (X ↘ Spec (CommRingCat.of k))
local notation "B" => Chow.classIntersectionNumber k X

private theorem isAmple_pow_mul_pow_of_self_pos {h a : LineBundleClass X}
    (hh : h.IsAmple) (ha : a.IsNef k f) {m n : ℕ} (hm : 0 < m)
    (hsq : 0 < B (h ^ m * a ^ n) (h ^ m * a ^ n)) :
    (h ^ m * a ^ n).IsAmple := by
  refine (isAmple_iff_self_pos_and_intersectionNumber_pos _).mpr ⟨hsq, ?_⟩
  intro C _ _ i _ hi
  have : RelativeDimensionLE 1 (C ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  rw [intersectionNumber_mul_of_isIntegral, intersectionNumber_pow_of_isIntegral,
    intersectionNumber_pow_of_isIntegral]
  exact add_pos_of_pos_of_nonneg
    (mul_pos (Int.natCast_pos.mpr hm) (hh.intersectionNumber_pos i))
    (mul_nonneg (Int.natCast_nonneg n) (ha.intersectionNumber_nonneg i hi))

/-- A nef line-bundle class on a smooth projective rational surface has nonnegative
self-intersection. -/
theorem IsNef.classIntersectionNumber_self_nonneg {a : LineBundleClass X}
    (ha : a.IsNef k f) : 0 ≤ B a a := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := rational.isIntegral_of_smooth
  obtain ⟨h, hh⟩ := X.exists_isAmple_of_isProjectiveOver k
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have (x : X) : UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two x
  have hab := ha.classIntersectionNumber_nonneg_of_isAmple hX hh
  have hhh := Chow.classIntersectionNumber_pos_of_isAmple k hX hh hh
  by_contra! hneg
  let c := -B a a
  let b := B a h
  have hc : 0 < c := neg_pos.mpr hneg
  -- The twist is just past the orthogonal direction: its intersection with `a` is `-c`,
  -- while its square is still positive.
  let m := (2 * c).toNat
  let n := (2 * b + 1).toNat
  have hm : (m : ℤ) = 2 * c := Int.toNat_of_nonneg (by omega)
  have hn : (n : ℤ) = 2 * b + 1 := Int.toNat_of_nonneg (by omega)
  have hm' : 0 < m := by omega
  have hsq : 0 < B (h ^ m * a ^ n) (h ^ m * a ^ n) := by
    simp only [Chow.classIntersectionNumber_mul_left k hX,
      Chow.classIntersectionNumber_mul_right k hX, Chow.classIntersectionNumber_pow_left k hX,
      Chow.classIntersectionNumber_pow_right k hX, hm, hn, Chow.classIntersectionNumber_comm h a]
    have hca : 1 ≤ c * B h h := by
      exact Int.add_one_le_iff.mpr (mul_pos hc hhh)
    have hpos : 0 < 4 * (c * B h h) + 4 * b ^ 2 - 1 := by nlinarith [sq_nonneg b]
    calc
      0 < c * (4 * (c * B h h) + 4 * b ^ 2 - 1) := mul_pos hc hpos
      _ = _ := by dsimp [b, c]; ring
  have htest := ha.classIntersectionNumber_nonneg_of_isAmple hX
    (isAmple_pow_mul_pow_of_self_pos hh ha hm' hsq)
  have hpair : B a (h ^ m * a ^ n) = -c := by
    simp only [Chow.classIntersectionNumber_mul_right k hX,
      Chow.classIntersectionNumber_pow_right k hX, hm, hn]
    dsimp [b, c]
    ring
  omega

/-- Tensoring an ample line-bundle class with a nef class on a smooth projective
rational surface preserves ampleness. -/
theorem IsAmple.mul_of_isNef {h a : LineBundleClass X} (hh : h.IsAmple)
    (ha : a.IsNef k f) : (h * a).IsAmple := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := rational.isIntegral_of_smooth
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have (x : X) : UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two x
  have hhh := Chow.classIntersectionNumber_pos_of_isAmple k hX hh hh
  have hmix := ha.classIntersectionNumber_nonneg_of_isAmple hX hh
  have hself := ha.classIntersectionNumber_self_nonneg
  suffices hsq : 0 < B (h * a) (h * a) by
    simpa only [pow_one] using
      isAmple_pow_mul_pow_of_self_pos hh ha (m := 1) (n := 1) Nat.one_pos (by simpa using hsq)
  rw [Chow.classIntersectionNumber_mul_left k hX, Chow.classIntersectionNumber_mul_right k hX,
    Chow.classIntersectionNumber_mul_right k hX, Chow.classIntersectionNumber_comm h a]
  omega

/-- Two nef line-bundle classes on a smooth projective rational surface have nonnegative
intersection. -/
theorem IsNef.classIntersectionNumber_nonneg {a b : LineBundleClass X}
    (ha : a.IsNef k f) (hb : b.IsNef k f) : 0 ≤ B a b := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := rational.isIntegral_of_smooth
  obtain ⟨h, hh⟩ := X.exists_isAmple_of_isProjectiveOver k
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have (x : X) : UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two x
  have hample (n : ℕ) : (h * b ^ n).IsAmple := by
    induction n with
    | zero => simpa using hh
    | succ n ih => simpa only [pow_succ, ← mul_assoc] using ih.mul_of_isNef hb
  by_contra! hneg
  -- A negative intersection would eventually make the intersection with an ample twist negative.
  obtain ⟨n, hn⟩ := exists_nat_gt (B a h)
  have hnonneg := ha.classIntersectionNumber_nonneg_of_isAmple hX (hample n)
  rw [Chow.classIntersectionNumber_mul_right k hX,
    Chow.classIntersectionNumber_pow_right k hX] at hnonneg
  have hbound : (n : ℤ) * B a b ≤ (n : ℤ) * (-1) :=
    mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg n)
  omega

end TauCeti.AlgebraicGeometry.LineBundleClass
