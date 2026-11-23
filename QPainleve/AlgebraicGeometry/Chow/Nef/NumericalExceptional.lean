/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Effectivity

import QPainleve.AlgebraicGeometry.Chow.Ample

/-!
# Effectivity of numerical exceptional classes

On a smooth projective rational surface with an effective anticanonical divisor, an
integral class of square and canonical degree `-1` is effective exactly when it pairs
positively with an ample class. A nef anticanonical class of square zero is itself
enough to rule out effectivity of the canonical complement.

These criteria give the numerical exceptional classes used to describe the nef cone
in [Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
Lemma 2.13][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve
open TauCeti.AlgebraicGeometry.Chow
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry.LineBundleClass

variable (k : Type u) [Field k] [algClosed : IsAlgClosed k]
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [rational : Scheme.IsRationalOver (X ↘ Spec (.of k))]

local notation "f" => (X ↘ Spec (CommRingCat.of k))
local notation "K" => mk (canonicalBundle k X 2)
local notation "B" => classIntersectionNumber k X
local notation "cl" => Scheme.CartierDivisor.weilToLineBundleClassHom X

include algClosed rational

/-- In the presence of an effective anticanonical divisor, a class of square and
canonical degree `-1` is represented by an effective Weil divisor exactly when its
intersection with the given ample class is positive. -/
theorem exists_effectiveWeilDivisor_iff_classIntersectionNumber_pos_of_isAmple
    {a h : LineBundleClass X} (hh : h.IsAmple) (hsq : B a a = -1) (hcan : B a K = -1)
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier) (hK : mk hD.toInvertibleSheaf = K) :
    let : Smooth f := SmoothOfRelativeDimension.smooth 2 f
    let : IsIntegral X := rational.isIntegral_of_smooth
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (∃ E : SchemeWeilDivisor X, 0 ≤ E ∧ (cl E).toMul = a) ↔ 0 < B h a := by
  intro _ _ _ _
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  constructor
  · rintro ⟨E, hE, rfl⟩
    refine classIntersectionNumber_weilToLineBundleClassHom_pos_of_isAmple k hX hh hE ?_
    rintro rfl
    simp [classIntersectionNumber_one_right] at hsq
  · intro hpos
    have hnef : h.IsNef k f := (isNef_iff_classIntersectionNumber_nonneg k hX h).mpr
      fun p ↦ (classIntersectionNumber_primeDivisorClass_pos_of_isAmple k hX hh p).le
    have hKinv : 0 ≤ B h K⁻¹ := hK ▸
      classIntersectionNumber_nonneg_of_isNef_of_isEffectiveCartier k hX hnef hD
    have hKpair := (classIntersectionBilinForm k hX (Additive.ofMul h)).map_neg
      (Additive.ofMul K)
    simp only [classIntersectionBilinForm_apply, toMul_neg, toMul_ofMul] at hKpair
    have hneg : B h (K * a⁻¹) < 0 := by
      have he := (classIntersectionBilinForm k hX (Additive.ofMul h)).map_sub
        (Additive.ofMul K) (Additive.ofMul a)
      simp only [classIntersectionBilinForm_apply, toMul_sub, toMul_ofMul, div_eq_mul_inv] at he
      omega
    have hχ := eulerCharBelow_eq_riemannRoch_of_isRationalOver k a
    obtain ⟨I, hI, hclass⟩ :=
      exists_effectiveCartier_of_eulerCharBelow_pos_of_intersection_canonical_mul_inv_neg k
        (by omega) hnef hneg
    let E := hI.toCartierDivisor
    have : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
    refine ⟨E.toWeilDivisor, (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg E).mp
      hI.isEffective_toCartierDivisor, ?_⟩
    simpa only [E, Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor,
      toMul_ofMul, IsEffectiveCartier.toLineBundleClass_toCartierDivisor] using hclass

/-- If the anticanonical class is nef of square zero, every class of square `-1`
and anticanonical degree one is represented by an effective Cartier divisor. -/
theorem exists_effectiveCartier_of_isNef_anticanonical_of_self_eq_neg_one
    {a : LineBundleClass X} (hsq : B a a = -1) (hdeg : B K⁻¹ a = 1)
    (hnef : (K⁻¹).IsNef k f) (hzero : B K⁻¹ K⁻¹ = 0) :
    ∃ (I : X.IdealSheafData) (hI : I.IsEffectiveCartier), (mk hI.toInvertibleSheaf)⁻¹ = a := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := rational.isIntegral_of_smooth
  have := (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have hflip (x y : LineBundleClass X) : B x y⁻¹ = -B x y := by
    simpa only [classIntersectionBilinForm_apply, toMul_neg, toMul_ofMul] using
      (classIntersectionBilinForm k hX (Additive.ofMul x)).map_neg (Additive.ofMul y)
  have hcan : B a K = -1 := by
    simpa only [inv_inv, classIntersectionNumber_comm a K⁻¹, hdeg] using hflip a K⁻¹
  have hneg : B K⁻¹ (K * a⁻¹) < 0 := by
    have hK : B K⁻¹ K = 0 := by
      simpa only [inv_inv, hzero, neg_zero] using hflip K⁻¹ K⁻¹
    rw [classIntersectionNumber_mul_right k hX, hflip, hK, hdeg]
    decide
  have hχ := eulerCharBelow_eq_riemannRoch_of_isRationalOver k a
  exact exists_effectiveCartier_of_eulerCharBelow_pos_of_intersection_canonical_mul_inv_neg k
    (by omega) hnef hneg

end TauCeti.AlgebraicGeometry.LineBundleClass
