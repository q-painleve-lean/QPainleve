/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Ample

import QPainleve.AlgebraicGeometry.CartierDivisor.Comparison

/-!
# Effective divisors of ample degree one

Since an ample class has positive integral intersection with every prime divisor,
a divisor of ample degree one is the reduced closure of a codimension-one point.
-/

public section

open AlgebraicGeometry TopologicalSpace TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Chow LineBundleClass

universe u

variable (k : Type u) [Field k] [Infinite k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

namespace TauCeti.AlgebraicGeometry.Chow

/-- An effective Weil divisor with ample degree one is prime with multiplicity one. -/
theorem exists_eq_ofPoint_of_classIntersectionNumber_eq_one
    (hX : topologicalKrullDim X = 2) {a : LineBundleClass X} (ha : a.IsAmple)
    {D : SchemeWeilDivisor X} (hD : 0 ≤ D)
    (h : classIntersectionNumber k X a
      (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul = 1) :
    ∃ p, D = WeilDivisor.ofPoint p := by
  classical
  let f := (classIntersectionBilinForm k hX (Additive.ofMul a)).comp
    (Scheme.CartierDivisor.weilToLineBundleClassHom X).toIntLinearMap
  have hD₁ : f D = 1 := by
    simpa only [f, LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap,
      classIntersectionBilinForm_apply, toMul_ofMul] using h
  have hf {E : SchemeWeilDivisor X} (hE : 0 ≤ E) (hne : E ≠ 0) : 0 < f E :=
    (classIntersectionBilinForm_apply k hX _ _).symm ▸
      classIntersectionNumber_weilToLineBundleClassHom_pos_of_isAmple k hX ha hE hne
  have hne : D ≠ 0 := by
    intro he
    simp [he] at hD₁
  obtain ⟨p, hp⟩ := Finsupp.support_nonempty_iff.mpr hne
  let E := WeilDivisor.ofPoint p
  have hE : 0 ≤ E := WeilDivisor.ofPoint_nonneg p
  have hle : E ≤ D := by
    intro q
    by_cases he : q = p
    · subst q
      rw [← WeilDivisor.coeff, WeilDivisor.coeff_ofPoint_self]
      have hp₁ := Finsupp.mem_support_iff.mp hp
      have hp₂ : 0 ≤ D p := hD p
      omega
    · rw [← WeilDivisor.coeff, WeilDivisor.coeff_ofPoint_of_ne he]
      exact hD q
  refine ⟨p, sub_eq_zero.mp ?_⟩
  by_contra hne'
  have hpos := hf (sub_nonneg.mpr hle) hne'
  rw [map_sub, hD₁] at hpos
  have hfE := hf hE (fun hzero ↦ by
    have hcoeff := congrArg (fun F : SchemeWeilDivisor X ↦ WeilDivisor.coeff F p) hzero
    simp [E] at hcoeff)
  omega

end TauCeti.AlgebraicGeometry.Chow

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {I : X.IdealSheafData}

/-- An effective Cartier divisor on a locally factorial surface with ample degree one
is the reduced closure of a prime divisor. -/
theorem exists_eq_vanishingIdeal_of_classIntersectionNumber_eq_one
    (hI : I.IsEffectiveCartier)
    (hX : topologicalKrullDim X = 2) {a : LineBundleClass X} (ha : a.IsAmple)
    (h : classIntersectionNumber k X a (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ = 1) :
    ∃ p : CodimensionOnePoint X, I = vanishingIdeal ⟨closure {(p : X)}, isClosed_closure⟩ := by
  let : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let D := hI.toCartierDivisor
  have hD := (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg
    D).mp hI.isEffective_toCartierDivisor
  have hD₁ : classIntersectionNumber k X a
      (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.weilToLineBundleClassHom X
        D.toWeilDivisor).toMul = 1 := by
    rw [TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor,
      toMul_ofMul, hI.toLineBundleClass_toCartierDivisor]
    exact h
  obtain ⟨p, hp⟩ := exists_eq_ofPoint_of_classIntersectionNumber_eq_one k hX ha hD hD₁
  let hJ := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  refine ⟨p, (hI.toCartierDivisor_eq_iff hJ).mp ?_⟩
  apply TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.toWeilDivisor_injective
  exact hp.trans
    (toWeilDivisor_toCartierDivisor_vanishingIdeal_closure_singleton
      p).symm

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
