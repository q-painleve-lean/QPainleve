/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Numerical

import Mathlib.Order.Minimal
import Mathlib.Order.Prod.Lex.Basic
import QPainleve.AlgebraicGeometry.CartierDivisor.Comparison
import QPainleve.AlgebraicGeometry.Chow.Ample
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Effectivity
import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.IdealSheaf.ClosedImmersion
import QPainleve.AlgebraicGeometry.LineBundle.Ample

/-!
# The complete linear system of a minimizing rational curve

On a minimal smooth projective rational surface, minimize the square of a
rational curve of nonnegative square and then its degree against an ample
class. Every effective Cartier divisor in the chosen class is itself a
projective line. This is the linear-system step in the classification of
minimal rational surfaces in [Vakil, Class 17, §2][Vakil].

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass17A.pdf
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry.Chow TauCeti.AlgebraicGeometry.LineBundleClass
open TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [rational : Scheme.IsRationalOver (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "dim₂" => topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
local notation "I(" p ")" => IdealSheafData.vanishingIdeal (X := X)
  (Closeds.mk (closure {(p : X)}) isClosed_closure)
local notation "cl(" h ")" =>
  (LineBundleClass.mk (IdealSheafData.IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "N(" a "," b ")" => classIntersectionNumber k X a b
local notation "K" => LineBundleClass.mk (QPainleve.canonicalBundle k X 2)
local notation "P(" p ")" => primeDivisorClass p

section LocallyFactorial

variable [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

local notation "B" => classIntersectionBilinForm k dim₂
local notation "W(" D ")" => weilToLineBundleClassHom X D

omit rational in
private theorem exists_canonical_negative_component {D : SchemeWeilDivisor X} (hD : 0 ≤ D)
    (hneg : N(K,(W(D)).toMul) < 0) :
    ∃ q : CodimensionOnePoint X, N(K,P(q)) < 0 ∧
      0 ≤ D - WeilDivisor.ofPoint q ∧
      W(D) = Additive.ofMul (P(q)) + W(D - WeilDivisor.ofPoint q) := by
  have hex : ∃ q ∈ D.support, N(K,P(q)) < 0 := by
    by_contra! h
    rw [classIntersectionNumber_weilToLineBundleClassHom k dim₂] at hneg
    exact hneg.not_ge (Finsupp.sum_nonneg fun p hp ↦ mul_nonneg (hD p) (h p hp))
  obtain ⟨q, hq, hqK⟩ := hex
  have hle : WeilDivisor.ofPoint q ≤ D := by
    have hcoeff := Finsupp.mem_support_iff.mp hq
    intro r
    rcases eq_or_ne r q with rfl | h
    · rw [← WeilDivisor.coeff, WeilDivisor.coeff_ofPoint_self]
      have hr : 0 ≤ D r := hD r
      omega
    · rw [← WeilDivisor.coeff, WeilDivisor.coeff_ofPoint_of_ne h]
      exact hD r
  have hqclass : W(WeilDivisor.ofPoint q) = Additive.ofMul (P(q)) := by
    rw [← toWeilDivisor_toCartierDivisor_vanishingIdeal_closure_singleton q,
      weilToLineBundleClassHom_toWeilDivisor, IsEffectiveCartier.toLineBundleClass_toCartierDivisor,
      primeDivisorClass_def]
  refine ⟨q, hqK, sub_nonneg.mpr hle, ?_⟩
  rw [← hqclass, ← map_add, add_sub_cancel]

private theorem canonical_negative_component_is_rational
    {a H : LineBundleClass X} (hH : H.IsAmple)
    (ha : a.IsNef k (X ↘ S))
    (hmin : ∀ I : X.IdealSheafData, ¬ I.IsExceptionalCurveOfFirstKind)
    (p : CodimensionOnePoint X) (hcan : N(P(p),K) < 0) (hadj : N(a,K * P(p)) < 0) :
    0 ≤ N(P(p),P(p)) ∧ ∃ e : I(p).subscheme ≅ projectiveLine k, e.hom.IsOver S := by
  let J := I(p)
  have hJ : J.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  have : J.subscheme.IsProjectiveOver k := .of_isClosedImmersion k J.subschemeι
  have : J.subscheme.IsCurveOver k := isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, QPainleve.topologicalKrullDim_vanishingIdeal_subscheme k dim₂ p⟩
  have hgenus : 2 * (J.subscheme.genus k : ℤ) - 2 = N(P(p),P(p)) + N(P(p),K) :=
    two_mul_genus_sub_two_eq_intersection_primeDivisorClass k p
  have hgen : J.subscheme.genus k = 0 := by
    by_contra! hn
    -- Positive genus would make the adjoint class effective by Riemann–Roch.
    -- Its negative intersection with the nef class then gives a contradiction.
    have hRR := eulerCharBelow_eq_riemannRoch_of_isRationalOver k (K * P(p))
    rw [classIntersectionNumber_mul_left k dim₂, classIntersectionNumber_mul_right k dim₂,
      classIntersectionNumber_mul_right k dim₂, classIntersectionNumber_mul_left k dim₂] at hRR
    have hχ : 0 < eulerCharBelow k (K * P(p)) 3 := by
      rw [classIntersectionNumber_comm K P(p)] at hRR
      omega
    have hdegree : N(H,K * (K * P(p))⁻¹) < 0 := by
      rw [mul_inv_rev, mul_comm K, mul_assoc, inv_mul_cancel, mul_one]
      have hpos := classIntersectionNumber_primeDivisorClass_pos_of_isAmple k dim₂ hH p
      have h := map_neg (B (Additive.ofMul H)) (Additive.ofMul (P(p)))
      have hInv : N(H,(P(p))⁻¹) = -N(H,P(p)) := by
        simpa only [← ofMul_inv, classIntersectionBilinForm_apply, toMul_ofMul] using h
      rwa [hInv, neg_lt_zero]
    obtain ⟨F, hF, hclass⟩ :=
      exists_effectiveCartier_of_eulerCharBelow_pos_of_intersection_canonical_mul_inv_neg
        k hχ hH.isNef hdegree
    exact hadj.not_ge (hclass ▸ classIntersectionNumber_nonneg_of_isNef_of_isEffectiveCartier
      k dim₂ ha hF)
  have hne : N(P(p),P(p)) ≠ -1 := by
    intro hs
    apply hmin J
    apply (hJ.isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_classIntersectionNumber
      (k := k) (dim₂).le).mpr
    exact ⟨hgen, by simpa only [primeDivisorClass_def] using hs⟩
  exact ⟨by omega, genus_eq_zero_iff_exists_iso_projectiveLine.mp hgen⟩

private theorem eq_ofPoint_of_minimal_rational_curve
    {H : LineBundleClass X} (hH : H.IsAmple)
    (hmin : ∀ I : X.IdealSheafData, ¬ I.IsExceptionalCurveOfFirstKind)
    (p : CodimensionOnePoint X)
    (hp : MinimalFor
      (fun q : CodimensionOnePoint X ↦ 0 ≤ N(P(q),P(q)) ∧
        ∃ e : I(q).subscheme ≅ projectiveLine k, e.hom.IsOver S)
      (fun q ↦ toLex (N(P(q),P(q)).toNat, N(H,P(q)).toNat)) p)
    {D : SchemeWeilDivisor X} (hD : 0 ≤ D) (hclass : (W(D)).toMul = P(p)) :
    ∃ q : CodimensionOnePoint X, D = WeilDivisor.ofPoint q ∧
      ∃ e : I(q).subscheme ≅ projectiveLine k, e.hom.IsOver S := by
  let J := I(p)
  have : J.subscheme.IsProjectiveOver k := .of_isClosedImmersion k J.subschemeι
  have : J.subscheme.IsCurveOver k := isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, QPainleve.topologicalKrullDim_vanishingIdeal_subscheme k dim₂ p⟩
  have hpgen := genus_eq_zero_iff_exists_iso_projectiveLine.mpr hp.prop.2
  have hpRR := two_mul_genus_sub_two_eq_intersection_primeDivisorClass k p
  have hneg : N(K,(W(D)).toMul) < 0 := by
    rw [hclass, classIntersectionNumber_comm K]
    have hs := hp.prop.1
    omega
  obtain ⟨q, hqK, hE, hsplit⟩ := exists_canonical_negative_component hD hneg
  have hdecomp : Additive.ofMul (P(p)) = Additive.ofMul (P(q)) + W(D - WeilDivisor.ofPoint q) := by
    rw [← hclass, ofMul_toMul, hsplit]
  -- Compare squares by intersecting the effective remainder with each nef prime class.
  have nonneg (r : CodimensionOnePoint X) (hr : 0 ≤ N(P(r),P(r))) (s : CodimensionOnePoint X) :
      0 ≤ N(P(r),P(s)) := by
    rcases eq_or_ne r s with rfl | h
    · exact hr
    · exact classIntersectionNumber_primeDivisorClass_nonneg_of_ne k dim₂ h
  have hbound (r : CodimensionOnePoint X) (hr : 0 ≤ N(P(r),P(r))) :
      N(P(r),P(q)) ≤ N(P(r),P(p)) := by
    have h := congrArg (B (Additive.ofMul (P(r)))) hdecomp
    simp only [map_add, classIntersectionBilinForm_apply, toMul_ofMul] at h
    rw [classIntersectionNumber_weilToLineBundleClassHom k dim₂] at h
    exact h ▸ le_add_of_nonneg_right
      (Finsupp.sum_nonneg fun s _ ↦ mul_nonneg (hE s) (nonneg r hr s))
  have hpq := hbound p hp.prop.1
  have hqcan : N(P(q),K) < 0 := by rwa [classIntersectionNumber_comm]
  have hqrat := canonical_negative_component_is_rational (k := k) hH
    ((isNef_iff_classIntersectionNumber_nonneg k dim₂ _).mpr (nonneg p hp.prop.1)) hmin q
    hqcan (by rw [classIntersectionNumber_mul_right k dim₂]; omega)
  refine ⟨q, ?_, hqrat.2⟩
  -- A nonzero remainder would make the component's ample degree strictly smaller.
  by_contra hne
  have hdegree := classIntersectionNumber_weilToLineBundleClassHom_pos_of_isAmple
    k dim₂ hH hE (sub_ne_zero.mpr hne)
  have hdegree' := congrArg (B (Additive.ofMul H)) hdecomp
  simp only [map_add, classIntersectionBilinForm_apply, toMul_ofMul] at hdegree'
  have hqdeg := classIntersectionNumber_primeDivisorClass_pos_of_isAmple k dim₂ hH q
  have hsq := hbound q hqrat.1
  rw [classIntersectionNumber_comm (P(q)) (P(p))] at hsq
  apply hp.not_lt hqrat
  rw [Prod.Lex.toLex_lt_toLex']
  exact ⟨by omega, fun _ ↦ by omega⟩

end LocallyFactorial

include rational in
/-- On a smooth projective rational surface without exceptional curves of the first kind,
the existence of a projective-line divisor of nonnegative square gives a divisor of
nonnegative square whose entire complete linear system consists of projective lines
over the ground field. The conclusion concerns the full Cartier divisor schemes,
including members that could a priori be reducible or nonreduced. -/
theorem exists_minimal_rational_curve_linear_system
    (hmin : ∀ I : X.IdealSheafData, ¬ I.IsExceptionalCurveOfFirstKind)
    {I : X.IdealSheafData} (hI : I.IsEffectiveCartier) (hsq : 0 ≤ N(cl(hI),cl(hI)))
    (e : I.subscheme ≅ projectiveLine k) (he : e.hom.IsOver S) :
    ∃ (C : X.IdealSheafData) (hC : C.IsEffectiveCartier), 0 ≤ N(cl(hC),cl(hC)) ∧
      ∀ (F : X.IdealSheafData) (hF : F.IsEffectiveCartier), cl(hF) = cl(hC) →
        ∃ e : F.subscheme ≅ projectiveLine k, e.hom.IsOver S := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := rational.isIntegral_of_smooth
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  have : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  obtain ⟨H, hH⟩ := X.exists_isAmple_of_isProjectiveOver k
  have hex : ∃ p : CodimensionOnePoint X, 0 ≤ N(P(p),P(p)) ∧
      ∃ e : I(p).subscheme ≅ projectiveLine k, e.hom.IsOver S := by
    have : IsIntegral I.subscheme := IsIntegral.of_isIso e.inv
    have hdim : topologicalKrullDim I.subscheme = 1 :=
      e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
        (IsCurveOver.topologicalKrullDim_eq_one (X := projectiveLine k) k)
    let p : CodimensionOnePoint X :=
      ⟨I.subschemeι (genericPoint I.subscheme),
        I.subschemeι.coheight_apply_genericPoint_eq_one_of_dim_eq_two k dim₂ hdim⟩
    have heq : I = I(p) := I.ker_subschemeι.symm.trans
      I.subschemeι.ker_eq_vanishingIdeal_closure_genericPoint
    have hclass : P(p) = cl(hI) := by
      rw [primeDivisorClass_def,
        LineBundleClass.mk_toInvertibleSheaf_congr hI _ heq]
    have he' : ∃ e : I.subscheme ≅ projectiveLine k, e.hom.IsOver S := ⟨e, he⟩
    exact ⟨p, hclass.symm ▸ hsq, heq ▸ he'⟩
  obtain ⟨p, hp⟩ := exists_minimalFor_of_wellFoundedLT _
    (fun p ↦ toLex (N(P(p),P(p)).toNat, N(H,P(p)).toNat)) hex
  let hC := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  refine ⟨I(p), hC, by simpa only [primeDivisorClass_def] using hp.prop.1, fun F hF hclass ↦ ?_⟩
  let D := hF.toCartierDivisor
  have hD := (isEffective_iff_toWeilDivisor_nonneg D).mp hF.isEffective_toCartierDivisor
  have hcl : (weilToLineBundleClassHom X D.toWeilDivisor).toMul = P(p) := by
    rw [weilToLineBundleClassHom_toWeilDivisor, toMul_ofMul,
      hF.toLineBundleClass_toCartierDivisor, hclass, primeDivisorClass_def]
  obtain ⟨q, hq, eF, heF⟩ := eq_ofPoint_of_minimal_rational_curve hH hmin p hp hD hcl
  have hFq : F = I(q) := by
    refine (hF.toCartierDivisor_eq_iff
      (isEffectiveCartier_vanishingIdeal_closure_singleton q.property)).mp ?_
    exact toWeilDivisor_injective
      (hq.trans (toWeilDivisor_toCartierDivisor_vanishingIdeal_closure_singleton q).symm)
  subst F
  exact ⟨eF, heF⟩

end AlgebraicGeometry.Scheme
