/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef
public import QPainleve.AlgebraicGeometry.LineBundle.EffectiveClass

import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Chow.Ample
import QPainleve.AlgebraicGeometry.Chow.NegativeCurve
import QPainleve.AlgebraicGeometry.Chow.Nef.NumericalExceptional
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.PositiveCone
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Numerical
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension

/-!
# Effective classes for nef square-zero anticanonical boundaries

A Picard isometry matching the components of reduced nef square-zero anticanonical
divisors on smooth projective rational surfaces preserves the effective classes
when neither surface has an internal `(-2)` curve. The total boundary selects the
ample component of the positive cone. Riemann–Roch then gives effective
representatives for the images of the nonnegative-square prime classes.
Negative curves off the boundary are exceptional curves of the first kind.

The curve classification and positive-cone argument use Gross, Hacking and Keel,
[*Moduli of surfaces with an anti-canonical cycle*, Lemmas 2.13–2.15][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry LineBundleClass
open scoped TensorProduct

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [Y.IsProjectiveOver k] [IsIntegral X] [IsIntegral Y]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  [Scheme.IsRationalOver (X ↘ Spec (.of k))] [Scheme.IsRationalOver (Y ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "B(" X ")" => classIntersectionNumber k X
local notation "Bℤ(" X ")" => intersectionBilinForm k X
local notation "Bℝ(" X ")" => realIntersectionBilinForm k X
local notation "K(" X ")" => mk (canonicalBundle k X 2)
local notation "ι(" a ")" => ((1 : ℝ) ⊗ₜ[ℤ] Additive.ofMul a)
local notation "P" => primeDivisorClass
local notation "cl(" X ")" => Scheme.CartierDivisor.weilToLineBundleClassHom X

variable (e : LinearMap.BilinForm.IsometryEquiv (intersectionBilinForm k X)
  (intersectionBilinForm k Y))

omit [Scheme.IsRationalOver (X ↘ S)] [Scheme.IsRationalOver (Y ↘ S)] in
private theorem intersection_map (a b : LineBundleClass X) :
    B(Y) (e (Additive.ofMul a)).toMul (e (Additive.ofMul b)).toMul = B(X) a b := by
  simpa only [intersectionBilinForm_apply, toMul_ofMul] using
    e.map_app (Additive.ofMul b) (Additive.ofMul a)

private theorem effective_class_of_cartier {I : Y.IdealSheafData} (hI : I.IsEffectiveCartier) :
    Additive.ofMul (mk hI.toInvertibleSheaf)⁻¹ ∈ Y.effectiveClasses := by
  exact Scheme.mem_effectiveClasses.mpr
    ⟨hI.toCartierDivisor, hI.isEffective_toCartierDivisor,
      by rw [hI.toLineBundleClass_toCartierDivisor]⟩

section Divisors

variable [IsNoetherian X] [IsNoetherian Y]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]

variable {ι : Type*} [Finite ι] [Nonempty ι]
  {D : X.IdealSheafData} {E : Y.IdealSheafData} [IsReduced D.subscheme] [IsReduced E.subscheme]
  (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
  (p : ι ↪ CodimensionOnePoint X) (q : ι ↪ CodimensionOnePoint Y)
  (hp : ∀ x : CodimensionOnePoint X, (x : X) ∈ D.support ↔ x ∈ Set.range p)
  (hq : ∀ y : CodimensionOnePoint Y, (y : Y) ∈ E.support ↔ y ∈ Set.range q)
  (hclass : ∀ i, e (Additive.ofMul (P (p i))) = Additive.ofMul (P (q i)))

omit [Scheme.IsRationalOver (X ↘ S)] [Scheme.IsRationalOver (Y ↘ S)] [Nonempty ι] in
include hD hE p q hp hq hclass in
private theorem map_anticanonical
    (hK : mk hD.toInvertibleSheaf = K(X)) (hK' : mk hE.toInvertibleSheaf = K(Y)) :
    e (Additive.ofMul (K(X))⁻¹) = Additive.ofMul (K(Y))⁻¹ := by
  let : Fintype ι := Fintype.ofFinite ι
  rw [← hK, ← hK', hD.ofMul_inv_toInvertibleSheaf_eq_sum_primeDivisorClass p hp,
    hE.ofMul_inv_toInvertibleSheaf_eq_sum_primeDivisorClass q hq, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ hclass i

omit [Scheme.IsRationalOver (X ↘ Spec (.of k))] in
include hD p hp in
private theorem one_tmul_anticanonical_ne_zero (hK : mk hD.toInvertibleSheaf = K(X))
    {h : LineBundleClass X} (hh : h.IsAmple) : ι((K(X))⁻¹) ≠ 0 := by
  let : Fintype ι := Fintype.ofFinite ι
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have hs : 0 < Bℝ(X) (ι(h)) (ι((K(X))⁻¹)) := by
    rw [← hK, hD.ofMul_inv_toInvertibleSheaf_eq_sum_primeDivisorClass p hp,
      TensorProduct.tmul_sum, map_sum]
    exact Finset.sum_pos (fun i _ ↦ by
      simpa using classIntersectionNumber_primeDivisorClass_pos_of_isAmple k hX hh (p i))
      Finset.univ_nonempty
  exact fun hz ↦ by simp only [hz, map_zero, lt_self_iff_false] at hs

omit [IsReduced E.subscheme] in
private theorem effective_image_of_prime_of_self_nonneg
    (hK' : mk hE.toInvertibleSheaf = K(Y))
    (hd : (K(X))⁻¹.IsNef k (X ↘ S)) (hd' : (K(Y))⁻¹.IsNef k (Y ↘ S))
    (hd₀ : ι((K(X))⁻¹) ≠ 0)
    (hdd : 0 ≤ B(X) (K(X))⁻¹ (K(X))⁻¹)
    (hdmap : e (Additive.ofMul (K(X))⁻¹) = Additive.ofMul (K(Y))⁻¹)
    (r : CodimensionOnePoint X) (hr : 0 ≤ B(X) (P r) (P r)) :
    e (Additive.ofMul (P r)) ∈ Y.effectiveClasses := by
  let a := (e (Additive.ofMul (P r))).toMul
  obtain ⟨h, hh⟩ := X.exists_isAmple_of_isProjectiveOver k
  obtain ⟨h', hh'⟩ := Y.exists_isAmple_of_isProjectiveOver k
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have hY := topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y ↘ S) (n := 2)
  have hpos : 0 < B(Y) h' a :=
    classIntersectionNumber_pos_of_nef_isometry k e hd hd' hd₀ hdd hdmap
      hh hh' hr (classIntersectionNumber_primeDivisorClass_pos_of_isAmple k hX hh r)
  have ha : 0 ≤ B(Y) a a := (intersection_map k e (P r) (P r)).symm ▸ hr
  have hdeg : 0 ≤ B(Y) (K(Y))⁻¹ a := by
    have h := intersection_map k e (K(X))⁻¹ (P r)
    rw [hdmap, toMul_ofMul] at h
    rw [h]
    exact (isNef_iff_classIntersectionNumber_nonneg k hX _).mp hd r
  have hflip (x y : LineBundleClass Y) : B(Y) x y⁻¹ = -B(Y) x y := by
    simpa only [intersectionBilinForm_apply, toMul_neg, toMul_ofMul] using
      (Bℤ(Y) (Additive.ofMul x)).map_neg (Additive.ofMul y)
  have hKdeg : B(Y) a K(Y) ≤ 0 := by
    have h := hflip a (K(Y))⁻¹
    rw [inv_inv, classIntersectionNumber_comm a (K(Y))⁻¹] at h
    exact h.trans_le (neg_nonpos.mpr hdeg)
  have hχ := eulerCharBelow_eq_riemannRoch_of_isRationalOver k a
  have hnef : h'.IsNef k (Y ↘ S) :=
    (isNef_iff_classIntersectionNumber_nonneg k hY h').mpr
      fun p ↦ (classIntersectionNumber_primeDivisorClass_pos_of_isAmple k hY hh' p).le
  have hKpos : 0 ≤ B(Y) h' (K(Y))⁻¹ := hK' ▸
    classIntersectionNumber_nonneg_of_isNef_of_isEffectiveCartier k hY hnef hE
  have hKneg : B(Y) h' K(Y) ≤ 0 := by
    simpa only [← hflip, inv_inv] using neg_nonpos.mpr hKpos
  have hneg : B(Y) h' (K(Y) * a⁻¹) < 0 := by
    rw [classIntersectionNumber_mul_right k hY, hflip]
    omega
  obtain ⟨I, hI, hIa⟩ :=
    exists_effectiveCartier_of_eulerCharBelow_pos_of_intersection_canonical_mul_inv_neg k
      (by omega) hnef hneg
  simpa only [hIa, a, ofMul_toMul] using effective_class_of_cartier hI

omit [IsReduced D.subscheme] [AlgebraicGeometry.IsNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] in
private theorem effective_image_of_negative_prime_off_boundary
    (hK : mk hD.toInvertibleSheaf = K(X))
    (hd' : (K(Y))⁻¹.IsNef k (Y ↘ S)) (hdd' : B(Y) (K(Y))⁻¹ (K(Y))⁻¹ = 0)
    (hdmap : e (Additive.ofMul (K(X))⁻¹) = Additive.ofMul (K(Y))⁻¹)
    (hroot : ∀ r : CodimensionOnePoint X,
      Disjoint (closure {(r : X)}) D.support → B(X) (P r) (P r) ≠ -2)
    (r : CodimensionOnePoint X) (hr : B(X) (P r) (P r) < 0) (hrD : (r : X) ∉ D.support) :
    e (Additive.ofMul (P r)) ∈ Y.effectiveClasses := by
  let I := vanishingIdeal (X := X) ⟨closure {(r : X)}, isClosed_closure⟩
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have : I.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
  have : I.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, topologicalKrullDim_vanishingIdeal_subscheme k hX r⟩
  have hI : I.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton r.property
  have hrI : I.subschemeι (genericPoint I.subscheme) ∉ D.support := by
    simpa only [I, subschemeι_genericPoint_vanishingIdeal_closure_singleton] using hrD
  have hP : (mk hI.toInvertibleSheaf)⁻¹ = P r := (primeDivisorClass_def r).symm
  have hneg := hI.classIntersectionNumber_self_neg_iff_of_anticanonical hD hK hrI
  dsimp only at hneg
  rw [hP, hK] at hneg
  obtain ⟨hexc, hdeg⟩ | ⟨_, hsq, hdis⟩ := hneg.mp hr
  · have hs : B(X) (P r) (P r) = -1 := hP ▸
      ((hI.isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_classIntersectionNumber
        (k := k) hX.le).mp hexc).2
    let a := (e (Additive.ofMul (P r))).toMul
    have hs' : B(Y) a a = -1 := (intersection_map k e (P r) (P r)).trans hs
    have hdeg' : B(Y) (K(Y))⁻¹ a = 1 := by
      simpa only [hdmap, a, toMul_ofMul] using
        (intersection_map k e (K(X))⁻¹ (P r)).trans hdeg
    obtain ⟨J, hJ, hJa⟩ :=
      exists_effectiveCartier_of_isNef_anticanonical_of_self_eq_neg_one k hs' hdeg' hd' hdd'
    simpa only [hJa, a, ofMul_toMul] using effective_class_of_cartier hJ
  · exact (hroot r (by simpa only [I, coe_support_vanishingIdeal, Closeds.coe_mk] using hdis)
      hsq).elim

include hD hE p q hp hq hclass in
private theorem mapsTo_effective_of_nef_anticanonical_isometry
    (hK : mk hD.toInvertibleSheaf = K(X)) (hK' : mk hE.toInvertibleSheaf = K(Y))
    (hd : (K(X))⁻¹.IsNef k (X ↘ S)) (hd' : (K(Y))⁻¹.IsNef k (Y ↘ S))
    (hdd : B(X) (K(X))⁻¹ (K(X))⁻¹ = 0)
    (hroot : ∀ r : CodimensionOnePoint X,
      Disjoint (closure {(r : X)}) D.support → B(X) (P r) (P r) ≠ -2) :
    Set.MapsTo e (X.effectiveClasses : Set Pic(X)) (Y.effectiveClasses : Set Pic(Y)) := by
  obtain ⟨h, hh⟩ := X.exists_isAmple_of_isProjectiveOver k
  have hdmap := map_anticanonical k e hD hE p q hp hq hclass hK hK'
  have hdd' : B(Y) (K(Y))⁻¹ (K(Y))⁻¹ = 0 := by
    simpa only [hdmap, toMul_ofMul, hdd] using intersection_map k e (K(X))⁻¹ (K(X))⁻¹
  have hprime (r : CodimensionOnePoint X) : e (Additive.ofMul (P r)) ∈ Y.effectiveClasses := by
    by_cases hrD : (r : X) ∈ D.support
    · obtain ⟨i, rfl⟩ := (hp r).mp hrD
      rw [hclass i]
      exact Scheme.primeDivisorClass_mem_effectiveClasses (q i)
    by_cases hr : 0 ≤ B(X) (P r) (P r)
    · exact effective_image_of_prime_of_self_nonneg k e hE hK' hd hd'
        (one_tmul_anticanonical_ne_zero k hD p hp hK hh) hdd.ge hdmap r hr
    · exact effective_image_of_negative_prime_off_boundary k e hD hK hd' hdd' hdmap
        hroot r (lt_of_not_ge hr) hrD
  intro a ha
  obtain ⟨A, hA, rfl⟩ := Scheme.mem_effectiveClasses_iff_exists_weilDivisor.mp ha
  classical
  have heq : e (cl(X) A) = A.sum (fun r m ↦ m • e (Additive.ofMul (P r))) := by
    calc
      _ = e (cl(X) (A.sum Finsupp.single)) := by rw [Finsupp.sum_single]
      _ = _ := by
        rw [map_finsuppSum, map_finsuppSum]
        simp only [Scheme.CartierDivisor.weilToLineBundleClassHom_single,
          ← primeDivisorClass_def, map_zsmul]
  rw [heq, Finsupp.sum]
  refine Y.effectiveClasses.sum_mem fun r _ ↦ ?_
  have hcoeff : ((A r).toNat : ℤ) = A r := Int.toNat_of_nonneg (hA r)
  rw [← hcoeff, natCast_zsmul]
  exact Y.effectiveClasses.nsmul_mem (hprime r) (A r).toNat

end Divisors

section Transport

variable {F G : Scheme.{u}} [F.Over (Spec (.of k))] [G.Over (Spec (.of k))]
  [F.IsProjectiveOver k] [G.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (F ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (G ↘ Spec (.of k))]
  [hF : Scheme.IsRationalOver (F ↘ Spec (.of k))]
  [hG : Scheme.IsRationalOver (G ↘ Spec (.of k))]

/-- A Picard isometry matching the components of reduced nef square-zero anticanonical
divisors identifies the effective-class monoids if both surfaces have no internal
`(-2)` curves. The correspondence on components also transports the total boundary class. -/
theorem map_effectiveClasses_of_nef_anticanonical_isometry
    {ι : Type*} [Finite ι] [Nonempty ι]
    {D : F.IdealSheafData} {E : G.IdealSheafData} [IsReduced D.subscheme] [IsReduced E.subscheme]
    (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
    (p : ι ↪ CodimensionOnePoint F) (q : ι ↪ CodimensionOnePoint G)
    (hp : ∀ x : CodimensionOnePoint F, (x : F) ∈ D.support ↔ x ∈ Set.range p)
    (hq : ∀ y : CodimensionOnePoint G, (y : G) ∈ E.support ↔ y ∈ Set.range q)
    (hK : mk hD.toInvertibleSheaf = K(F)) (hK' : mk hE.toInvertibleSheaf = K(G))
    (hd : (K(F))⁻¹.IsNef k (F ↘ S)) (hd' : (K(G))⁻¹.IsNef k (G ↘ S))
    (hdd : B(F) (K(F))⁻¹ (K(F))⁻¹ = 0) :
    let : Smooth (F ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : Smooth (G ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : IsIntegral F := hF.isIntegral_of_smooth
    let : IsIntegral G := hG.isIntegral_of_smooth
    let : IsNoetherian F := isNoetherian_of_finiteType (F ↘ S)
    let : IsNoetherian G := isNoetherian_of_finiteType (G ↘ S)
    let : ∀ x : F, UniqueFactorizationMonoid (F.presheaf.stalk x) :=
      (F ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let : ∀ y : G, UniqueFactorizationMonoid (G.presheaf.stalk y) :=
      (G ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    ∀ (e : (Bℤ(F)).IsometryEquiv (Bℤ(G))),
      (∀ i, e (Additive.ofMul (P (p i))) = Additive.ofMul (P (q i))) →
      (∀ r : CodimensionOnePoint F, Disjoint (closure {(r : F)}) D.support →
        B(F) (P r) (P r) ≠ -2) →
      (∀ r : CodimensionOnePoint G, Disjoint (closure {(r : G)}) E.support →
        B(G) (P r) (P r) ≠ -2) →
      F.effectiveClasses.map e.toLinearEquiv.toAddMonoidHom = G.effectiveClasses := by
  intro _ _ _ _ _ _ _ _ e hclass hroot hroot'
  have hdmap := map_anticanonical k e hD hE p q hp hq hclass hK hK'
  have hdd' : B(G) (K(G))⁻¹ (K(G))⁻¹ = 0 := by
    simpa only [hdmap, toMul_ofMul, hdd] using intersection_map k e (K(F))⁻¹ (K(F))⁻¹
  have hforward := mapsTo_effective_of_nef_anticanonical_isometry k e hD hE p q hp hq hclass
    hK hK' hd hd' hdd hroot
  have hback := mapsTo_effective_of_nef_anticanonical_isometry k e.symm hE hD q p hq hp
    (fun i ↦ (congrArg e.symm (hclass i).symm).trans (e.symm_apply_apply _))
    hK' hK hd' hd hdd' hroot'
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hforward hb
  · intro ha
    exact ⟨e.symm a, hback ha, e.apply_symm_apply a⟩

end Transport
end TauCeti.AlgebraicGeometry.Chow
