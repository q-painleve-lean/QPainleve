/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.CurveCone
public import QPainleve.AlgebraicGeometry.Chow.RationalSurface
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic

import QPainleve.AlgebraicGeometry.Chow.ProperIntersection
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Numerical
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension

/-!
# Effective classes on exceptional rays

An effective class of square `-1` that generates a face of the closed cone of curves
has a single prime component of multiplicity one. On a smooth projective rational
surface over an algebraically closed field, canonical degree `-1` identifies the
representative as an exceptional curve of the first kind. This is the recognition
step in the transport of exceptional configurations in [Gross, Hacking and Keel,
*Moduli of surfaces with an anti-canonical cycle*, proof of Theorem 1.8](https://paulhacking.github.io/mlp.pdf#page=14).
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry.Chow

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "f" => (X ↘ Spec (CommRingCat.of k))
local notation "V(" S ")" => (ℝ ⊗[ℤ] Additive (LineBundleClass S))
local notation "ι" => (fun a : LineBundleClass X ↦ (1 : ℝ) ⊗ₜ[ℤ] Additive.ofMul a)
local notation "P" => LineBundleClass.primeDivisorClass
local notation "B" => classIntersectionNumber k X
local notation "Bℝ" => realIntersectionBilinForm k X
local notation "c" => realPrimeDivisorClass k (X := X)
local notation "W" => Scheme.CartierDivisor.weilToLineBundleClassHom X

section Integral

variable [IsIntegral X] [Infinite k]

private theorem classIntersectionNumber_primeDivisorClass_neg_of_mem_hull
    {a : LineBundleClass X} (ha : B a a < 0) {p : CodimensionOnePoint X}
    (hp : c p ∈ PointedCone.hull ℝ {ι a}) :
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    B a (P p) < 0 := by
  intro _ _
  obtain ⟨r, hr, hscale⟩ := PointedCone.mem_hull_singleton.mp hp
  have hr' : 0 < r := lt_of_le_of_ne hr fun hz ↦
    realPrimeDivisorClass_ne_zero k p (by simpa only [← hz, zero_smul] using hscale.symm)
  have hpair := congrArg (Bℝ (ι a)) hscale
  simp only [map_smul, smul_eq_mul, realIntersectionBilinForm_tmul, one_mul, toMul_ofMul,
    realIntersectionBilinForm_one_tmul_realPrimeDivisorClass] at hpair
  have hself : (B a a : ℝ) < 0 := by exact_mod_cast ha
  have hneg : (B a (P p) : ℝ) < 0 := hpair ▸ mul_neg_of_pos_of_neg hr' hself
  exact_mod_cast hneg

variable [TopologicalSpace V(X)] [IsTopologicalAddGroup V(X)] [ContinuousSMul ℝ V(X)]

/-- Every effective Weil divisor representing a class of square `-1` on an extremal ray
of the closed cone of curves is a prime divisor of multiplicity one. -/
theorem exists_eq_single_of_square_eq_neg_one_of_isFaceOf
    {a : LineBundleClass X} (ha : B a a = -1)
    (hface : (PointedCone.hull ℝ {ι a}).IsFaceOf (closedCurveCone k (X := X)).toPointedCone)
    (D : SchemeWeilDivisor X) (hD : 0 ≤ D) :
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (W D).toMul = a → ∃ p : CodimensionOnePoint X, D = Finsupp.single p 1 := by
  classical
  intro _ _ hclass
  have hm (p : D.support) : 0 < D p :=
    lt_of_le_of_ne (hD p) (Finsupp.mem_support_iff.mp p.property).symm
  have hsum : ∑ p : D.support, ((D p : ℤ) : ℝ) • c p ∈ PointedCone.hull ℝ {ι a} := by
    have hclass' : W D = Additive.ofMul a := congrArg Additive.ofMul hclass
    rw [Finset.sum_coe_sort D.support (fun p ↦ (D p : ℝ) • c p)]
    have hmem : D.sum (fun p n ↦ (n : ℝ) • c p) ∈ PointedCone.hull ℝ {ι a} := by
      rw [← one_tmul_weilToLineBundleClassHom k D, hclass']
      exact Submodule.subset_span (Set.mem_singleton _)
    simpa only [Finsupp.sum] using hmem
  -- Extremality puts each prime component on the same ray.
  have hneg (p : D.support) : B a (P p) < 0 :=
    classIntersectionNumber_primeDivisorClass_neg_of_mem_hull k (ha.trans_lt (by decide))
      (hface.mem_of_sum_smul_mem (fun q : D.support ↦ realPrimeDivisorClass_mem_closedCurveCone k q)
        (fun q ↦ by exact_mod_cast (hm q).le) hsum p (by exact_mod_cast hm p))
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  -- Pairing with the class itself gives a sum of positive integers equal to one.
  have htotal : ∑ p ∈ D.support, D p * -(B a (P p)) = 1 := by
    have h := classIntersectionNumber_weilToLineBundleClassHom k hX a D
    rw [hclass, ha] at h
    simpa only [Finsupp.sum, mul_neg, Finset.sum_neg_distrib, neg_neg] using congrArg Neg.neg h.symm
  have hterm (p : CodimensionOnePoint X) (hp : p ∈ D.support) : 0 < D p * -(B a (P p)) :=
    mul_pos (hm ⟨p, hp⟩) (neg_pos.mpr (hneg ⟨p, hp⟩))
  obtain ⟨p, hp⟩ : D.support.Nonempty := by
    by_contra! hempty
    simp [hempty] at htotal
  rw [← Finset.sum_erase_add _ _ hp] at htotal
  have hrest : 0 ≤ ∑ q ∈ D.support.erase p, D q * -(B a (P q)) :=
    Finset.sum_nonneg (fun q hq ↦ (hterm q (Finset.mem_of_mem_erase hq)).le)
  have hprod : D p * -(B a (P p)) = 1 := by linarith [hterm p hp]
  have hzero : ∑ q ∈ D.support.erase p, D q * -(B a (P q)) = 0 := by linarith
  refine ⟨p, Finsupp.eq_single_iff.mpr ⟨?_, ?_⟩⟩
  · intro q hq
    by_contra hqp
    have hq' : q ∈ D.support.erase p := Finset.mem_erase.mpr ⟨by simpa using hqp, hq⟩
    exact (hterm q hq).ne' ((Finset.sum_eq_zero_iff_of_nonneg
      (fun r hr ↦ (hterm r (Finset.mem_of_mem_erase hr)).le)).mp hzero q hq')
  · rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hprod with h | h
    · exact h.1
    · linarith [hm ⟨p, hp⟩, h.1]

end Integral

variable [TopologicalSpace V(X)] [IsTopologicalAddGroup V(X)] [ContinuousSMul ℝ V(X)]

/-- An effective class of square and canonical degree `-1` generating an extremal ray
of a smooth projective rational surface over an algebraically closed field has a unique
exceptional prime representative. -/
theorem existsUnique_exceptionalCurve_of_extremal_ray [IsAlgClosed k]
    [hRat : Scheme.IsRationalOver f] {a : LineBundleClass X}
    (ha : B a a = -1) (hK : B a (LineBundleClass.mk (canonicalBundle k X 2)) = -1) :
    let : Smooth f := SmoothOfRelativeDimension.smooth 2 f
    let : IsIntegral X := hRat.isIntegral_of_smooth
    (PointedCone.hull ℝ {ι a}).IsFaceOf (closedCurveCone k (X := X)).toPointedCone →
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (∃ D : SchemeWeilDivisor X, 0 ≤ D ∧ (W D).toMul = a) →
    ∃! p : CodimensionOnePoint X, P p = a ∧
      (vanishingIdeal ⟨closure {(p : X)}, isClosed_closure⟩).IsExceptionalCurveOfFirstKind := by
  intro _ _ hface _ _ ⟨D, hD, hab⟩
  obtain ⟨p, rfl⟩ := exists_eq_single_of_square_eq_neg_one_of_isFaceOf k ha hface D hD hab
  have hp : P p = a := by
    simpa only [Scheme.CartierDivisor.weilToLineBundleClassHom_single, one_zsmul, toMul_ofMul,
      LineBundleClass.primeDivisorClass_def] using hab
  refine ⟨p, ⟨hp, ?_⟩, fun q hq ↦ ?_⟩
  · let I := vanishingIdeal (X := X) ⟨closure {(p : X)}, isClosed_closure⟩
    have hI : I.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
    have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
    have : I.subscheme.IsProjectiveOver k :=
      Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
    have : I.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
      ⟨inferInstance, inferInstance, QPainleve.topologicalKrullDim_vanishingIdeal_subscheme k hX p⟩
    have hadj := I.subschemeι.two_mul_genus_sub_two_eq_intersection_of_isRationalOver k
    dsimp only at hadj
    rw [LineBundleClass.mk_toInvertibleSheaf_congr _ hI (ker_subschemeι I)] at hadj
    have hclass : (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ = a :=
      (LineBundleClass.primeDivisorClass_def p).symm.trans hp
    rw [hclass, ha, hK] at hadj
    exact (hI.isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_classIntersectionNumber
      (k := k) hX.le).mpr ⟨by omega, hclass ▸ ha⟩
  · by_contra hqp
    have hnonneg := classIntersectionNumber_primeDivisorClass_nonneg_of_ne k
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)) hqp
    rw [hq.1, hp, ha] at hnonneg
    omega

/-- Pairwise orthogonal effective exceptional ray classes are represented by a
configuration of pairwise disjoint exceptional curves of the first kind. -/
theorem exists_pairwise_disjoint_exceptionalCurves_of_extremal_rays [IsAlgClosed k]
    [hRat : Scheme.IsRationalOver f] {J : Type*} (a : J → LineBundleClass X)
    (hsquare : ∀ j, B (a j) (a j) = -1)
    (hK : ∀ j, B (a j) (LineBundleClass.mk (canonicalBundle k X 2)) = -1)
    (horth : Pairwise (fun i j ↦ B (a i) (a j) = 0)) :
    let : Smooth f := SmoothOfRelativeDimension.smooth 2 f
    let : IsIntegral X := hRat.isIntegral_of_smooth
    (∀ j, (PointedCone.hull ℝ {ι (a j)}).IsFaceOf (closedCurveCone k (X := X)).toPointedCone) →
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (∀ j, ∃ D : SchemeWeilDivisor X, 0 ≤ D ∧ (W D).toMul = a j) →
    ∃ p : J → CodimensionOnePoint X,
      (∀ j, P (p j) = a j ∧
        (vanishingIdeal ⟨closure {(p j : X)}, isClosed_closure⟩).IsExceptionalCurveOfFirstKind) ∧
      Pairwise (fun i j ↦ Disjoint
        ((vanishingIdeal ⟨closure {(p i : X)}, isClosed_closure⟩).support : Set X)
        ((vanishingIdeal ⟨closure {(p j : X)}, isClosed_closure⟩).support : Set X)) := by
  intro _ _ hface _ _ heff
  choose p hp using fun j ↦ (existsUnique_exceptionalCurve_of_extremal_ray k
    (hsquare j) (hK j) (hface j) (heff j)).exists
  refine ⟨p, hp, fun i j hij ↦ ?_⟩
  have hzero : B (P (p i)) (P (p j)) = 0 := by rw [(hp i).1, (hp j).1, horth hij]
  have hne : p i ≠ p j := by
    intro he
    rw [← he, (hp i).1, hsquare i] at hzero
    omega
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have hi := (hp i).2.isEffectiveCartier
  have hj := (hp j).2.isEffectiveCartier
  have hproper := hi.comap_subschemeι_vanishingIdeal_closure_singleton_of_ne hne.symm
  refine Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp fun h ↦ ?_)
  have hpos := (classIntersectionNumber_pos_iff_support_inter_nonempty k hX.le hi hj hproper).mpr h
  rw [← LineBundleClass.primeDivisorClass_def, ← LineBundleClass.primeDivisorClass_def,
    hzero] at hpos
  exact (lt_irrefl (0 : ℤ)) hpos

end TauCeti.AlgebraicGeometry.Chow
