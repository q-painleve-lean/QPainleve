/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
public import QPainleve.AlgebraicGeometry.WeilDivisor.LinearSystem.BaseIdeal
import QPainleve.AlgebraicGeometry.Chow.ProperIntersection
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension

/-!
# Self-intersection of moving linear systems

The class of a family without fixed components is nef. Its square is nonnegative, and a
base point forces strict positivity. These bounds apply to the moving part of a linear
system and give the lower bound for the decreasing self-intersections in base-point
resolution. The proof compares the members one prime at a time using the proper
intersection formula.

## References

* [P. Hacking, *583C Lecture notes*, Proposition 7.3](https://paulhacking.github.io/surfaces.pdf#page=38).
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry.Chow

open SchemeWeilDivisor

variable (k : Type u) [Field k] [Infinite k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
  {S : Set (SchemeWeilDivisor X)} {a : LineBundleClass X}

/-- A common class of effective divisors with no fixed prime component is nef. -/
theorem isNef_of_no_fixed_components
    (hX : topologicalKrullDim X = 2) (hS : ∀ D ∈ S, 0 ≤ D)
    (hclass : ∀ D ∈ S, (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul = a)
    (hmove : ∀ p : CodimensionOnePoint X, (p : X) ∉ (baseIdeal S hS).support) :
    LineBundleClass.IsNef k (X ↘ Spec (.of k)) a := by
  refine (isNef_iff_classIntersectionNumber_nonneg k hX a).mpr fun p ↦ ?_
  obtain ⟨D, hD, hp⟩ := (notMem_support_baseIdeal_iff hS).mp (hmove p)
  rw [← hclass D hD]
  exact classIntersectionNumber_primeDivisorClass_nonneg_of_notMem_support k hX (hS D hD)
    (Finsupp.notMem_support_iff.mpr hp)

/-- A common class of a nonempty family of effective divisors with no fixed component
has nonnegative self-intersection. -/
theorem classIntersectionNumber_self_nonneg_of_no_fixed_components
    (hX : topologicalKrullDim X = 2) (hS : ∀ D ∈ S, 0 ≤ D) (hne : S.Nonempty)
    (hclass : ∀ D ∈ S, (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul = a)
    (hmove : ∀ p : CodimensionOnePoint X, (p : X) ∉ (baseIdeal S hS).support) :
    0 ≤ classIntersectionNumber k X a a := by
  have hnef := (isNef_iff_classIntersectionNumber_nonneg k hX a).mp
    (isNef_of_no_fixed_components k hX hS hclass hmove)
  obtain ⟨D, hD⟩ := hne
  rw [← hclass D hD, classIntersectionNumber_weilToLineBundleClassHom k hX, hclass D hD]
  exact Finset.sum_nonneg fun p _ ↦ mul_nonneg (hS D hD p) (hnef p)

/-- The self-intersection is positive if the family has a base point and no fixed component. -/
theorem classIntersectionNumber_self_pos_of_basePoint
    (hX : topologicalKrullDim X = 2) (hS : ∀ D ∈ S, 0 ≤ D) (hne : S.Nonempty)
    (hclass : ∀ D ∈ S, (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul = a)
    (hmove : ∀ p : CodimensionOnePoint X, (p : X) ∉ (baseIdeal S hS).support)
    {x : X} (hx : x ∈ (baseIdeal S hS).support) :
    0 < classIntersectionNumber k X a a := by
  -- Choose a component of one member through the base point.
  obtain ⟨D, hD⟩ := hne
  have hDx := (mem_support_baseIdeal_iff hS).mp hx D hD
  obtain ⟨p, hp, hpx⟩ :=
    ((D.isEffectiveCartier_idealSheaf (hS D hD)).mem_support_iff_exists_codimensionOnePoint).mp hDx
  have hpD : p ∈ D.support := Finsupp.mem_support_iff.mpr fun h ↦
    ((D.coeff_eq_zero_iff_notMem_support (hS D hD) p).mp h) hp
  -- Another member avoids the generic point of that component and still contains the base point.
  obtain ⟨E, hE, hpE⟩ := (notMem_support_baseIdeal_iff hS).mp (hmove p)
  let I := E.idealSheaf (hS E hE)
  let J := vanishingIdeal (X := X) ⟨closure {(p : X)}, isClosed_closure⟩
  have hI : I.IsEffectiveCartier := E.isEffectiveCartier_idealSheaf (hS E hE)
  have hJ : J.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  have hIJ : (I.comap J.subschemeι).IsEffectiveCartier :=
    hI.comap_subschemeι_vanishingIdeal_closure_singleton
      ((E.coeff_eq_zero_iff_notMem_support (hS E hE) p).mp hpE)
  have ha : (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ = a := by
    rw [← IsEffectiveCartier.toLineBundleClass_toCartierDivisor,
      ← toMul_ofMul hI.toCartierDivisor.toLineBundleClass,
      ← Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor,
      E.toCartierDivisor_idealSheaf, toWeilDivisor_equivCartierDivisorOfUniqueFactorizationMonoid]
    exact hclass E hE
  have hpPos : 0 < classIntersectionNumber k X a (LineBundleClass.primeDivisorClass p) := by
    rw [← ha, LineBundleClass.primeDivisorClass_def,
      classIntersectionNumber_pos_iff_support_inter_nonempty k hX.le hI hJ hIJ]
    refine ⟨x, (mem_support_baseIdeal_iff hS).mp hx E hE, ?_⟩
    simpa only [J, coe_support_vanishingIdeal, Closeds.coe_mk] using
      specializes_iff_mem_closure.mp hpx
  have hnef := isNef_of_no_fixed_components k hX hS hclass hmove
  have hnonneg :=
    classIntersectionNumber_self_nonneg_of_no_fixed_components k hX hS ⟨D, hD⟩ hclass hmove
  rw [← hclass D hD] at hnef hnonneg hpPos ⊢
  refine lt_of_le_of_ne hnonneg fun hzero ↦ hpPos.ne' ?_
  exact (classIntersectionNumber_weilToLineBundleClassHom_self_eq_zero_iff k hX
    (hS D hD) hnef).mp hzero.symm p hpD

/-- Removing the fixed divisor from a nonempty system leaves a class of nonnegative
self-intersection. This applies to linear subsystems as well as complete linear systems. -/
theorem classIntersectionNumber_movingPart_self_nonneg
    (hX : topologicalKrullDim X = 2) (hS : ∀ D ∈ S, 0 ≤ D) (hne : S.Nonempty)
    (hclass : ∀ D ∈ S, (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul = a) :
    let b := a / (Scheme.CartierDivisor.weilToLineBundleClassHom X
      (WeilDivisor.fixedPart S hne hS)).toMul
    0 ≤ classIntersectionNumber k X b b := by
  dsimp only
  refine classIntersectionNumber_self_nonneg_of_no_fixed_components k hX
    (fun _ ↦ WeilDivisor.nonneg_of_mem_movingPart hne hS)
    (WeilDivisor.movingPart_nonempty hne hS) ?_ (notMem_support_baseIdeal_movingPart hS hne)
  intro D hD
  have h := hclass _ ((WeilDivisor.mem_movingPart_iff hne hS).mp hD)
  rw [map_add, toMul_add] at h
  exact eq_div_iff_mul_eq'.mpr h

end TauCeti.AlgebraicGeometry.Chow
