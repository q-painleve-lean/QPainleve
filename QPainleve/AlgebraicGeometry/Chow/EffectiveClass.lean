/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.Group.Irreducible.Lemmas
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import QPainleve.AlgebraicGeometry.Chow.Ample
public import QPainleve.AlgebraicGeometry.LineBundle.EffectiveClass

import QPainleve.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension
import QPainleve.AlgebraicGeometry.WeilDivisor.Basic

/-!
# Effective classes and negative prime curves

An effective divisor meeting a prime curve negatively contains the curve. When the
divisor has the class of the curve itself, subtracting that component leaves an
effective divisor of class zero, which vanishes by intersection with an ample class.
Consequently the classes of negative prime curves are exactly the additive
irreducibles of negative square in the monoid of effective classes. This criterion
lets an isometry preserving effective classes transport the negative prime curves.

See [Sakai, *Rational surfaces associated with affine root systems and geometry
of the Painlevé equations*, §4](https://doi.org/10.1007/s002200100446) for the
effective-class condition in the definition of a Cremona isometry.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

universe u

local notation "cl" => weilToLineBundleClassHom
local notation "P" => LineBundleClass.primeDivisorClass

namespace TauCeti.AlgebraicGeometry.Chow

open _root_.AlgebraicGeometry.Scheme

section LocallyFactorial

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

variable (k : Type u) [Field k] [Infinite k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k]

local notation "I(" Z ")" => classIntersectionNumber k Z

/-- An effective Weil divisor with negative intersection against a prime curve contains
that curve with positive multiplicity. -/
theorem single_le_of_classIntersectionNumber_lt_zero
    (hX : topologicalKrullDim X = 2) {D : SchemeWeilDivisor X} (hD : 0 ≤ D)
    (p : CodimensionOnePoint X) (hneg : I(X) (P p) (cl X D).toMul < 0) :
    Finsupp.single p 1 ≤ D := by
  apply WeilDivisor.single_one_le_of_coeff_pos hD
  by_contra! hp
  have hp₀ : D p = 0 := le_antisymm hp (hD p)
  rw [classIntersectionNumber_comm] at hneg
  exact hneg.not_ge (classIntersectionNumber_primeDivisorClass_nonneg_of_notMem_support k hX hD
    (Finsupp.notMem_support_iff.mpr hp₀))

include k in
/-- The zero Picard class has only the zero effective representative on a projective surface. -/
theorem weilToLineBundleClassHom_eq_zero_iff_of_nonneg
    (hX : topologicalKrullDim X = 2) {D : SchemeWeilDivisor X} (hD : 0 ≤ D) :
    cl X D = 0 ↔ D = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ map_zero _⟩
  by_contra hne
  obtain ⟨a, ha⟩ := X.exists_isAmple_of_isProjectiveOver k
  have hpos := classIntersectionNumber_weilToLineBundleClassHom_pos_of_isAmple k hX ha hD hne
  rw [h, toMul_zero, classIntersectionNumber_one_right] at hpos
  exact hpos.false

/-- The only effective Weil divisor representing the class of a negative prime curve
is that prime divisor with multiplicity one. -/
theorem eq_single_of_weilToLineBundleClassHom_eq_of_self_neg
    (hX : topologicalKrullDim X = 2) {D : SchemeWeilDivisor X} (hD : 0 ≤ D)
    (p : CodimensionOnePoint X) (hp : I(X) (P p) (P p) < 0)
    (hclass : cl X D = Additive.ofMul (P p)) : D = Finsupp.single p 1 := by
  have hle := single_le_of_classIntersectionNumber_lt_zero k hX hD p (by simpa [hclass])
  have hzero : cl X (D - Finsupp.single p 1) = 0 := by
    rw [map_sub, hclass]
    simp only [weilToLineBundleClassHom_single, one_smul, ← LineBundleClass.primeDivisorClass_def,
      sub_self]
  exact sub_eq_zero.mp ((weilToLineBundleClassHom_eq_zero_iff_of_nonneg k hX
    (sub_nonneg.mpr hle)).mp hzero)

include k in
/-- Within the effective-class monoid, zero is the only additive unit. -/
theorem isAddUnit_effectiveClasses_iff_eq_zero
    (hX : topologicalKrullDim X = 2) (a : X.effectiveClasses) : IsAddUnit a ↔ a = 0 := by
  refine ⟨fun ha ↦ ?_, fun h ↦ h ▸ isAddUnit_zero⟩
  obtain ⟨b, hab⟩ := ha.exists_neg
  obtain ⟨D, hD, hDa⟩ := mem_effectiveClasses_iff_exists_weilDivisor.mp a.property
  obtain ⟨E, hE, hEb⟩ := mem_effectiveClasses_iff_exists_weilDivisor.mp b.property
  have hzero : cl X (D + E) = 0 := by
    rw [map_add, hDa, hEb]
    exact congrArg Subtype.val hab
  have hDE := (weilToLineBundleClassHom_eq_zero_iff_of_nonneg k hX (add_nonneg hD hE)).mp hzero
  have hD₀ : D = 0 := le_antisymm (hDE ▸ le_add_of_nonneg_right hE) hD
  apply Subtype.ext
  simpa only [hD₀, map_zero, AddSubmonoid.coe_zero] using hDa.symm

omit [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)] in
private theorem eq_zero_or_eq_zero_of_add_eq_single {D E : SchemeWeilDivisor X}
    (hD : 0 ≤ D) (hE : 0 ≤ E) {p : CodimensionOnePoint X}
    (h : D + E = Finsupp.single p 1) : D = 0 ∨ E = 0 := by
  classical
  have eq_zero (F : SchemeWeilDivisor X) (hF : 0 ≤ F) (hle : F ≤ Finsupp.single p 1)
      (hFp : F p = 0) : F = 0 := by
    refine le_antisymm (fun q ↦ ?_) hF
    rcases eq_or_ne p q with rfl | hq
    · simpa only [hFp, Finsupp.zero_apply] using le_rfl
    · simpa only [Finsupp.single_apply, ite_eq_right hq, Finsupp.zero_apply] using hle q
  have hp : D p = 0 ∨ E p = 0 := by
    have hsum : D p + E p = 1 := by simpa using DFunLike.congr_fun h p
    have hDp : 0 ≤ D p := hD p
    have hEp : 0 ≤ E p := hE p
    omega
  exact hp.imp (eq_zero D hD (h ▸ le_add_of_nonneg_right hE))
    (eq_zero E hE (h ▸ le_add_of_nonneg_left hD))

include k in
/-- Any additive irreducible effective class has a prime divisor representative. -/
theorem exists_primeDivisorClass_eq_of_addIrreducible
    (hX : topologicalKrullDim X = 2) (a : X.effectiveClasses) (ha : AddIrreducible a) :
    ∃ p : CodimensionOnePoint X, Additive.ofMul (P p) = a.val := by
  obtain ⟨D, hD, hDa⟩ := mem_effectiveClasses_iff_exists_weilDivisor.mp a.property
  have hD₀ : D ≠ 0 := by
    rintro rfl
    exact ha.ne_zero (Subtype.ext (by simpa only [map_zero, AddSubmonoid.coe_zero] using hDa.symm))
  obtain ⟨p, hp⟩ := WeilDivisor.exists_pos_coeff_of_ne_zero hD hD₀
  have hle := WeilDivisor.single_one_le_of_coeff_pos hD hp
  let S : SchemeWeilDivisor X := Finsupp.single p 1
  let b : X.effectiveClasses :=
    ⟨cl X S, mem_effectiveClasses_iff_exists_weilDivisor.mpr ⟨S, by simp [S], rfl⟩⟩
  let c : X.effectiveClasses := ⟨cl X (D - S),
    mem_effectiveClasses_iff_exists_weilDivisor.mpr ⟨_, sub_nonneg.mpr hle, rfl⟩⟩
  have habc : a = b + c := Subtype.ext (by
    simpa only [b, c, AddSubmonoid.coe_add, ← map_add, add_comm S, sub_add_cancel] using hDa.symm)
  rcases ha.isAddUnit_or_isAddUnit habc with hb | hc
  · have hb₀ : cl X S = 0 :=
      congrArg Subtype.val ((isAddUnit_effectiveClasses_iff_eq_zero k hX b).mp hb)
    have hS := (weilToLineBundleClassHom_eq_zero_iff_of_nonneg k hX (by simp [S])).mp hb₀
    simp [S] at hS
  · have hc₀ := (isAddUnit_effectiveClasses_iff_eq_zero k hX c).mp hc
    rw [hc₀, add_zero] at habc
    refine ⟨p, ?_⟩
    simpa only [b, S, weilToLineBundleClassHom_single, one_smul,
      ← LineBundleClass.primeDivisorClass_def] using congrArg Subtype.val habc.symm

/-- An effective class of negative square is additively irreducible exactly when it
has a prime representative. -/
theorem addIrreducible_iff_exists_primeDivisorClass_eq
    (hX : topologicalKrullDim X = 2) (a : X.effectiveClasses)
    (ha : I(X) a.val.toMul a.val.toMul < 0) :
    AddIrreducible a ↔ ∃ p : CodimensionOnePoint X, Additive.ofMul (P p) = a.val := by
  refine ⟨exists_primeDivisorClass_eq_of_addIrreducible k hX a, ?_⟩
  rintro ⟨p, hp⟩
  have hneg : I(X) (P p) (P p) < 0 := by simpa only [← hp, toMul_ofMul] using ha
  refine ⟨fun hu ↦ ?_, fun {b c} habc ↦ ?_⟩
  · rw [(isAddUnit_effectiveClasses_iff_eq_zero k hX a).mp hu] at ha
    exact (lt_irrefl (0 : ℤ)) (by simpa only [AddSubmonoid.coe_zero, toMul_zero,
      classIntersectionNumber_one_right] using ha)
  · obtain ⟨D, hD, hDb⟩ := mem_effectiveClasses_iff_exists_weilDivisor.mp b.property
    obtain ⟨E, hE, hEc⟩ := mem_effectiveClasses_iff_exists_weilDivisor.mp c.property
    have hclass : cl X (D + E) = Additive.ofMul (P p) := by
      rw [map_add, hDb, hEc, hp, habc, AddSubmonoid.coe_add]
    have h := eq_single_of_weilToLineBundleClassHom_eq_of_self_neg k hX (add_nonneg hD hE)
      p hneg hclass
    rcases eq_zero_or_eq_zero_of_add_eq_single hD hE h with rfl | rfl
    · exact Or.inl ((isAddUnit_effectiveClasses_iff_eq_zero k hX b).mpr
        (Subtype.ext (by simpa only [map_zero, AddSubmonoid.coe_zero] using hDb.symm)))
    · exact Or.inr ((isAddUnit_effectiveClasses_iff_eq_zero k hX c).mpr
        (Subtype.ext (by simpa only [map_zero, AddSubmonoid.coe_zero] using hEc.symm)))

variable {Y : Scheme.{u}} [Y.Over (Spec (.of k))] [Y.IsProjectiveOver k] [IsIntegral Y]
  [IsNoetherian Y] [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]

/-- An intersection isometry identifying the effective-class monoids sends each
negative prime curve class to the class of a unique negative prime curve. -/
theorem existsUnique_primeDivisorClass_eq_of_map_effectiveClasses
    (hX : topologicalKrullDim X = 2) (hY : topologicalKrullDim Y = 2)
    (e : (classIntersectionBilinForm k hX).IsometryEquiv (classIntersectionBilinForm k hY))
    (he : X.effectiveClasses.map e.toLinearEquiv.toAddEquiv.toAddMonoidHom = Y.effectiveClasses)
    (p : CodimensionOnePoint X) (hp : I(X) (P p) (P p) < 0) :
    ∃! q : CodimensionOnePoint Y, Additive.ofMul (P q) = e (Additive.ofMul (P p)) ∧
      I(Y) (P q) (P q) = I(X) (P p) (P p) := by
  let a : X.effectiveClasses :=
    ⟨Additive.ofMul (P p), primeDivisorClass_mem_effectiveClasses p⟩
  let g := (e.toLinearEquiv.toAddEquiv.addSubmonoidMap X.effectiveClasses).trans
    (AddEquiv.addSubmonoidCongr he)
  have ha : AddIrreducible a :=
    (addIrreducible_iff_exists_primeDivisorClass_eq k hX a hp).mpr ⟨p, rfl⟩
  have hg : (g a).val = e (Additive.ofMul (P p)) := by
    -- The congruence changes only the membership proof of the image class.
    exact AddEquiv.coe_addSubmonoidMap_apply e.toLinearEquiv.toAddEquiv X.effectiveClasses a
  have hsq : I(Y) (g a).val.toMul (g a).val.toMul = I(X) (P p) (P p) := by
    simpa only [hg, a, classIntersectionBilinForm_apply, toMul_ofMul] using e.map_app a.val a.val
  obtain ⟨q, hq⟩ :=
    (addIrreducible_iff_exists_primeDivisorClass_eq k hY (g a) (hsq.trans_lt hp)).mp
      (ha.map g)
  have hqq : P q = (g a).val.toMul := congrArg Additive.toMul hq
  have hqSq : I(Y) (P q) (P q) = I(X) (P p) (P p) := by rwa [hqq]
  refine ⟨q, ⟨hq.trans hg, hqSq⟩, fun r hr ↦ ?_⟩
  apply Finsupp.single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0)
  refine eq_single_of_weilToLineBundleClassHom_eq_of_self_neg k hY
    (by simp) q (hqSq.trans_lt hp) ?_
  simpa only [weilToLineBundleClassHom_single, one_smul, ← LineBundleClass.primeDivisorClass_def]
    using hr.1.trans (hq.trans hg).symm

end LocallyFactorial

variable (k : Type u) [Field k] [Infinite k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [Y.Over (Spec (.of k))] [Y.IsProjectiveOver k] [IsIntegral Y]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]

/-- An effective-class-preserving isometry of smooth projective surfaces transports
each negative prime curve to the unique target prime with its image class and square. -/
theorem existsUnique_primeDivisorClass_eq_of_intersectionBilinForm_isometry
    (e : (intersectionBilinForm k X).IsometryEquiv (intersectionBilinForm k Y))
    (he : X.effectiveClasses.map e.toLinearEquiv.toAddEquiv.toAddMonoidHom = Y.effectiveClasses)
    (p : CodimensionOnePoint X) :
    let : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
    let : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ Spec (.of k))
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y) :=
      (Y ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    classIntersectionNumber k X (P p) (P p) < 0 →
    ∃! q : CodimensionOnePoint Y, Additive.ofMul (P q) = e (Additive.ofMul (P p)) ∧
      classIntersectionNumber k Y (P q) (P q) = classIntersectionNumber k X (P p) (P p) := by
  intro _ _ _ _ hp
  let f := X ↘ Spec (CommRingCat.of k)
  let g := Y ↘ Spec (CommRingCat.of k)
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have hY := topologicalKrullDim_eq_of_smoothOfRelativeDimension g (n := 2)
  let e' : (classIntersectionBilinForm k hX).IsometryEquiv (classIntersectionBilinForm k hY) :=
    { e.toLinearEquiv with
      map_app' := fun a b ↦ by
        simpa only [classIntersectionBilinForm_apply, intersectionBilinForm_apply,
          LinearEquiv.toFun_eq_coe, LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv]
          using e.map_app b a }
  exact existsUnique_primeDivisorClass_eq_of_map_effectiveClasses k hX hY e' he p hp

end TauCeti.AlgebraicGeometry.Chow
