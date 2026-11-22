/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection
public import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef

/-!
# Intersection with effective divisors on surfaces

On an integral locally factorial projective surface, distinct prime divisors meet
nonnegatively. Thus nefness of an effective divisor is detected by its own components.
For a nef effective divisor, square zero is equivalent to orthogonality to every component.

## References

* O. Debarre, *Introduction to Mori Theory*, §§3.2 and 4.2.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable (k : Type u) [Field k] [Infinite k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

/-- On an integral locally factorial projective surface, nefness is equivalent to
nonnegative surface intersection with every prime divisor class. -/
public theorem isNef_iff_classIntersectionNumber_nonneg [IsLocallyNoetherian X]
    (hX : topologicalKrullDim X = 2) (a : LineBundleClass X) :
    LineBundleClass.IsNef k (X ↘ Spec (.of k)) a ↔
      ∀ p : CodimensionOnePoint X, 0 ≤
        classIntersectionNumber k X a (LineBundleClass.primeDivisorClass p) := by
  constructor
  · intro ha p
    let I := vanishingIdeal (X := X) ⟨closure {(p : X)}, isClosed_closure⟩
    have : I.subscheme.IsProjectiveOver k :=
      Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
    have : I.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
      ⟨inferInstance, inferInstance, topologicalKrullDim_vanishingIdeal_subscheme k hX p⟩
    rw [classIntersectionNumber_primeDivisorClass_eq_intersectionNumber k hX]
    exact ha.intersectionNumber_nonneg I.subschemeι (comp_over _ _).symm
  · intro ha
    refine (LineBundleClass.isNef_iff k _ a).mpr fun C _ _ i _ hi ↦ ?_
    have hC := Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := C) k
    let p : CodimensionOnePoint X :=
      ⟨i (genericPoint C), i.coheight_apply_genericPoint_eq_one_of_dim_eq_two k hX hC⟩
    have he := i.ker_eq_vanishingIdeal_closure_genericPoint
    have hp : (vanishingIdeal ⟨closure {(p : X)}, isClosed_closure⟩).IsEffectiveCartier :=
      isEffectiveCartier_vanishingIdeal_closure_singleton p.property
    have hker : i.ker.IsEffectiveCartier := he ▸ hp
    let : i.IsOver (Spec (.of k)) := ⟨hi.symm⟩
    rw [← classIntersectionNumber_eq_intersectionNumber_of_isEffectiveCartier_ker k hX.le i hC
      hker, LineBundleClass.mk_toInvertibleSheaf_congr hker hp he,
      ← LineBundleClass.primeDivisorClass_def]
    exact ha p

variable [IsNoetherian X]

/-- An effective Weil divisor is nef exactly when it intersects each component of its
support nonnegatively. -/
public theorem isNef_weilToLineBundleClassHom_iff
    (hX : topologicalKrullDim X = 2) {D : SchemeWeilDivisor X} (hD : 0 ≤ D) :
    LineBundleClass.IsNef k (X ↘ Spec (.of k))
      (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul ↔
      ∀ p ∈ D.support, 0 ≤ classIntersectionNumber k X
        (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul
        (LineBundleClass.primeDivisorClass p) := by
  rw [isNef_iff_classIntersectionNumber_nonneg k hX]
  refine ⟨fun h p _ ↦ h p, fun h p ↦ ?_⟩
  by_cases hp : p ∈ D.support
  · exact h p hp
  rw [classIntersectionNumber_comm, classIntersectionNumber_weilToLineBundleClassHom k hX]
  refine Finset.sum_nonneg fun q hq ↦ mul_nonneg (hD q) ?_
  exact classIntersectionNumber_primeDivisorClass_nonneg_of_ne k hX
    (fun he ↦ hp (he.symm ▸ hq))

/-- A nef effective Weil divisor has square zero exactly when its class is orthogonal to
each prime divisor in its support. -/
public theorem classIntersectionNumber_weilToLineBundleClassHom_self_eq_zero_iff
    (hX : topologicalKrullDim X = 2) {D : SchemeWeilDivisor X} (hD : 0 ≤ D)
    (hnef : LineBundleClass.IsNef k (X ↘ Spec (.of k))
      (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul) :
    classIntersectionNumber k X (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul
      (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul = 0 ↔
      ∀ p ∈ D.support, classIntersectionNumber k X
        (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul
        (LineBundleClass.primeDivisorClass p) = 0 := by
  rw [classIntersectionNumber_weilToLineBundleClassHom k hX _ D]
  have hnonneg := (isNef_weilToLineBundleClassHom_iff k hX hD).mp hnef
  rw [Finsupp.sum, Finset.sum_eq_zero_iff_of_nonneg fun p hp ↦ mul_nonneg (hD p) (hnonneg p hp)]
  refine forall₂_congr fun p hp ↦ ?_
  simp only [mul_eq_zero, Finsupp.mem_support_iff.mp hp, false_or]

end TauCeti.AlgebraicGeometry.Chow
