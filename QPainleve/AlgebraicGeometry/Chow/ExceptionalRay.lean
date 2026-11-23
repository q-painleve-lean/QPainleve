/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.ExtremalDivisor
import QPainleve.AlgebraicGeometry.Chow.ProperIntersection

/-!
# Disjoint exceptional curves on extremal rays

Pairwise orthogonal effective classes of square and canonical degree `-1` on extremal
rays give a configuration of pairwise disjoint exceptional curves of the first kind.
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
local notation "W" => Scheme.CartierDivisor.weilToLineBundleClassHom X

variable [TopologicalSpace V(X)] [IsTopologicalAddGroup V(X)] [ContinuousSMul ℝ V(X)]

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
  choose p hp using fun j ↦ (existsUnique_exceptionalPrimeDivisor_of_effective_extremalRay k
    (hface j) (hsquare j) (hK j) (heff j)).exists
  refine ⟨p, hp, fun i j hij ↦ ?_⟩
  have hzero : B (P (p i)) (P (p j)) = 0 := by rw [(hp i).1, (hp j).1, horth hij]
  have hne : p i ≠ p j := by
    intro he
    rw [← he, (hp i).1, hsquare i] at hzero
    omega
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have hdisjoint : Disjoint (closure {(p i : X)}) (closure {(p j : X)}) := by
    refine Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp fun h ↦ ?_)
    have hpos := (classIntersectionNumber_primeDivisorClass_pos_iff k hX.le hne).mpr h
    exact (ne_of_gt hpos) hzero
  simpa only [coe_support_vanishingIdeal, Closeds.coe_mk] using hdisjoint

end TauCeti.AlgebraicGeometry.Chow
