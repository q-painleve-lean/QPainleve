/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Analysis.Convex.Cone.Dual
public import QPainleve.AlgebraicGeometry.Chow.CurveCone
public import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
public import QPainleve.AlgebraicGeometry.LineBundle.EffectiveClass

import QPainleve.Analysis.Convex.Cone.Dual
import QPainleve.Topology.Algebra.Module.LocallyConvex
import QPainleve.Topology.Algebra.Module.PerfectPairing

/-!
# Duality between nef classes and curves on a surface

The real nef cone consists of classes pairing nonnegatively with every prime curve,
or equivalently with every integral effective class. A Picard isometry identifying
the integral effective-class monoids carries the real nef cones onto one another.
For a finite-dimensional real Picard space with nondegenerate intersection pairing,
the nef cone and the closed cone of curves are dual. In particular, an intersection
isometry carrying nef cones onto one another also carries the closed curve cones
onto one another.

See Gross, Hacking and Keel, [*Moduli of surfaces with an anti-canonical cycle*][GHK],
Lemma 2.15 and the proof of Theorem 1.8.

[GHK]: https://paulhacking.github.io/mlp.pdf#page=14
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry.Chow

universe u

variable (k : Type u) [Field k] [Infinite k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "V(" S ")" => (ℝ ⊗[ℤ] Additive (LineBundleClass S))
local notation "B(" S ")" => realIntersectionBilinForm k S
local notation "f" => (X ↘ Spec (CommRingCat.of k))

variable [TopologicalSpace V(X)] [IsTopologicalAddGroup V(X)] [ContinuousSMul ℝ V(X)]
  [T2Space V(X)]

variable [FiniteDimensional ℝ V(X)]

/-- The closed cone of real classes with nonnegative intersection against every prime curve. -/
def nefCone : ProperCone ℝ V(X) where
  toSubmodule := PointedCone.dual (B(X)) (Set.range (realPrimeDivisorClass k (X := X)))
  isClosed' := PointedCone.isClosed_dual fun x ↦ (B(X) x).continuous_of_finiteDimensional

/-- Membership in the real nef cone is nonnegative intersection with each prime curve. -/
theorem mem_nefCone {a : V(X)} :
    a ∈ nefCone k ↔ ∀ p : CodimensionOnePoint X, 0 ≤ B(X) a (realPrimeDivisorClass k p) := by
  -- Pass to the underlying pointed cone to use the membership rule for its dual.
  change a ∈ PointedCone.dual (B(X)) (Set.range (realPrimeDivisorClass k (X := X))) ↔ _
  simp only [PointedCone.mem_dual, Set.forall_mem_range,
    (isSymm_realIntersectionBilinForm k X).eq a]

/-- The real image of an integral line bundle class lies in the real nef cone exactly
when the line bundle class is nef. -/
@[simp]
theorem one_tmul_mem_nefCone_iff (a : LineBundleClass X) :
    ((1 : ℝ) ⊗ₜ[ℤ] Additive.ofMul a) ∈ nefCone k ↔ a.IsNef k f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  rw [mem_nefCone, isNef_iff_classIntersectionNumber_nonneg k hX]
  refine forall_congr' fun p ↦ ?_
  rw [realIntersectionBilinForm_one_tmul_realPrimeDivisorClass]
  norm_cast

section EffectiveClasses

local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "ι(" a ")" => ((1 : ℝ) ⊗ₜ[ℤ] a)

/-- A real Picard class is nef exactly when it pairs nonnegatively with every
integral effective class. -/
theorem mem_nefCone_iff_nonneg_on_effectiveClasses {x : V(X)} :
    x ∈ nefCone k ↔ ∀ a ∈ X.effectiveClasses, 0 ≤ B(X) x ι(a) := by
  let : IsNoetherian X := isNoetherian_of_finiteType f
  let : ∀ z : X, UniqueFactorizationMonoid (X.presheaf.stalk z) :=
    (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  rw [mem_nefCone]
  refine ⟨fun h a ha ↦ ?_, fun h p ↦ ?_⟩
  · obtain ⟨D, hD, rfl⟩ := Scheme.mem_effectiveClasses_iff_exists_weilDivisor.mp ha
    exact (nonneg_on_closedCurveCone_iff k (B(X) x).toContinuousLinearMap).mpr h _
      (one_tmul_weilToLineBundleClassHom_mem_closedCurveCone k hD)
  · rw [realPrimeDivisorClass_def]
    exact h _ (Scheme.primeDivisorClass_mem_effectiveClasses p)

variable [Y.Over (Spec (.of k))] [Y.IsProjectiveOver k] [IsIntegral Y]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  [TopologicalSpace V(Y)] [IsTopologicalAddGroup V(Y)] [ContinuousSMul ℝ V(Y)]
  [T2Space V(Y)] [FiniteDimensional ℝ V(Y)]

/-- A Picard isometry identifying the integral effective-class monoids carries
the real nef cones onto one another. -/
theorem image_nefCone_eq_of_map_effectiveClasses
    (e : (intersectionBilinForm k X).IsometryEquiv (intersectionBilinForm k Y))
    (he : X.effectiveClasses.map e.toLinearEquiv.toAddMonoidHom = Y.effectiveClasses) :
    (e.baseChange ℝ) '' (nefCone k (X := X) : Set V(X)) = nefCone k (X := Y) := by
  let g := e.baseChange ℝ
  have hpair (x : V(X)) (a : Pic(X)) : B(Y) (g x) ι(e a) = B(X) x ι(a) := by
    simpa only [g, realIntersectionBilinForm_def, e.baseChange_tmul] using g.map_app ι(a) x
  have hnef (x : V(X)) : g x ∈ nefCone k ↔ x ∈ nefCone k := by
    rw [mem_nefCone_iff_nonneg_on_effectiveClasses, mem_nefCone_iff_nonneg_on_effectiveClasses]
    have he' : e '' (X.effectiveClasses : Set Pic(X)) = (Y.effectiveClasses : Set Pic(Y)) :=
      congrArg SetLike.coe he
    simp only [← SetLike.mem_coe, ← he', Set.forall_mem_image, hpair]
  ext y
  obtain ⟨x, rfl⟩ := g.surjective y
  exact g.injective.mem_set_image.trans (hnef x).symm

end EffectiveClasses

variable [LinearMap.IsContPerfPair (realIntersectionBilinForm k X)]

/-- The real nef cone is the dual of the closed cone of curves under the intersection form. -/
theorem nefCone_eq_dual_closedCurveCone :
    nefCone k (X := X) = ProperCone.dual (B(X)) (closedCurveCone k (X := X) : Set V(X)) := by
  ext a
  rw [mem_nefCone, ProperCone.mem_dual]
  simpa only [LinearMap.coe_toContinuousLinearMap', SetLike.mem_coe,
    (isSymm_realIntersectionBilinForm k X).eq a] using
    (nonneg_on_closedCurveCone_iff k (LinearMap.toContinuousLinearMap (B(X) a))).symm

/-- The dual of the real nef cone is the closed cone of curves. -/
@[simp]
theorem dual_nefCone_eq_closedCurveCone :
    ProperCone.dual (B(X)) (nefCone k (X := X) : Set V(X)) = closedCurveCone k := by
  let : LocallyConvexSpace ℝ V(X) := locallyConvexSpace_of_finiteDimensional
  calc
    _ = ProperCone.dual (LinearMap.flip (B(X))) (nefCone k (X := X) : Set V(X)) := by
      ext a
      simp only [ProperCone.mem_dual, LinearMap.flip_apply,
        (isSymm_realIntersectionBilinForm k X).eq a]
    _ = closedCurveCone k := by
      rw [nefCone_eq_dual_closedCurveCone, ProperCone.dual_flip_dual]

section Transport

variable {Y : Scheme.{u}} [Y.Over (Spec (.of k))] [Y.IsProjectiveOver k] [IsIntegral Y]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  [TopologicalSpace V(Y)] [IsTopologicalAddGroup V(Y)] [ContinuousSMul ℝ V(Y)]
  [T2Space V(Y)] [FiniteDimensional ℝ V(Y)]
  [LinearMap.IsContPerfPair (realIntersectionBilinForm k Y)]

/-- An intersection isometry identifies the nef cones exactly when it identifies the closed
cones of curves. Both equalities refer to the actual image under the isometry. -/
theorem image_nefCone_eq_iff_image_closedCurveCone_eq
    (e : (B(X)).IsometryEquiv (B(Y))) :
    e '' (nefCone k (X := X) : Set V(X)) = nefCone k (X := Y) ↔
      e '' (closedCurveCone k (X := X) : Set V(X)) = closedCurveCone k (X := Y) := by
  let g := e.toLinearEquiv
  have hg (x y : V(X)) : B(Y) (g x) (g y) = B(X) x y :=
    e.map_app y x
  constructor
  · intro h
    have h' : g '' (nefCone k (X := X) : Set V(X)) = nefCone k (X := Y) := h
    have hd := ProperCone.coe_dual_image_eq_image g.toLinearMap g hg (nefCone k (X := X) : Set V(X))
    simp only [LinearEquiv.coe_coe, h', dual_nefCone_eq_closedCurveCone] at hd
    exact hd.symm
  · intro h
    have h' : g '' (closedCurveCone k (X := X) : Set V(X)) = closedCurveCone k (X := Y) := h
    have hd := ProperCone.coe_dual_image_eq_image g.toLinearMap g hg
      (closedCurveCone k (X := X) : Set V(X))
    simp only [LinearEquiv.coe_coe, h', ← nefCone_eq_dual_closedCurveCone] at hd
    exact hd.symm

/-- The image of a negative prime curve class under a nef-cone-preserving isometry
spans an extremal ray of the target closed cone of curves. -/
theorem isFaceOf_hull_singleton_image_realPrimeDivisorClass
    (e : (B(X)).IsometryEquiv (B(Y)))
    (hnef : e '' (nefCone k (X := X) : Set V(X)) = nefCone k (X := Y))
    (p : CodimensionOnePoint X)
    (hp : B(X) (realPrimeDivisorClass k p) (realPrimeDivisorClass k p) < 0) :
    (PointedCone.hull ℝ {e (realPrimeDivisorClass k p)}).IsFaceOf
      (closedCurveCone k (X := Y)).toPointedCone := by
  have hcurves := (image_nefCone_eq_iff_image_closedCurveCone_eq k e).mp hnef
  have hmap : (closedCurveCone k (X := X)).toPointedCone.map e.toLinearEquiv.toLinearMap =
      (closedCurveCone k (X := Y)).toPointedCone :=
    SetLike.coe_injective ((PointedCone.coe_map _ _).trans hcurves)
  have hB := (inferInstance : LinearMap.IsContPerfPair (B(X))).nondegenerate
  have hface := (isFaceOf_hull_singleton_realPrimeDivisorClass k hB p hp).map_equiv
    e.toLinearEquiv
  rw [hmap] at hface
  simpa only [PointedCone.hull, PointedCone.map, Submodule.map_span, Set.image_singleton,
    LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
    LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv] using hface

end Transport

end TauCeti.AlgebraicGeometry.Chow
