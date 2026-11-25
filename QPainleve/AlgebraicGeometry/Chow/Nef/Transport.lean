/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Nef.Cone
public import QPainleve.AlgebraicGeometry.Chow.Nef.EffectiveTransport
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes
public import TauCeti.Topology.Algebra.Module.ModuleTopology

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryPrimes

/-!
# Transport of nef cones by Picard isometries

The integral effective classes test membership in the real nef cone. An
isometry carrying the effective-class monoids onto one another therefore
carries the nef cones onto one another. For root-free rational surfaces
with nef square-zero anticanonical boundaries, the nef-cone comparison
follows from matching the boundary primes. It gives the numerical input
for transporting exceptional configurations.

See [Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
Lemmas 2.13–2.15 and Theorem 1.8](https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass
open scoped TensorProduct

universe u

namespace TauCeti.AlgebraicGeometry.Chow

local notation "S(" k ")" => Spec (CommRingCat.of k)
local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "V(" X ")" => (ℝ ⊗[ℤ] Pic(X))
local notation "ι(" a ")" => ((1 : ℝ) ⊗ₜ[ℤ] a)
local notation "P" => primeDivisorClass

section Nef

variable (k : Type u) [Field k] [Infinite k] {X Y : Scheme.{u}}
  [X.Over S(k)] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ S(k))]
  [TopologicalSpace V(X)] [IsTopologicalAddGroup V(X)] [ContinuousSMul ℝ V(X)] [T2Space V(X)]
  [FiniteDimensional ℝ V(X)]

/-- A real Picard class is nef exactly when it pairs nonnegatively with every
integral effective class. -/
theorem mem_nefCone_iff_nonneg_on_effectiveClasses {x : V(X)} :
    x ∈ nefCone k ↔ ∀ a ∈ X.effectiveClasses, 0 ≤ realIntersectionBilinForm k X x ι(a) := by
  let f := X ↘ S(k)
  let : IsNoetherian X := isNoetherian_of_finiteType f
  let : ∀ z : X, UniqueFactorizationMonoid (X.presheaf.stalk z) :=
    f.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  rw [mem_nefCone]
  refine ⟨fun h a ha ↦ ?_, fun h p ↦ ?_⟩
  · obtain ⟨D, hD, rfl⟩ := Scheme.mem_effectiveClasses_iff_exists_weilDivisor.mp ha
    exact (nonneg_on_closedCurveCone_iff k
      (realIntersectionBilinForm k X x).toContinuousLinearMap).mpr h _
      (one_tmul_weilToLineBundleClassHom_mem_closedCurveCone k hD)
  · rw [realPrimeDivisorClass_def]
    exact h _ (Scheme.primeDivisorClass_mem_effectiveClasses p)

variable [Y.Over S(k)] [Y.IsProjectiveOver k] [IsIntegral Y]
  [SmoothOfRelativeDimension 2 (Y ↘ S(k))]
  [TopologicalSpace V(Y)] [IsTopologicalAddGroup V(Y)] [ContinuousSMul ℝ V(Y)] [T2Space V(Y)]
  [FiniteDimensional ℝ V(Y)]

/-- A Picard isometry identifying the integral effective-class monoids carries
the real nef cones onto one another. -/
theorem image_nefCone_eq_of_map_effectiveClasses
    (e : (intersectionBilinForm k X).IsometryEquiv (intersectionBilinForm k Y))
    (he : X.effectiveClasses.map e.toLinearEquiv.toAddMonoidHom = Y.effectiveClasses) :
    (e.baseChange ℝ) '' (nefCone k (X := X) : Set V(X)) = nefCone k (X := Y) := by
  let g := e.baseChange ℝ
  have hpair (x : V(X)) (a : Pic(X)) :
      realIntersectionBilinForm k Y (g x) ι(e a) = realIntersectionBilinForm k X x ι(a) := by
    simpa only [g, realIntersectionBilinForm_def, e.baseChange_tmul] using g.map_app ι(a) x
  have hnef (x : V(X)) : g x ∈ nefCone k ↔ x ∈ nefCone k := by
    rw [mem_nefCone_iff_nonneg_on_effectiveClasses, mem_nefCone_iff_nonneg_on_effectiveClasses]
    have he' : e '' (X.effectiveClasses : Set Pic(X)) = (Y.effectiveClasses : Set Pic(Y)) :=
      congrArg SetLike.coe he
    simp only [← SetLike.mem_coe, ← he', Set.forall_mem_image, hpair]
  ext y
  obtain ⟨x, rfl⟩ := g.surjective y
  exact g.injective.mem_set_image.trans (hnef x).symm

end Nef

section Anticanonical

variable (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
  [X.Over S(k)] [Y.Over S(k)] [X.IsProjectiveOver k] [Y.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ S(k))] [SmoothOfRelativeDimension 2 (Y ↘ S(k))]
  [hX : Scheme.IsRationalOver (X ↘ S(k))] [hY : Scheme.IsRationalOver (Y ↘ S(k))]

variable [TopologicalSpace V(X)] [IsModuleTopology ℝ V(X)]
  [TopologicalSpace V(Y)] [IsModuleTopology ℝ V(Y)]

local notation "K(" X ")" => mk (canonicalBundle k X 2)
local notation "I(" X ")" => classIntersectionNumber k X

/-- A Picard isometry matching the nonempty reduced nef square-zero anticanonical
boundaries of smooth projective rational surfaces carries their real nef cones
onto one another when neither surface has an internal `(-2)` curve. -/
theorem image_nefCone_eq_of_nef_anticanonical_isometry
    {D : X.IdealSheafData} {E : Y.IdealSheafData} [IsReduced D.subscheme] [IsReduced E.subscheme]
    [Nonempty D.boundaryPrimes] (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
    (hcanD : mk hD.toInvertibleSheaf = K(X)) (hcanE : mk hE.toInvertibleSheaf = K(Y))
    (hnefD : (K(X))⁻¹.IsNef k (X ↘ S(k))) (hnefE : (K(Y))⁻¹.IsNef k (Y ↘ S(k)))
    (hzero : I(X) (K(X))⁻¹ (K(X))⁻¹ = 0) (σ : D.boundaryPrimes ≃ E.boundaryPrimes) :
    let : Smooth (X ↘ S(k)) := SmoothOfRelativeDimension.smooth 2 _
    let : Smooth (Y ↘ S(k)) := SmoothOfRelativeDimension.smooth 2 _
    let : IsIntegral X := hX.isIntegral_of_smooth
    let : IsIntegral Y := hY.isIntegral_of_smooth
    let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S(k))
    let : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ S(k))
    let := (X ↘ S(k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let := (Y ↘ S(k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let : Module.Finite ℤ Pic(X) := X.finite_picard_of_isRationalOver k
    let : Module.Finite ℤ Pic(Y) := Y.finite_picard_of_isRationalOver k
    let : IsTopologicalAddGroup V(X) := IsModuleTopology.isTopologicalAddGroup ℝ V(X)
    let : IsTopologicalAddGroup V(Y) := IsModuleTopology.isTopologicalAddGroup ℝ V(Y)
    let : T2Space V(X) := TauCeti.ModuleTopology.t2Space (Module.Free.chooseBasis ℝ V(X))
    let : T2Space V(Y) := TauCeti.ModuleTopology.t2Space (Module.Free.chooseBasis ℝ V(Y))
    ∀ (e : (intersectionBilinForm k X).IsometryEquiv (intersectionBilinForm k Y)),
      (∀ p, e (Additive.ofMul (P (D.boundaryPrimeEmbedding p))) =
        Additive.ofMul (P (E.boundaryPrimeEmbedding (σ p)))) →
      (∀ p : CodimensionOnePoint X, Disjoint (closure {(p : X)}) D.support →
        I(X) (P p) (P p) ≠ -2) →
      (∀ p : CodimensionOnePoint Y, Disjoint (closure {(p : Y)}) E.support →
        I(Y) (P p) (P p) ≠ -2) →
      (e.baseChange ℝ) '' (nefCone k (X := X) : Set V(X)) = nefCone k (X := Y) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ e hclass hrootD hrootE
  let : Finite D.boundaryPrimes := hD.finite_boundaryPrimes
  let q := σ.toEmbedding.trans E.boundaryPrimeEmbedding
  have hp (p : CodimensionOnePoint X) :
      (p : X) ∈ D.support ↔ p ∈ Set.range D.boundaryPrimeEmbedding :=
    (Set.ext_iff.mp D.range_boundaryPrimeEmbedding p).symm
  have hq (p : CodimensionOnePoint Y) : (p : Y) ∈ E.support ↔ p ∈ Set.range q := by
    simp only [q, Function.Embedding.coe_trans, Equiv.coe_toEmbedding, EquivLike.range_comp]
    exact (Set.ext_iff.mp E.range_boundaryPrimeEmbedding p).symm
  have heff := map_effectiveClasses_of_nef_anticanonical_isometry k hD hE
    D.boundaryPrimeEmbedding q hp hq hcanD hcanE hnefD hnefE hzero e hclass hrootD hrootE
  exact image_nefCone_eq_of_map_effectiveClasses k e heff

end Anticanonical

end TauCeti.AlgebraicGeometry.Chow
