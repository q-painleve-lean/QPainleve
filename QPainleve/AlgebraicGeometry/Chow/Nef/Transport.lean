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

For root-free rational surfaces with nef square-zero anticanonical boundaries,
matching the boundary primes gives an identification of the effective-class
monoids and hence of the nef cones. This gives the numerical input for
transporting exceptional configurations.

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
local notation "P" => primeDivisorClass

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
