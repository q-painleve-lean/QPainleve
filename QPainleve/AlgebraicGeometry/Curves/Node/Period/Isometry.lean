/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
public import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic

import QPainleve.AlgebraicGeometry.CartierDivisor.Excision

/-!
# Picard isometries and boundary period domains

A class belongs to the boundary orthogonal exactly when its intersections with the
numbered boundary primes vanish. A Picard isometry matching the numbered primes
therefore transports the domains of the boundary period characters.
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry LineBundleClass
open AlgebraicGeometry.Scheme.IdealSheafData

universe u v w

namespace AlgebraicGeometry.Scheme.NodalCycleNumbering

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [Y.IsProjectiveOver k] [IsIntegral X] [IsIntegral Y]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  {D : X.IdealSheafData} {E : Y.IdealSheafData}
  [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  [PrestableFamily (E.subscheme ↘ Spec (.of k))]
  {n m : ℕ} [NeZero n] [NeZero m] {ι : Type v} {κ : Type w}
  {p : ι → (D.subscheme ↘ Spec (.of k)).smoothLocus}
  {q : κ → (E.subscheme ↘ Spec (.of k)).smoothLocus}

local notation "B(" X ")" => Chow.intersectionBilinForm k X
local notation "P(" D "," r ")" => Additive.ofMul (primeDivisorClass (boundaryPrimeEmbedding D r))
local notation "s(" X ")" => (X ↘ Spec (CommRingCat.of k))

/-- The numbered boundary primes suffice to test membership in the boundary orthogonal. -/
theorem mem_boundaryOrthogonal_iff (A : NodalCycleNumbering p n) (hD : D.IsEffectiveCartier)
    (x : Additive (LineBundleClass X)) :
    let : IsNoetherian X := isNoetherian_of_finiteType s(X)
    let := s(X).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    x ∈ D.boundaryOrthogonal k ↔ ∀ j, B(X) P(D, A.boundaryPrimeEquiv hD j) x = 0 := by
  intro _ _
  let r := A.boundaryPrimeEquiv hD
  have hspan := Scheme.Opens.primeDivisorSpanCompl_eq_span_of_mem_iff D.support.compl
    (D.boundaryPrimeEmbedding ∘ r) (by
      rw [EquivLike.range_comp, range_boundaryPrimeEmbedding]
      intro a
      exact not_not)
  rw [D.boundaryOrthogonal_def, hspan, LinearMap.BilinForm.orthogonal,
    Submodule.mem_orthogonalBilin_span]
  exact Set.forall_mem_range

/-- A Picard isometry matching the numbered boundary prime classes preserves membership
in the boundary orthogonal in both directions. -/
theorem isometry_mem_boundaryOrthogonal_iff (A : NodalCycleNumbering p n)
    (C : NodalCycleNumbering q m) (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
    (σ : ZMod n ≃ ZMod m) (e : B(X).IsometryEquiv B(Y)) :
    let : IsNoetherian X := isNoetherian_of_finiteType s(X)
    let : IsNoetherian Y := isNoetherian_of_finiteType s(Y)
    let := s(X).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let := s(Y).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (∀ j, e P(D, A.boundaryPrimeEquiv hD j) = P(E, C.boundaryPrimeEquiv hE (σ j))) →
    ∀ x, e x ∈ E.boundaryOrthogonal k ↔ x ∈ D.boundaryOrthogonal k := by
  intro _ _ _ _ h x
  refine (C.mem_boundaryOrthogonal_iff hE (e x)).trans
    (Iff.trans ?_ (A.mem_boundaryOrthogonal_iff hD x).symm)
  exact σ.surjective.forall.trans (forall_congr' fun j ↦ by rw [← h j, e.map_app])

/-- Matching the boundary prime classes identifies the two boundary orthogonal submodules
under the Picard isometry. -/
theorem map_boundaryOrthogonal_eq_of_isometry (A : NodalCycleNumbering p n)
    (C : NodalCycleNumbering q m) (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
    (σ : ZMod n ≃ ZMod m) (e : B(X).IsometryEquiv B(Y)) :
    let : IsNoetherian X := isNoetherian_of_finiteType s(X)
    let : IsNoetherian Y := isNoetherian_of_finiteType s(Y)
    let := s(X).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let := s(Y).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (∀ j, e P(D, A.boundaryPrimeEquiv hD j) = P(E, C.boundaryPrimeEquiv hE (σ j))) →
    (D.boundaryOrthogonal k).map e.toLinearEquiv.toLinearMap = E.boundaryOrthogonal k := by
  intro _ _ _ _ h
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  simpa only [Submodule.mem_map_equiv, ← LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv,
    LinearEquiv.symm_apply_apply] using (A.isometry_mem_boundaryOrthogonal_iff C hD hE σ e h x).symm

end AlgebraicGeometry.Scheme.NodalCycleNumbering
