/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Coordinates
public import QPainleve.Algebra.Cluster.Word.LoopComparison.Basic
public import QPainleve.SignedClusterModularGroup.Realization.Presentation
public import QPainleve.SignedClusterModularGroup.Realization.Relations.RayOrders
public import QPainleve.SignedClusterModularGroup.Realization.Relations.SurvivingOffsets

import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.SignedClusterModularGroup.Realization.Relations.Reference

/-!
# Signed loop comparison from a toric ray table

The input lists primitive ray coordinates in cyclic order from boundary component
zero, together with the ray offset of every ordered center and the set of offsets
that survive a nodal contraction. The center offsets determine the exchange
matrix. The surviving offsets determine the determinant orders used in the
tropical boundary search. An integer kernel calculation supplies the Casimir
basis, so the decision procedure uses only these discrete inputs and the words.
-/

public section

open AlgebraicGeometry CategoryTheory Module Quiver
open QPainleve.CharacterTorus QPainleve.Cluster
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

local notation "seed[" ray "," center "]" => SkewExchangeMatrix.ofChargeCoordinates (ray ∘ center)

/-- Compare the inversion signs, transported integral kernel columns, and forward boundary
labels of two loops using the primitive ray coordinates and the offsets of the centers and
surviving rays. The ray table is ordered cyclically from the ray of component zero. -/
def compareSignedLoopsOfRayCoordinates {m n r : ℕ} [NeZero n]
    (ray : Fin m → Fin 2 → ℤ) (centerRay : Fin r → Fin m)
    (survivors : Finset (Fin m)) (hcard : survivors.card = n)
    (w v : Word (seed[ray,centerRay]) (seed[ray,centerRay])) : Bool :=
  (seed[ray,centerRay]).compareSignedLoops
    (boundaryOrderTable (ray ∘ centerRay) ray survivors hcard) w v

namespace CompleteToricPresentation

open GeometricRealization (Point)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "cartier[" M "]" => MarkedSurface.isEffectiveCartier_boundaryIdeal M
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  (Q : CompleteToricPresentation i b r L γ)
  {c₀ : Point Centers[r]} {M₀ : MarkedSurface ℂ n B XTor[r]}

local instance instNonemptyCoordinateRelationCones : Nonempty Q.fan.cones :=
  Q.complete.nonempty_cones
local instance instNeZeroCoordinateRelationLength : NeZero Q.length := Q.neZero
local instance instPrestableCoordinateRelationBoundary :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "raysFromOrigin" =>
  Q.fan.rayEquivOfNodalCycleNumbering Q.regular (Q.cycle.rotate Q.origin)
local notation "rayAt" => Q.fan.rayFinEquivOfNodalCycleNumbering Q.regular Q.cycle Q.origin
local notation "fiber[" M "," c "]" =>
  ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c] M

/-- For a certified ray table of a reference nodal contraction of a primitive nef
square-zero anticanonical cycle, the three integer invariants computed from the ray table
decide equality of signed loop pullbacks over any field. Only the rays of centers and
surviving boundary primes need certified coordinates. -/
theorem compareSignedLoopsOfRayCoordinates_eq_true_iff
    (k : Type*) [Field k]
    (p₀ : fiber[M₀,c₀]) (hnodal₀ : p₀.IsNodalContraction)
    (hprim : IsPrimitive (Additive.ofMul classOf(cartier[M₀])))
    (hnef : (classOf(cartier[M₀])).IsNef ℂ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface classOf(cartier[M₀])
      classOf(cartier[M₀]) = 0)
    (ray : Fin Q.length → Fin 2 → ℤ) (centerRay : Fin r → Fin Q.length)
    (survivors : Finset (Fin Q.length)) (hcard : survivors.card = n)
    (hray : ∀ j, j ∈ survivors ∨ j ∈ Set.range centerRay →
      ray j = b.repr (rayAt j).primitiveGenerator)
    (hcenter : ∀ j, rayAt (centerRay j) = Q.rays j)
    (hkeep : ∀ j ∈ survivors, rayAt j ∈ Set.range (p₀.numberedBoundaryRays cartier[M₀]))
    (w v : Word (seed[ray,centerRay]) (seed[ray,centerRay])) :
    compareSignedLoopsOfRayCoordinates ray centerRay survivors hcard w v = true ↔
      w.xPullback k = v.xPullback k := by
  have hcharge (j : Fin r) : (ray ∘ centerRay) j = b.repr (Q.rays j).primitiveGenerator := by
    rw [Function.comp_apply, hray _ (Or.inr (Set.mem_range_self j)), hcenter j]
  have hE : (seed[ray,centerRay]).matrix =
      chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays) := by
    simpa only [Fan.rayChargeMap_single, funext hcharge] using
      SkewExchangeMatrix.ofChargeCoordinates_matrix_eq_chargeExchangeMatrix b
        (Fan.rayChargeMap Q.rays)
  have hord := p₀.boundaryOrderTable_eq (Φ := Q.fan) cartier[M₀] survivors hcard hkeep
    (ray ∘ centerRay) ray hcharge (fun j hj ↦ hray j (Or.inl hj))
  obtain ⟨β, hβ⟩ := (seed[ray,centerRay]).matrix.exists_basis_eq_intKernelBasisVectors
  simp only [compareSignedLoopsOfRayCoordinates, SkewExchangeMatrix.compareSignedLoops_eq_true_iff,
    hord, ← hβ]
  exact (Q.xPullback_eq_iff_signedLoopInvariants_eq_of_nodal_contraction k p₀ hnodal₀ hE
    hprim hnef hsq w v β).symm

/-- Decide equality of signed-loop pullbacks by integer computation on the supplied ray table.
The reference contraction and its certificates justify the answer. -/
def decidableXPullbackEqOfRayCoordinates
    (k : Type*) [Field k]
    (p₀ : fiber[M₀,c₀]) (hnodal₀ : p₀.IsNodalContraction)
    (hprim : IsPrimitive (Additive.ofMul classOf(cartier[M₀])))
    (hnef : (classOf(cartier[M₀])).IsNef ℂ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface classOf(cartier[M₀])
      classOf(cartier[M₀]) = 0)
    (ray : Fin Q.length → Fin 2 → ℤ) (centerRay : Fin r → Fin Q.length)
    (survivors : Finset (Fin Q.length)) (hcard : survivors.card = n)
    (hray : ∀ j, j ∈ survivors ∨ j ∈ Set.range centerRay →
      ray j = b.repr (rayAt j).primitiveGenerator)
    (hcenter : ∀ j, rayAt (centerRay j) = Q.rays j)
    (hkeep : ∀ j ∈ survivors, rayAt j ∈ Set.range (p₀.numberedBoundaryRays cartier[M₀]))
    (w v : Word (seed[ray,centerRay]) (seed[ray,centerRay])) :
    Decidable (w.xPullback k = v.xPullback k) :=
  decidable_of_iff _ (Q.compareSignedLoopsOfRayCoordinates_eq_true_iff k p₀ hnodal₀
    hprim hnef hsq ray centerRay survivors hcard hray hcenter hkeep w v)

/-- The integer coefficients of a pulled-back ample class determine the surviving offsets
for the ray-coordinate checker. Its answer then decides equality of the two X pullbacks. -/
theorem compareSignedLoopsOfRayCoordinates_eq_true_iff_of_polarization
    (k : Type*) [Field k]
    (p₀ : fiber[M₀,c₀]) (hnodal₀ : p₀.IsNodalContraction)
    (hprim : IsPrimitive (Additive.ofMul classOf(cartier[M₀])))
    (hnef : (classOf(cartier[M₀])).IsNef ℂ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface classOf(cartier[M₀])
      classOf(cartier[M₀]) = 0)
    {H : LineBundleClass M₀.surface} (hH : H.IsAmple)
    (ray : Fin Q.length → Fin 2 → ℤ) (centerRay : Fin r → Fin Q.length)
    (selfIntersection toricCoeff : ZMod Q.length → ℤ) (exceptionalCoeff : Fin r → ℤ)
    (hself : ∀ j, selfIntersection j = Q.fan.rayBoundarySelfIntersection Q.regular
      (raysFromOrigin j))
    (hcoords : (Q.fan.rayDivisorToPicard Q.regular (toricCoeff ∘ (raysFromOrigin).symm),
        exceptionalCoeff) = Q.inclusion (M₀.picardMarking.symm (Additive.ofMul H)))
    (hcenter : ∀ j, rayAt (centerRay j) = Q.rays j) :
    let survivors := survivingRayOffsets selfIntersection toricCoeff
      ((ZMod.finEquiv Q.length) ∘ centerRay) exceptionalCoeff
    (∀ j, j ∈ survivors ∨ j ∈ Set.range centerRay →
      ray j = b.repr (rayAt j).primitiveGenerator) →
    ∀ (w v : Word (seed[ray,centerRay]) (seed[ray,centerRay])),
      ∃ hcard : survivors.card = n,
        compareSignedLoopsOfRayCoordinates ray centerRay survivors hcard w v = true ↔
          w.xPullback k = v.xPullback k := by
  intro survivors hray w v
  let : Q.fan.algebraicRealization.IsProjectiveOver ℂ :=
    Q.fan.isProjectiveOver_algebraicRealization_of_isComplete Q.regular Q.complete b
  have hcenter' (j : Fin r) : raysFromOrigin ((ZMod.finEquiv Q.length ∘ centerRay) j) =
      Q.rays j := by
    simpa only [Fan.rayFinEquivOfNodalCycleNumbering_apply, Function.comp_apply] using hcenter j
  have hs : survivors = Finset.univ.map (p₀.numberedBoundaryRayOffsets hnodal₀.cartier) :=
    p₀.survivingRayOffsets_eq_map_numberedBoundaryRayOffsets (Φ := Q.fan) hnodal₀ Q.complete hH
      selfIntersection toricCoeff _ exceptionalCoeff hself hcenter' hcoords
  have hcard : survivors.card = n := by
    rw [hs, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hkeep j (hj : j ∈ survivors) : rayAt j ∈ Set.range
      (p₀.numberedBoundaryRays cartier[M₀]) := by
    rw [hs, ← Finset.mem_coe, Finset.coe_map, Finset.coe_univ, Set.image_univ] at hj
    exact (p₀.mem_range_numberedBoundaryRayOffsets_iff hnodal₀.cartier j).mp hj
  exact ⟨hcard, Q.compareSignedLoopsOfRayCoordinates_eq_true_iff k p₀ hnodal₀
    hprim hnef hsq ray centerRay survivors hcard hray hcenter hkeep w v⟩

end CompleteToricPresentation

end QPainleve.SignedClusterModularGroup
