/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.LineBundle.Ample
public import QPainleve.Geometry.Toric.Fan.Picard.Boundary.Degree
public import QPainleve.SignedClusterModularGroup.Realization.NumberedRays

import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Polarization
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective

/-!
# Computing the offsets of surviving boundary rays

To form a boundary order table for signed loop comparison, first select the rays
whose strict boundary primes survive the given nodal contraction. An ample
class on the contracted surface supplies an integer test for this selection.
In the ordered toric coordinates of its pullback, a strict prime's degree is
the toric degree plus the exceptional coefficients at the internal centers on
that ray. The toric degree uses just the component and its two neighbours.
-/

public section

open AlgebraicGeometry CategoryTheory Module Multiplicative
open QPainleve.BlowupTower TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup

/-- Compute the offsets of surviving boundary rays using the toric divisor and total
exceptional coefficients of a pulled back polarization. The input arrays are indexed
cyclically starting at the ray of component zero on the contracted surface. -/
def survivingRayOffsets {m : ℕ} [NeZero m] {ι : Type*} [Fintype ι]
    (selfIntersection toricCoeff : ZMod m → ℤ) (centerRay : ι → Fin m)
    (exceptionalCoeff : ι → ℤ) : Finset (Fin m) :=
  Finset.univ.filter fun k ↦
    0 < strictBoundaryRayDegree selfIntersection toricCoeff centerRay exceptionalCoeff k

/-- A ray offset is selected precisely when its integer degree is positive. -/
@[simp]
theorem mem_survivingRayOffsets {m : ℕ} [NeZero m] {ι : Type*} [Fintype ι]
    (selfIntersection toricCoeff : ZMod m → ℤ) (centerRay : ι → Fin m)
    (exceptionalCoeff : ι → ℤ) (k : Fin m) :
    k ∈ survivingRayOffsets selfIntersection toricCoeff centerRay exceptionalCoeff ↔
      0 < strictBoundaryRayDegree selfIntersection toricCoeff centerRay exceptionalCoeff k := by
  simp only [survivingRayOffsets, Finset.mem_filter, Finset.mem_univ, true_and]

namespace ContractedToricFiber

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))

variable {N V L : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] [AddCommGroup L]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n] {B : LinearMap.BilinForm ℤ L}
  {b : Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}
  [PrestableFamily ((Φ.boundaryIdeal h₀).subscheme ↘ S)]
  {γ : Type*} {a : γ → ((Φ.boundaryIdeal h₀).subscheme ↘ S).smoothLocus}
  {T : NodalCycleNumbering a m} {origin : ZMod m}
  {μ : L →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin r → ℤ)}
  {c : Multiplicative (Fin r → ℤ) →* ℂˣ}
  {M : MarkedSurface ℂ n B (Spec (CommRingCat.of (LaurentRing ℂ (Fin r))))}
  (p : ContractedToricFiber b s hΦ T origin μ c M)

local notation "u" => Φ.rayEquivOfNodalCycleNumbering hΦ (T.rotate origin)
local notation "rayAt" => Φ.rayFinEquivOfNodalCycleNumbering hΦ T origin
local notation "F" => LinearMap.BilinForm.prod
  (Chow.intersectionBilinForm ℂ Φ.algebraicRealization)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))
local notation "center" => (fun j : Fin r ↦ c (ofAdd (Pi.single j 1)))

private theorem markedBoundaryMap_pairing_pos_iff_mem_range
    [Φ.algebraicRealization.IsProjectiveOver ℂ]
    [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S)]
    (hp : p.IsNodalContraction) {H : LineBundleClass M.surface} (hH : H.IsAmple) (ρ : Φ.Ray) :
    (0 < (F) (Fan.markedBoundaryMap hΦ s (Pi.single ρ 1))
        (μ (M.picardMarking.symm (Additive.ofMul H)))) ↔
      ρ ∈ Set.range (p.numberedBoundaryRays hp.cartier) := by
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  obtain ⟨_, _, A, hA, e, he⟩ := hp.exists_tower
  have h := Fan.markedBoundaryMap_single_pairing_pullback_pos_iff hΦ b s (center) hA e.symm
    (by rw [Iso.symm_hom, reassoc_of% he]; exact p.projection_over)
    (by rw [Iso.symm_hom, he]; exact p.support_comap) hH ρ
  rw [Iso.symm_hom, he] at h
  simpa only [← p.marked_pullback (M.picardMarking.symm (Additive.ofMul H)),
    LinearEquiv.apply_symm_apply, toMul_ofMul,
    p.mem_range_numberedBoundaryRays_iff hp.cartier ρ] using h

variable (hp : p.IsNodalContraction) (hc : Φ.IsComplete)
    {H : LineBundleClass M.surface} (hH : H.IsAmple)
    (selfIntersection toricCoeff : ZMod m → ℤ) (centerRay : Fin r → Fin m)
    (exceptionalCoeff : Fin r → ℤ)
    (hself : ∀ j, selfIntersection j = Φ.rayBoundarySelfIntersection hΦ
      (Φ.rayEquivOfNodalCycleNumbering hΦ (T.rotate origin) j))
    (hcenter : ∀ t, Φ.rayFinEquivOfNodalCycleNumbering hΦ T origin (centerRay t) = s t)
    (hcoords : (Φ.rayDivisorToPicard hΦ
        (toricCoeff ∘ (Φ.rayEquivOfNodalCycleNumbering hΦ (T.rotate origin)).symm),
      exceptionalCoeff) =
      μ (M.picardMarking.symm (Additive.ofMul H)))

include hc hH hself hcenter hcoords in
private theorem survivingRayOffsets_val_eq :
    survivingRayOffsets selfIntersection toricCoeff centerRay exceptionalCoeff =
      (p.survivingBoundaryRayOffsets hp.cartier).val := by
  let : Φ.algebraicRealization.IsProjectiveOver ℂ :=
    Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
  let : SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S) :=
    ((finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
      Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  obtain ⟨b', -, hdet, hcone⟩ :=
    Φ.exists_positive_ray_numbering_of_nodalCycleNumbering b hΦ hc (T.rotate origin)
  have hnext (j : ZMod m) :
      b'.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
        ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ := by
    obtain ⟨σ, h₁, h₂, -⟩ := hcone j
    exact ⟨hdet j, σ.val, h₁, h₂⟩
  ext k
  let j := ZMod.finEquiv m k
  have hlabel (t : Fin r) : u (ZMod.finEquiv m (centerRay t)) = s t := by
    simpa only [Fan.rayFinEquivOfNodalCycleNumbering_apply] using hcenter t
  have hdegree :
      (F) (Fan.markedBoundaryMap hΦ s (Pi.single (u j) 1))
          (μ (M.picardMarking.symm (Additive.ofMul H))) =
        strictBoundaryRayDegree selfIntersection toricCoeff centerRay exceptionalCoeff k := by
    rw [← hcoords, Fan.markedBoundaryMap_single_pairing_eq_strictBoundaryRayDegree
      hΦ hc b' (u) s centerRay hlabel hnext, ← funext hself]
  rw [mem_survivingRayOffsets, ← hdegree, p.markedBoundaryMap_pairing_pos_iff_mem_range hp hH,
    ← Fan.rayFinEquivOfNodalCycleNumbering_apply, Set.powersetCard.mem_coe_iff,
    p.mem_survivingBoundaryRayOffsets]

include p hp hc hH hself hcenter hcoords in
/-- The computed survivor offsets, with cardinality given by the numbered boundary.
The toric divisor representing the toric part of the pulled-back ample class may be chosen
arbitrarily. -/
def survivingRayOffsetsOfPolarization : Set.powersetCard (Fin m) n :=
  Set.powersetCard.ofCard
    ((congrArg Finset.card
      (p.survivingRayOffsets_val_eq hp hc hH selfIntersection toricCoeff centerRay
        exceptionalCoeff hself hcenter hcoords)).trans
      (p.survivingBoundaryRayOffsets hp.cartier).prop)

local notation "offsets" => p.survivingRayOffsetsOfPolarization hp hc hH selfIntersection
  toricCoeff centerRay exceptionalCoeff hself hcenter hcoords

/-- The underlying finite set is the integer degree filter. -/
@[simp]
theorem survivingRayOffsetsOfPolarization_val :
    (offsets).val = survivingRayOffsets selfIntersection toricCoeff centerRay exceptionalCoeff :=
  Set.powersetCard.val_ofCard _

/-- A computed offset survives precisely when its strict boundary degree is positive. -/
@[simp]
theorem mem_survivingRayOffsetsOfPolarization (k : Fin m) :
    k ∈ offsets ↔ 0 < strictBoundaryRayDegree selfIntersection toricCoeff
      centerRay exceptionalCoeff k := by
  rw [← Set.powersetCard.mem_coe_iff, survivingRayOffsetsOfPolarization_val,
    mem_survivingRayOffsets]

/-- The computed set contains exactly the offsets occurring in the contracted numbering. -/
theorem survivingRayOffsetsOfPolarization_eq :
    offsets = p.survivingBoundaryRayOffsets hp.cartier :=
  Subtype.ext (p.survivingRayOffsets_val_eq hp hc hH selfIntersection toricCoeff centerRay
    exceptionalCoeff hself hcenter hcoords)

end ContractedToricFiber

end QPainleve.SignedClusterModularGroup
