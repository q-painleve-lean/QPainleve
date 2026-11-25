/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import QPainleve.SignedClusterModularGroup.Realization.NumberedRays

import TauCeti.Data.ZMod.FinEquiv

/-!
# Computing the boundary order table of a toric presentation

Record the primitive ray coordinates in cyclic order starting at the ray of
boundary component zero. To compute the table for signed loop comparison,
enumerate the indices of the surviving rays in increasing order and pair their
coordinates with each charge by the determinant. The proof identifies this
enumeration with the actual boundary numbering of a marked contraction.
-/

public section

open AlgebraicGeometry CategoryTheory Module Multiplicative
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup

/-- Compute the boundary order table from integer charge coordinates and a subset of
toric ray indices. The ray indices are cyclic offsets from the initial boundary ray. -/
def boundaryOrderTable {ι : Type*} {m n : ℕ} (charge : ι → Fin 2 → ℤ)
    (ray : Fin m → Fin 2 → ℤ) (survivors : Finset (Fin m)) (hcard : survivors.card = n) :
    Fin n → ι → ℤ :=
  fun j i ↦
    let u := ray (survivors.orderEmbOfFin hcard j)
    Matrix.det !![charge i 0, charge i 1; u 0, u 1]

/-- Each table entry is the determinant of the charge and the selected primitive ray. -/
@[simp]
theorem boundaryOrderTable_apply {ι : Type*} {m n : ℕ} (charge : ι → Fin 2 → ℤ)
    (ray : Fin m → Fin 2 → ℤ) (survivors : Finset (Fin m)) (hcard : survivors.card = n)
    (j : Fin n) (i : ι) :
    boundaryOrderTable charge ray survivors hcard j i =
      charge i 0 * ray (survivors.orderEmbOfFin hcard j) 1 -
        charge i 1 * ray (survivors.orderEmbOfFin hcard j) 0 :=
  Matrix.det_fin_two_of _ _ _ _

namespace ContractedToricFiber

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))

variable {N V L : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] [AddCommGroup L]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones] {r m n : ℕ} [NeZero m] [NeZero n]
  {B : LinearMap.BilinForm ℤ L} {b : Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}
  [PrestableFamily ((Φ.boundaryIdeal h₀).subscheme ↘ S)]
  {γ : Type*} {a : γ → ((Φ.boundaryIdeal h₀).subscheme ↘ S).smoothLocus}
  {T : NodalCycleNumbering a m} {origin : ZMod m}
  {μ : L →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin r → ℤ)}
  {c : Multiplicative (Fin r → ℤ) →* ℂˣ}
  {M : MarkedSurface ℂ n B (Spec (CommRingCat.of (LaurentRing ℂ (Fin r))))}
  (p : ContractedToricFiber b s hΦ T origin μ c M) (hD : D[M].IsEffectiveCartier)

local notation "RayIndex" =>
  Equiv.trans (Φ.boundaryNormalizationComponentEquiv hΦ)
    (Equiv.trans (Equiv.symm (NodalCycleNumbering.component T))
      (Equiv.trans (Equiv.subRight origin) (Equiv.symm (RingEquiv.toEquiv (ZMod.finEquiv m)))))

/-- The contracted boundary numbering is the increasing enumeration of the surviving
ray indices, read from the specified initial toric ray. -/
theorem numberedBoundaryRays_eq_orderEmbOfFin (survivors : Finset (Fin m))
    (hcard : survivors.card = n)
    (hkeep : ∀ k ∈ survivors, (RayIndex).symm k ∈ Set.range (p.numberedBoundaryRays hD)) :
    ∀ j : Fin n, p.numberedBoundaryRays hD (ZMod.finEquiv n j) =
      (RayIndex).symm (survivors.orderEmbOfFin hcard j) := by
  let f (j : Fin n) := RayIndex (p.numberedBoundaryRays hD (ZMod.finEquiv n j))
  have hmono : StrictMono f := by
    intro a b hab
    simpa only [f, Fin.lt_def, Equiv.trans_apply, Equiv.subRight_apply,
      RingEquiv.toEquiv_eq_coe, RingEquiv.coe_coe_toEquiv_symm, ZMod.finEquiv_symm_apply_val] using
      p.strictMono_numberedBoundaryRays hD hab
  have hsubset : survivors ⊆ Finset.univ.image f := by
    intro k hk
    obtain ⟨j, hj⟩ := hkeep k hk
    obtain ⟨j, rfl⟩ := (ZMod.finEquiv n).surjective j
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by
      simp only [f, hj, Equiv.apply_symm_apply]⟩
  have hmem (j : Fin n) : f j ∈ survivors := by
    have heq := Finset.eq_of_subset_of_card_le hsubset (by
      rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ,
        Fintype.card_fin, hcard])
    rw [heq]
    exact Finset.mem_image_of_mem f (Finset.mem_univ j)
  intro j
  have hj := congrFun (Finset.orderEmbOfFin_unique hcard hmem hmono) j
  exact (RayIndex).injective (by simpa only [Equiv.apply_symm_apply] using hj)

/-- The determinant table computed from the surviving offsets and integer coordinates
is the order table of the numbered components of the marked surface. A set of the correct
size suffices when every listed ray's strict prime maps to a boundary prime. -/
theorem boundaryOrderTable_eq (survivors : Finset (Fin m)) (hcard : survivors.card = n)
    (hkeep : ∀ k ∈ survivors,
      p.projection (Fan.internalBlowupBoundaryPrimeEquiv hΦ b s
        (fun j ↦ c (ofAdd (Pi.single j 1))) ((RayIndex).symm k)).val ∈ D[M].boundaryPrimes)
    (charge : Fin r → Fin 2 → ℤ) (ray : Fin m → Fin 2 → ℤ)
    (hcharge : ∀ k, charge k = b.repr (s k).primitiveGenerator)
    (hray : ∀ k ∈ survivors, ray k = b.repr ((RayIndex).symm k).primitiveGenerator) :
    boundaryOrderTable charge ray survivors hcard = fun j : Fin n ↦
      Fan.rayBoundaryOrders b s (p.numberedBoundaryRays hD (ZMod.finEquiv n j)) := by
  funext j k
  have hsurvives l hl := (p.mem_range_numberedBoundaryRays_iff hD _).mpr (hkeep l hl)
  rw [p.numberedBoundaryRays_eq_orderEmbOfFin hD survivors hcard hsurvives,
    Fan.rayBoundaryOrders_apply_eq_repr]
  simp only [boundaryOrderTable_apply, hcharge, hray _ (Finset.orderEmbOfFin_mem survivors hcard j)]

end ContractedToricFiber

end QPainleve.SignedClusterModularGroup
