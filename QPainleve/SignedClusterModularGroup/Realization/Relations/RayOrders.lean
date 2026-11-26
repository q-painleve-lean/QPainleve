/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.NumberedRays

/-!
# Computing the boundary order table of a toric presentation

Record the primitive ray coordinates in cyclic order starting at the ray of
boundary component zero. To compute the table for signed loop comparison,
enumerate the indices of the surviving rays in increasing order and pair their
coordinates with each charge by the determinant. The proof identifies this
enumeration with the actual boundary numbering of a marked contraction.
-/

public section

open AlgebraicGeometry CategoryTheory Module
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup

/-- Compute the boundary order table from integer charge coordinates and a subset of
toric ray indices. The ray indices are cyclic offsets from the initial boundary ray. -/
def boundaryOrderTable {ι : Type*} {m n : ℕ} (charge : ι → Fin 2 → ℤ)
    (ray : Fin m → Fin 2 → ℤ) (survivors : Set.powersetCard (Fin m) n) :
    Fin n → ι → ℤ :=
  fun j i ↦
    let u := ray (survivors.val.orderEmbOfFin survivors.prop j)
    Matrix.det !![charge i 0, charge i 1; u 0, u 1]

/-- Each table entry is the determinant of the charge and the selected primitive ray. -/
@[simp]
theorem boundaryOrderTable_apply {ι : Type*} {m n : ℕ} (charge : ι → Fin 2 → ℤ)
    (ray : Fin m → Fin 2 → ℤ) (survivors : Set.powersetCard (Fin m) n)
    (j : Fin n) (i : ι) :
    boundaryOrderTable charge ray survivors j i =
      charge i 0 * ray (survivors.val.orderEmbOfFin survivors.prop j) 1 -
        charge i 1 * ray (survivors.val.orderEmbOfFin survivors.prop j) 0 :=
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

local notation "rayAt" => Φ.rayFinEquivOfNodalCycleNumbering hΦ T origin

/-- The determinant table computed from the surviving offsets and integer coordinates
is the order table of the numbered components of the marked surface. A set of the correct
size suffices when every listed ray occurs in that boundary numbering. -/
theorem boundaryOrderTable_eq (survivors : Set.powersetCard (Fin m) n)
    (hkeep : ∀ k ∈ survivors, rayAt k ∈ Set.range (p.numberedBoundaryRays hD))
    (charge : Fin r → Fin 2 → ℤ) (ray : Fin m → Fin 2 → ℤ)
    (hcharge : ∀ k, charge k = b.repr (s k).primitiveGenerator)
    (hray : ∀ k ∈ survivors, ray k = b.repr (rayAt k).primitiveGenerator) :
    boundaryOrderTable charge ray survivors = p.numberedBoundaryOrders hD := by
  funext j k
  rw [p.numberedBoundaryOrders_apply, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    p.numberedBoundaryRays_eq_orderEmbOfFin hD survivors hkeep,
    Fan.rayBoundaryOrders_apply_eq_repr]
  have hj := Finset.orderEmbOfFin_mem survivors.val survivors.prop j
  simp only [boundaryOrderTable_apply, hcharge, hray _ hj]

end ContractedToricFiber

end QPainleve.SignedClusterModularGroup
