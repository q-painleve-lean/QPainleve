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

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

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

local notation "S" => Spec (CommRingCat.of k₀)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))

variable {N V L : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] [AddCommGroup L]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones] {r m n : ℕ} [NeZero m] [NeZero n]
  {B : LinearMap.BilinForm ℤ L} {b : Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}
  [PrestableFamily ((Φ.toricBoundaryIdeal k₀ h₀).subscheme ↘ Spec (.of k₀))]
  {γ : Type*} {a : γ → ((Φ.toricBoundaryIdeal k₀ h₀).subscheme ↘ Spec (.of k₀)).smoothLocus}
  {T : NodalCycleNumbering a m} {origin : ZMod m}
  {μ : L →ₗ[ℤ] Additive (LineBundleClass (Φ.finiteFanScheme k₀)) × (Fin r → ℤ)}
  {c : Multiplicative (Fin r → ℤ) →* k₀ˣ}
  {M : MarkedSurface k₀ n B (Spec (CommRingCat.of (LaurentRing k₀ (Fin r))))}
  (p : ContractedToricFiber b s hΦ T origin μ c M) (hD : D[M].IsEffectiveCartier)

local notation "rayAt" => Φ.rayFinEquivOfNodalCycleNumbering k₀ hΦ T origin

/-- The determinant table computed from the surviving offsets and integer coordinates
is the order table of the numbered components of the marked surface. -/
theorem boundaryOrderTable_eq (survivors : Set.powersetCard (Fin m) n)
    (hsurvivors : survivors = p.survivingBoundaryRayOffsets hD)
    (charge : Fin r → Fin 2 → ℤ) (ray : Fin m → Fin 2 → ℤ)
    (hcharge : ∀ k, charge k = b.repr (s k).primitiveGenerator)
    (hray : ∀ k ∈ survivors, ray k = b.repr (rayAt k).primitiveGenerator) :
    boundaryOrderTable charge ray survivors = p.numberedBoundaryOrders hD := by
  subst survivors
  funext j k
  rw [p.numberedBoundaryOrders_apply, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    p.numberedBoundaryRays_eq_orderEmbOfFin hD j, Fan.rayBoundaryOrders_apply_eq_repr]
  have hj := Finset.orderEmbOfFin_mem (p.survivingBoundaryRayOffsets hD).val
    (p.survivingBoundaryRayOffsets hD).prop j
  simp only [boundaryOrderTable_apply, hcharge, hray _ hj]

end ContractedToricFiber

end QPainleve.SignedClusterModularGroup
