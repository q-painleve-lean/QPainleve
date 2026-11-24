/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Refinement
public import QPainleve.SignedClusterModularGroup.Realization.Tropical

/-!
# Boundary order search under marked toric refinements

Representing a marked surface on a refined fan lifts the ray associated to
each numbered component of its boundary. Since the lifted rays have the same
primitive generators, the finite search for a boundary label from its order
vector gives the same result on either fan.
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup.ContractedToricFiber

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]
  {r m l n : ℕ} [NeZero m] [NeZero l] [NeZero n]
  {L : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray}
  {hΦ : Φ.IsRegular} {hΨ : Ψ.IsRegular}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "D[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)
local notation "Pic[" Φ "," r "]" =>
  Additive (LineBundleClass (Fan.algebraicRealization Φ)) × (Fin r → ℤ)

variable [PrestableFamily (D[Φ,hΦ₀] ↘ S)] [PrestableFamily (D[Ψ,hΨ₀] ↘ S)]
  {α β : Type*} {a : α → (D[Φ,hΦ₀] ↘ S).smoothLocus} {d : β → (D[Ψ,hΨ₀] ↘ S).smoothLocus}
  {T : Scheme.NodalCycleNumbering a m} {U : Scheme.NodalCycleNumbering d l}
  {o : ZMod m} {o' : ZMod l} {J : L →ₗ[ℤ] Pic[Φ,r]} {J' : L →ₗ[ℤ] Pic[Ψ,r]}
  {c : Multiplicative (Fin r → ℤ) →* ℂˣ}
  {M : MarkedSurface ℂ n B (Spec (CommRingCat.of (LaurentRing ℂ (Fin r))))}
  (p : ContractedToricFiber b s hΦ T o J c M) (h : Ψ.IsSubdivision Φ)
  (q : ContractedToricFiber b (h.liftRay ∘ s) hΨ U o' J' c M)
  (hq : q.boundaryMap = h.boundaryMap hΨ₀ hΦ₀ ≫ p.boundaryMap)
  (hM : M.pair.hom.left.ker.IsEffectiveCartier)

include hq in
/-- The ray representing any numbered component of the contracted surface is
the lift of its ray before subdivision. -/
theorem numberedBoundaryRays_subdivision (j : ZMod n) :
    q.numberedBoundaryRays hM j = h.liftRay (p.numberedBoundaryRays hM j) := by
  let : PrestableFamily (M.boundary ↘ S) := M.prestable
  let ρ := p.numberedBoundaryRays hM j
  obtain ⟨k, hk⟩ := T.component.surjective (Φ.boundaryNormalizationComponentEquiv hΦ ρ)
  obtain ⟨k', hk'⟩ :=
    U.component.surjective (Ψ.boundaryNormalizationComponentEquiv hΨ (h.liftRay ρ))
  have hp := (p.numberedBoundaryRays_eq_iff hM j k).mp
    (by rw [hk, Equiv.symm_apply_apply])
  have hpoint := h.boundaryMap_componentGenericPoint_of_liftRay T hΦ hΨ U hk hk'
  have hqpoint : q.boundaryMap (U.componentGenericPoint k') = M.cycle.componentGenericPoint j := by
    rw [hq, Scheme.Hom.comp_apply, hpoint, hp]
  simpa only [hk', Equiv.symm_apply_apply] using
    (q.numberedBoundaryRays_eq_iff hM j k').mpr hqpoint

include hq in
/-- Subdivision preserves the result of searching the numbered boundary
components for an order vector, including when the vector is absent or repeated. -/
theorem boundaryRayOfOrders_subdivision (orders : Fin r → ℤ) :
    Fan.boundaryRayOfOrders b (h.liftRay ∘ s)
      ((ZMod.finEquiv n).toEquiv.toEmbedding.trans (q.numberedBoundaryRays hM)) orders =
    Fan.boundaryRayOfOrders b s
      ((ZMod.finEquiv n).toEquiv.toEmbedding.trans (p.numberedBoundaryRays hM)) orders := by
  simp only [Fan.boundaryRayOfOrders_eq_find_coordinates, Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply, p.numberedBoundaryRays_subdivision h q hq hM,
    Function.comp_apply, h.primitiveGenerator_liftRay]

end QPainleve.SignedClusterModularGroup.ContractedToricFiber
