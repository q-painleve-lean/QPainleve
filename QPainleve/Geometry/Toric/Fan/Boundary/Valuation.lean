/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Basic
public import QPainleve.Geometry.Toric.Fan.Charge

/-!
# Boundary orders of labeled toric characters

For each boundary ray, its order vector records the vanishing orders of the
characters indexed by a labeled family of primitive vectors. These orders
distinguish the boundary rays when the charges span the lattice over the rationals.
Searching the specified boundary labels recovers the ray with a given order vector.
-/

public noncomputable section

open AlgebraicGeometry Module Multiplicative

namespace TauCeti.Toric.Fan

variable {N : Type} {V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (s : ι → Φ.Ray)

/-- The order vector of the determinant characters of the labeled rays along the ray `ρ`. -/
def rayBoundaryOrders (ρ : Φ.Ray) : ι → ℤ :=
  fun j ↦ b.det ![(s j).primitiveGenerator, ρ.primitiveGenerator]

/-- The entry of a ray's order vector is the determinant of the charge and the ray generator. -/
@[simp]
theorem rayBoundaryOrders_apply (ρ : Φ.Ray) (j : ι) :
    rayBoundaryOrders b s ρ j = b.det ![(s j).primitiveGenerator, ρ.primitiveGenerator] :=
  (rfl)

/-- The determinant formula computes an order entry from the two integer coordinate pairs. -/
theorem rayBoundaryOrders_apply_eq_repr (ρ : Φ.Ray) (j : ι) :
    rayBoundaryOrders b s ρ j =
      b.repr (s j).primitiveGenerator 0 * b.repr ρ.primitiveGenerator 1 -
        b.repr (s j).primitiveGenerator 1 * b.repr ρ.primitiveGenerator 0 := by
  simp [rayBoundaryOrders_apply, Basis.det_apply, Basis.toMatrix_apply, Matrix.det_fin_two,
    mul_comm]

/-- Multiplying the character of a labeled ray by a nonzero constant preserves its order
along each boundary divisor. -/
theorem ord_rayBoundaryPoint_chargeCharacter [Nonempty Φ.cones]
    (hΦ : Φ.IsRegular) (ρ : Φ.Ray) (c : ℂˣ) (j : ι) :
    Φ.algebraicRealization.ord
      (algebraMap ℂ Φ.algebraicRealization.functionField (c : ℂ) *
        Φ.character (ofAdd (b.detDualEquiv (s j).primitiveGenerator).toAddMonoidHom))
      (Φ.rayBoundaryPoint hΦ ρ).val = rayBoundaryOrders b s ρ j := by
  simp only [ord_rayBoundaryPoint_mul_character, rayBoundaryOrders_apply,
    LinearMap.toAddMonoidHom_coe, Basis.detDualEquiv_apply]

/-- When the charges generate a finite-index sublattice, their order vector determines
the boundary ray, even when they do not generate the entire lattice over the integers. -/
theorem rayBoundaryOrders_injective [Finite ι]
    (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0) :
    Function.Injective (rayBoundaryOrders b s) := by
  classical
  let _ := Fintype.ofFinite ι
  intro ρ τ h
  let f := b.detDualEquiv ρ.primitiveGenerator
  let g := b.detDualEquiv τ.primitiveGenerator
  have hcomp : f.comp (rayChargeMap s) = g.comp (rayChargeMap s) := by
    apply (Pi.basisFun ℤ ι).ext
    intro j
    simp only [LinearMap.comp_apply, Pi.basisFun_apply, rayChargeMap_single, f, g,
      b.detDualEquiv_swap _ (s j).primitiveGenerator]
    have hj := congrFun h j
    simp only [rayBoundaryOrders_apply, ← b.detDualEquiv_apply] at hj
    exact congrArg Neg.neg hj
  apply Ray.primitiveGenerator_injective
  apply b.detDualEquiv.injective
  ext x
  obtain ⟨z, hz⟩ := (rayChargeMap s).range.toAddSubgroup.nsmul_index_mem x
  apply mul_left_cancel₀ (Int.natCast_ne_zero.mpr hindex)
  simpa only [LinearMap.comp_apply, hz, map_nsmul, nsmul_eq_mul] using
    LinearMap.congr_fun hcomp z

section Search

variable [Fintype ι] {n : ℕ} (boundary : Fin n ↪ Φ.Ray) (orders : ι → ℤ)

/-- Search the specified boundary rays for the label with the given order vector.
The enumeration can select just the rays belonging to the boundary on a contracted model. -/
def boundaryRayOfOrders : Option (Fin n) :=
  Fin.find? fun j ↦ decide (rayBoundaryOrders b s (boundary j) = orders)

/-- With the rays given in basis coordinates, the search uses only integer arithmetic and
equality over the finite set of charge labels. -/
theorem boundaryRayOfOrders_eq_find_coordinates :
    boundaryRayOfOrders b s boundary orders =
      Fin.find? fun j ↦
        let u := b.repr (boundary j).primitiveGenerator
        decide (∀ k, let v := b.repr (s k).primitiveGenerator
          v 0 * u 1 - v 1 * u 0 = orders k) :=
  congrArg Fin.find? (funext fun _ ↦ by
    simp only [funext_iff, rayBoundaryOrders_apply_eq_repr])

/-- The search returns no label exactly when the vector is absent from the specified rays. -/
@[simp]
theorem boundaryRayOfOrders_eq_none_iff :
    boundaryRayOfOrders b s boundary orders = none ↔
      ∀ j, rayBoundaryOrders b s (boundary j) ≠ orders := by
  simp [boundaryRayOfOrders, Fin.find?_decide_eq_dite]

/-- With finite-index charges, the search returns a label exactly when its order vector
agrees with the input. The matching ray is unique. -/
theorem boundaryRayOfOrders_eq_some_iff (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    (j : Fin n) :
    boundaryRayOfOrders b s boundary orders = some j ↔
      rayBoundaryOrders b s (boundary j) = orders := by
  have hinj := (rayBoundaryOrders_injective b s hindex).comp boundary.injective
  have hmem : j ∈ boundaryRayOfOrders b s boundary orders ↔
      rayBoundaryOrders b s (boundary j) = orders ∧
        ∀ k, k < j → rayBoundaryOrders b s (boundary k) ≠ orders := by
    simp only [boundaryRayOfOrders, Fin.mem_find?_iff, decide_eq_true_eq]
  rw [← Option.mem_def, hmem]
  refine ⟨And.left, fun hj ↦ ⟨hj, fun k hlt hk ↦ ?_⟩⟩
  exact hlt.ne (hinj (hk.trans hj.symm))

/-- Reconstruct a boundary label from the actual vanishing orders of its scaled torus
characters. The nonzero center parameters can be chosen independently of the input vector. -/
theorem boundaryRayOfOrders_eq_some_iff_ord
    (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    (j : Fin n) (hΦ : Φ.IsRegular) (c : ι → ℂˣ) :
    letI : Nonempty Φ.cones := ⟨(boundary j).toCone⟩
    boundaryRayOfOrders b s boundary orders = some j ↔
      ∀ k, Φ.algebraicRealization.ord
        (algebraMap ℂ Φ.algebraicRealization.functionField (c k : ℂ) *
          Φ.character (ofAdd (b.detDualEquiv (s k).primitiveGenerator).toAddMonoidHom))
        (Φ.rayBoundaryPoint hΦ (boundary j)).val = orders k := by
  simp only [ord_rayBoundaryPoint_chargeCharacter]
  rw [boundaryRayOfOrders_eq_some_iff b s boundary orders hindex j]
  exact funext_iff

end Search

end TauCeti.Toric.Fan
