/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.BoundaryQuotient
public import QPainleve.Geometry.Toric.Fan.Boundary.SelfIntersection

/-!
# Degrees along the strict toric boundary

The integer Picard coordinates of a class on an ordered internal blowup give
its degree on a strict boundary ray. The toric divisor contributes its
coefficients at the ray and its two neighbors. Each total exceptional
coordinate contributes on the ray of its center. The comparison uses
`Fan.markedBoundaryMap_single_pairing` and the toric wall relation in
`Fan.rayBoundarySelfIntersection_eq_neg_det_of_neighbors`.
-/

public section

open AlgebraicGeometry Module TauCeti.AlgebraicGeometry
open scoped Matrix

namespace QPainleve

/-- Toric self-intersection in positive cyclic order, from the two neighboring
primitive ray coordinates. -/
def toricBoundarySelfIntersection {m : ℕ} (ray : ZMod m → Fin 2 → ℤ) (j : ZMod m) : ℤ :=
  let u := ray (j - 1)
  let v := ray (j + 1)
  Int.neg (u 0 * v 1 - u 1 * v 0)

/-- The self-intersection is the negative determinant of the two neighboring rays. -/
@[simp]
theorem toricBoundarySelfIntersection_apply {m : ℕ} (ray : ZMod m → Fin 2 → ℤ) (j : ZMod m) :
    toricBoundarySelfIntersection ray j =
      (-(Matrix.det !![ray (j - 1) 0, ray (j - 1) 1; ray (j + 1) 0, ray (j + 1) 1])) := by
  rw [Matrix.det_fin_two_of]
  rfl

/-- Degree on the strict boundary component of a ray, computed from the integer
Picard coordinates of a class on the internal blowup. The offsets start at the
ray of component zero. -/
def strictBoundaryRayDegree {m : ℕ} [NeZero m] {ι : Type*} [Fintype ι]
    (selfIntersection toricCoeff : ZMod m → ℤ) (centerRay : ι → Fin m)
    (exceptionalCoeff : ι → ℤ) (k : Fin m) : ℤ :=
  let j := ZMod.finEquiv m k
  toricCoeff (j - 1) + selfIntersection j * toricCoeff j + toricCoeff (j + 1) +
    ∑ t ∈ Finset.univ.filter (fun t ↦ centerRay t = k), exceptionalCoeff t

/-- The degree uses the two neighboring coefficients, the self-intersection term, and
the total exceptional coefficients on this ray. -/
@[simp]
theorem strictBoundaryRayDegree_apply {m : ℕ} [NeZero m] {ι : Type*} [Fintype ι]
    (selfIntersection toricCoeff : ZMod m → ℤ) (centerRay : ι → Fin m)
    (exceptionalCoeff : ι → ℤ) (k : Fin m) :
    strictBoundaryRayDegree selfIntersection toricCoeff centerRay exceptionalCoeff k =
      let j := ZMod.finEquiv m k
      toricCoeff (j - 1) + selfIntersection j * toricCoeff j + toricCoeff (j + 1) +
        ∑ t ∈ Finset.univ.filter (fun t ↦ centerRay t = k), exceptionalCoeff t :=
  (rfl)

end QPainleve

namespace TauCeti.Toric.Fan

open QPainleve

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  [Φ.algebraicRealization.IsProjectiveOver ℂ]

/-- In positive cyclic coordinates, each ray's self-intersection equals the integer
self-intersection computed from its neighboring rays. -/
theorem rayBoundarySelfIntersection_eq_of_positiveRayCoordinates
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (b : Basis (Fin 2) ℤ N)
    {m : ℕ} (e : ZMod m ≃ Φ.Ray)
    (he : ∀ j, b.detDualEquiv (e j).primitiveGenerator (e (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (e j).toCone ≤ σ ∧ (e (j + 1)).toCone ≤ σ) :
    (fun j ↦ Φ.rayBoundarySelfIntersection hΦ (e j)) =
      toricBoundarySelfIntersection (fun j ↦ b.repr (e j).primitiveGenerator) := by
  funext j
  have hp := he (j - 1)
  rw [sub_add_cancel] at hp
  rw [toricBoundarySelfIntersection_apply, Matrix.det_fin_two_of,
    rayBoundarySelfIntersection_eq_neg_det_of_neighbors b hΦ hc hp (he j),
    Basis.detDualEquiv_apply, Basis.det_apply]
  simp only [Matrix.det_fin_two, Basis.toMatrix_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

variable [Nonempty Φ.cones]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ))]

/-- In a cyclic ray numbering, the marked pairing with a strict boundary component
is the integer degree of the toric divisor and exceptional coefficients. -/
theorem markedBoundaryMap_single_pairing_eq_strictBoundaryRayDegree
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (b : Basis (Fin 2) ℤ N)
    {m : ℕ} [NeZero m] (e : ZMod m ≃ Φ.Ray) {ι : Type*} [Fintype ι]
    (s : ι → Φ.Ray) (centerRay : ι → Fin m)
    (hcenter : ∀ t, e (ZMod.finEquiv m (centerRay t)) = s t)
    (he : ∀ j, b.detDualEquiv (e j).primitiveGenerator (e (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (e j).toCone ≤ σ ∧ (e (j + 1)).toCone ≤ σ)
    (toricCoeff : ZMod m → ℤ) (exceptionalCoeff : ι → ℤ) (k : Fin m) :
    LinearMap.BilinForm.prod (Chow.intersectionBilinForm ℂ Φ.algebraicRealization)
        (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (ι → ℤ)))
        (markedBoundaryMap hΦ s (Pi.single (e (ZMod.finEquiv m k)) 1))
        (Φ.rayDivisorToPicard hΦ (toricCoeff ∘ e.symm), exceptionalCoeff) =
      strictBoundaryRayDegree (fun j ↦ Φ.rayBoundarySelfIntersection hΦ (e j))
        toricCoeff centerRay exceptionalCoeff k := by
  let j := ZMod.finEquiv m k
  have htoric := Φ.intersectionBilinForm_rayDivisorToPicard_single hΦ b hc
    (toricCoeff ∘ e.symm) (by simpa only [sub_add_cancel] using he (j - 1)) (he j)
  have hsum (t : ι) : (s t = e j) ↔ centerRay t = k := by
    rw [← hcenter t, e.injective.eq_iff, (ZMod.finEquiv m).injective.eq_iff]
  rw [markedBoundaryMap_single_pairing, htoric, strictBoundaryRayDegree_apply]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, hsum, j]

end TauCeti.Toric.Fan
