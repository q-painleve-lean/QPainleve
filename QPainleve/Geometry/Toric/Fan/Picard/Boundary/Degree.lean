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
`Fan.markedBoundaryMap_single_pairing` and the toric boundary pairing in
`Fan.intersectionBilinForm_rayChartDivisorToPicard_single`.
-/

public section

open AlgebraicGeometry Module TauCeti.AlgebraicGeometry

namespace QPainleve

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

universe u

variable (K : Type u) [Field K] [Infinite K] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  [(Φ.finiteFanScheme K).IsProjectiveOver K] [Nonempty Φ.cones]
  [SmoothOfRelativeDimension 2 (Φ.finiteFanScheme K ↘ Spec (CommRingCat.of K))]

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
    LinearMap.BilinForm.prod (Chow.intersectionBilinForm K (Φ.finiteFanScheme K))
        (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (ι → ℤ)))
        (markedBoundaryMap K hΦ s (Pi.single (e (ZMod.finEquiv m k)) 1))
        (Φ.rayChartDivisorToPicard K hΦ (toricCoeff ∘ e.symm), exceptionalCoeff) =
      strictBoundaryRayDegree (fun j ↦ Φ.rayBoundarySelfIntersection K hΦ (e j))
        toricCoeff centerRay exceptionalCoeff k := by
  classical
  let j := ZMod.finEquiv m k
  have htoric := Φ.intersectionBilinForm_rayChartDivisorToPicard_single K hΦ b hc
    (toricCoeff ∘ e.symm) (by simpa only [sub_add_cancel] using he (j - 1)) (he j)
  have hsum (t : ι) : (s t = e j) ↔ centerRay t = k := by
    rw [← hcenter t, e.injective.eq_iff, (ZMod.finEquiv m).injective.eq_iff]
  rw [markedBoundaryMap_single_pairing K, htoric, strictBoundaryRayDegree_apply]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, hsum, j]

end TauCeti.Toric.Fan
