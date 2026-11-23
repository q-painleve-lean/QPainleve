/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.BoundaryQuotient
public import QPainleve.LinearAlgebra.BilinearForm.Prod
public import QPainleve.LinearAlgebra.BilinearForm.QuotientDual

import QPainleve.LinearAlgebra.Dual.Kernel

/-!
# The charge kernel in marked Picard coordinates

Dualizing the marked boundary quotient identifies the right orthogonal complement
of the boundary with the integral charge kernel. The coordinates of the comparison
are the pairings with the total exceptional classes. For the block-diagonal
intersection form, the inverse recovers the toric class by its boundary degrees
and has exceptional coordinates equal to the negatives of the kernel coordinates.

The geometric calculation is the one in Gross, Hacking, and Keel,
*Birational geometry of cluster algebras*, proof of Theorem 5.5.
-/

public noncomputable section

open Module
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N : Type} {V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

private theorem charge_dual_eval_injective (Φ : Fan i) : Function.Injective (Dual.eval ℤ N) := by
  have := Φ.lattice.free
  have := Φ.lattice.finite
  exact (bijective_dual_eval ℤ N).injective

variable {Φ : Fan i} [Nonempty Φ.cones] [Finite ι]
  (hΦ : Φ.IsRegular) (s : ι → Φ.Ray)

local notation "Pic" => Additive (LineBundleClass Φ.algebraicRealization)
local notation "Mark" => (Pic × (ι → ℤ))
local notation "M" => LinearMap.range (markedBoundaryMap hΦ s)

/-- The orthogonal complement of the marked boundary identifies with the kernel of the charge map.
The pairing on the whole marking is perfect, and the restriction to the complement may be
degenerate. The charge map can have any rank. -/
def boundaryOrthogonalEquivChargeKernel (B : LinearMap.BilinForm ℤ Mark)
    [LinearMap.IsPerfPair B] : B.orthogonal M ≃ₗ[ℤ] (rayChargeMap s).ker :=
  (B.orthogonalEquivDualQuotient M).trans
    ((boundaryQuotientEquivDualChargeCokernel hΦ s).symm.dualMap.trans
      ((rayChargeMap s).kerEquivDualCokerDualMap (charge_dual_eval_injective Φ)).symm)

/-- Each charge coordinate is obtained by pairing with the corresponding total exceptional
class in the first argument. For symmetric intersection pairings this is the intersection
of the orthogonal class with the exceptional class. -/
@[simp] theorem boundaryOrthogonalEquivChargeKernel_apply [DecidableEq ι]
    (B : LinearMap.BilinForm ℤ Mark) [LinearMap.IsPerfPair B] (x : B.orthogonal M) (j : ι) :
    (boundaryOrthogonalEquivChargeKernel hΦ s B x : ι → ℤ) j =
      B (0, Pi.single j 1) x := by
  let φ : Dual ℤ (ι → ℤ) := LinearMap.proj j
  let e := (rayChargeMap s).kerEquivDualCokerDualMap (charge_dual_eval_injective Φ)
  have hφ : (fun k ↦ φ (Pi.single k 1)) = Pi.single j 1 := by
    funext k
    by_cases h : k = j
    · subst k
      simp [φ]
    · simp [φ, Pi.single_eq_of_ne, h, Ne.symm h]
  calc
    _ = e (boundaryOrthogonalEquivChargeKernel hΦ s B x) (Submodule.Quotient.mk φ) := by
      simp [e, φ]
    _ = B (0, Pi.single j 1) x := by
      rw [boundaryOrthogonalEquivChargeKernel, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
        e.apply_symm_apply, LinearEquiv.dualMap_apply,
        boundaryQuotientEquivDualChargeCokernel_symm_apply_mk,
        LinearMap.BilinForm.orthogonalEquivDualQuotient_apply_mk, hφ]

variable [Fintype ι]
  (A : LinearMap.BilinForm ℤ (Additive (LineBundleClass (Fan.algebraicRealization Φ))))

local notation "negDot" => (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (ι → ℤ)))

/-- In the orthogonal marking with exceptional squares `-1`, the inverse charge comparison
has exceptional coefficients equal to the negatives of the kernel coordinates. -/
@[simp] theorem boundaryOrthogonalEquivChargeKernel_symm_snd
    [LinearMap.IsPerfPair (A.prod negDot)]
    (x : (rayChargeMap s).ker) :
    ((boundaryOrthogonalEquivChargeKernel hΦ s (A.prod negDot)).symm x : Mark).2 =
      -(x : ι → ℤ) := by
  classical
  let e := boundaryOrthogonalEquivChargeKernel hΦ s (A.prod negDot)
  funext j
  have h := boundaryOrthogonalEquivChargeKernel_apply hΦ s (A.prod negDot) (e.symm x) j
  rw [e.apply_symm_apply] at h
  simpa [LinearMap.BilinForm.prod_apply, dotProductBilin_apply_apply, single_dotProduct, e]
    using (congrArg Neg.neg h).symm

/-- The toric part of the inverse pairs with each toric boundary class by the sum of the kernel
coordinates at its centers. The identity is linear in the coefficients of the toric divisor. -/
theorem boundaryOrthogonalEquivChargeKernel_symm_fst_pairing
    [LinearMap.IsPerfPair (A.prod negDot)]
    (x : (rayChargeMap s).ker)
    (a : Φ.Ray → ℤ) :
    A (Φ.rayDivisorToPicard hΦ a)
        ((boundaryOrthogonalEquivChargeKernel hΦ s (A.prod negDot)).symm x : Mark).1 =
      ∑ j, a (s j) * (x : ι → ℤ) j := by
  let y := (boundaryOrthogonalEquivChargeKernel hΦ s (A.prod negDot)).symm x
  have hz := LinearMap.BilinForm.mem_orthogonal_iff.mp y.property (markedBoundaryMap hΦ s a)
    (LinearMap.mem_range_self _ a)
  rw [LinearMap.BilinForm.prod_apply, markedBoundaryMap_apply,
    boundaryOrthogonalEquivChargeKernel_symm_snd hΦ s A x] at hz
  apply sub_eq_zero.mp
  simpa [dotProductBilin_apply_apply, dotProduct, sub_eq_add_neg, y] using hz

/-- The prescribed boundary degrees of a kernel vector determine a unique toric class. -/
theorem existsUnique_rayDivisorToPicard_pairing_eq_charge
    [LinearMap.IsPerfPair (A.prod negDot)] (x : (rayChargeMap s).ker) :
    ∃! H : Pic, ∀ a : Φ.Ray → ℤ,
      A (Φ.rayDivisorToPicard hΦ a) H = ∑ j, a (s j) * (x : ι → ℤ) j := by
  let y := (boundaryOrthogonalEquivChargeKernel hΦ s (A.prod negDot)).symm x
  have hy := boundaryOrthogonalEquivChargeKernel_symm_fst_pairing hΦ s A x
  refine ⟨(y : Mark).1, hy, fun H hH ↦ ?_⟩
  have hA := (LinearMap.BilinForm.isPerfPair_prod_iff.mp
    (inferInstance : LinearMap.IsPerfPair (A.prod negDot))).1
  apply (LinearMap.IsPerfPair.bijective_right A).injective
  ext z
  obtain ⟨a, rfl⟩ := Φ.rayDivisorToPicard_surjective hΦ z
  exact (hH a).trans (hy a).symm

end TauCeti.Toric.Fan
