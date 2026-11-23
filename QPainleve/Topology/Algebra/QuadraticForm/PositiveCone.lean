/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Real
public import QPainleve.LinearAlgebra.QuadraticForm.PositiveCone
public import TauCeti.Topology.Algebra.QuadraticForm.Continuity
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Order.IntermediateValue

/-!
# Components of the positive cone

For a nondegenerate real quadratic form of positive index one, the component of a
positive vector is cut out within the positive locus by positive polar pairing with
that vector. A nonzero isotropic vector on its boundary distinguishes the same component.
Its closure is given by the corresponding weak inequalities, and the polar pairing
is nonnegative on pairs from this closure.

For an intersection form `B`, the associated quadratic form is `x ↦ B x x`.
Its polar pairing is twice the intersection pairing, so the sign conditions agree.
The description by pairing with an ample class is used in Gross, Hacking and Keel,
[*Moduli of surfaces with an anti-canonical cycle*, Lemma 2.14][GHK].

[GHK]: https://paulhacking.github.io/mlp.pdf#page=13
-/

public section

open QuadraticMap Set

namespace QuadraticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace V] [IsModuleTopology ℝ V] {Q : QuadraticForm ℝ V}

/-- The connected component of a positive vector `h` consists exactly of the
positive vectors with positive polar pairing with `h`. -/
theorem connectedComponentIn_pos_eq (hQ : Q.Nondegenerate) (hsig : sigPos Q ≤ 1)
    {h : V} (hh : 0 < Q h) :
    connectedComponentIn {x | 0 < Q x} h = {x | 0 < Q x ∧ 0 < polar Q h x} := by
  have : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℝ V
  have hself : 0 < polar Q h h := by
    rw [polar_self, two_nsmul]
    exact add_pos hh hh
  have hset : h ∈ {x | 0 < Q x} := hh
  have hh₀ : h ≠ 0 := by
    rintro rfl
    simp at hh
  refine Subset.antisymm (fun x hx ↦ ?_) ?_
  · refine ⟨connectedComponentIn_subset _ _ hx, ?_⟩
    by_contra! hnot
    have hc : Continuous (polar Q h) :=
      IsModuleTopology.continuous_of_linearMap (Q.polarBilin h)
    obtain ⟨z, hz, he⟩ := isPreconnected_connectedComponentIn.intermediate_value hx
      (mem_connectedComponentIn hset) hc.continuousOn ⟨hnot, hself.le⟩
    exact hh₀ (eq_zero_of_polar_eq_zero_of_nonneg hQ hsig
      (connectedComponentIn_subset _ _ hz) he hh.le)
  · have hconn := (convex_setOf_pos_and_polar_pos hQ hsig hh).isPreconnected
    exact hconn.subset_connectedComponentIn ⟨hh, hself⟩ (fun _ hx ↦ hx.1)

/-- A nonzero vector of nonnegative square on the positive side of `h` detects
the component of `h` by its own polar pairing. This includes isotropic vectors. -/
theorem connectedComponentIn_pos_eq_of_nonneg (hQ : Q.Nondegenerate) (hsig : sigPos Q ≤ 1)
    {h d : V} (hh : 0 < Q h) (hd : 0 ≤ Q d) (hd₀ : d ≠ 0) (hhd : 0 ≤ polar Q h d) :
    connectedComponentIn {x | 0 < Q x} h = {x | 0 < Q x ∧ 0 < polar Q d x} := by
  rw [connectedComponentIn_pos_eq hQ hsig hh]
  ext x
  exact and_congr_right fun hx ↦ (polar_pos_iff_of_nonneg hQ hsig hh hd hd₀ hhd hx).symm

/-- Adding a positive multiple of a positive vector to a point on its closed
positive side gives a point in the same positive component. -/
theorem add_smul_mem_connectedComponentIn_pos (hQ : Q.Nondegenerate) (hsig : sigPos Q ≤ 1)
    {h x : V} (hh : 0 < Q h) (hx : 0 ≤ Q x) (hhx : 0 ≤ polar Q h x)
    {t : ℝ} (ht : 0 < t) :
    x + t • h ∈ connectedComponentIn {z | 0 < Q z} h := by
  rw [connectedComponentIn_pos_eq hQ hsig hh]
  refine ⟨?_, ?_⟩
  · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_right, smul_eq_mul, smul_eq_mul,
      polar_comm Q x h]
    exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos hx (by positivity))
      (mul_nonneg ht.le hhx)
  · rw [polar_add_right, polar_smul_right, polar_self, two_nsmul, smul_eq_mul]
    exact add_pos_of_nonneg_of_pos hhx (mul_pos ht (add_pos hh hh))

/-- The closure of the component of `h` is cut out by nonnegative square and
nonnegative polar pairing with `h`. -/
theorem closure_connectedComponentIn_pos_eq (hQ : Q.Nondegenerate) (hsig : sigPos Q ≤ 1)
    {h : V} (hh : 0 < Q h) :
    closure (connectedComponentIn {x | 0 < Q x} h) = {x | 0 ≤ Q x ∧ 0 ≤ polar Q h x} := by
  have : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℝ V
  have hc : Continuous (polar Q h) :=
    IsModuleTopology.continuous_of_linearMap (Q.polarBilin h)
  refine Subset.antisymm
    (closure_minimal ?_
      ((isClosed_le continuous_const Q.continuous).inter (isClosed_le continuous_const hc))) ?_
  · rw [connectedComponentIn_pos_eq hQ hsig hh]
    exact fun _ hx ↦ ⟨hx.1.le, hx.2.le⟩
  intro x hx
  have hc' : Continuous (fun t : ℝ ↦ x + t • h) := by fun_prop
  have h0 : (0 : ℝ) ∈ closure (Ioi 0) := by simp [closure_Ioi]
  have happrox : x ∈ closure ((fun t : ℝ ↦ x + t • h) '' Ioi 0) := by
    simpa using mem_closure_image hc'.continuousAt h0
  exact closure_mono
    (image_subset_iff.mpr fun _ ht ↦ add_smul_mem_connectedComponentIn_pos hQ hsig hh hx.1 hx.2 ht)
      happrox

/-- A nonzero vector in the closure of a positive-cone component detects that component
by its polar pairing with positive vectors. -/
theorem connectedComponentIn_pos_eq_of_mem_closure
    (hQ : Q.Nondegenerate) (hsig : sigPos Q ≤ 1) {h d : V} (hh : 0 < Q h)
    (hd₀ : d ≠ 0) (hd : d ∈ closure (connectedComponentIn {x | 0 < Q x} h)) :
    connectedComponentIn {x | 0 < Q x} h = {x | 0 < Q x ∧ 0 < polar Q d x} := by
  rw [closure_connectedComponentIn_pos_eq hQ hsig hh] at hd
  exact connectedComponentIn_pos_eq_of_nonneg hQ hsig hh hd.1 hd₀ hd.2

/-- Two vectors in the closure of the same positive component pair nonnegatively. -/
theorem polar_nonneg_of_mem_closure_connectedComponentIn_pos (hQ : Q.Nondegenerate)
    (hsig : sigPos Q ≤ 1) {h x y : V} (hh : 0 < Q h)
    (hx : x ∈ closure (connectedComponentIn {z | 0 < Q z} h))
    (hy : y ∈ closure (connectedComponentIn {z | 0 < Q z} h)) :
    0 ≤ polar Q x y := by
  rw [closure_connectedComponentIn_pos_eq hQ hsig hh] at hx hy
  exact polar_nonneg_of_nonneg_of_polar_nonneg hQ hsig hh hx.1 hy.1 hx.2 hy.2

end QuadraticForm
