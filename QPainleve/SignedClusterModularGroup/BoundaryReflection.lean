/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Codex
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.Data.ZMod.Basic
public import TauCeti.Algebra.Module.Primitive
public import TauCeti.LinearAlgebra.BilinearForm.Characteristic
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import QPainleve.SignedClusterModularGroup.BoundaryCycle

/-!
# Reflection of an affine type-A boundary cycle

In a unimodular symmetric lattice, a boundary cycle with primitive characteristic total class
admits an involutive isometry reversing the cyclic order. It fixes a square `-1` class that
pairs to one with the component at the cut. On the plane of these two classes the involution is
the identity. On its orthogonal complement it acts by the negative of the type-A reversal.
-/

open scoped BigOperators

public section

namespace QPainleve

open LinearMap LinearMap.BilinForm

variable {L : Type*} [AddCommGroup L]
variable {n : ℕ} [NeZero n]
variable {B : LinearMap.BilinForm ℤ L} {D : ZMod n → L}

private theorem exists_boundary_unit_pairing
    (hIntersection : ∀ i j : ZMod n,
      B (D i) (D j) = (-2 : ℤ) * (if i = j then 1 else 0) +
        (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))
    {x : L} (hx : B x (∑ i, D i) = 1) :
    ∃ j₀ : ZMod n, ∃ y : L, ∀ j : ZMod n, B y (D j) = if j = j₀ then 1 else 0 := by
  classical
  -- In the cokernel of the degree map, the classes of the unit vectors form an
  -- arithmetic progression. A degree vector of total degree one then represents
  -- the same class as the unit vector at its moment modulo n.
  let degrees : L →ₗ[ℤ] (ZMod n → ℤ) := LinearMap.pi fun j ↦ B.flip (D j)
  let q := degrees.range.mkQ
  let e : ZMod n → (ZMod n → ℤ) := fun j ↦ Pi.single j 1
  let v := q ∘ e
  have hdegrees (y : L) (j : ZMod n) : degrees y j = B y (D j) := rfl
  have hrel (i : ZMod n) : (-2 : ℤ) • v i + v (i + 1) + v (i - 1) = 0 := by
    have heq : degrees (D i) = (-2 : ℤ) • e i + e (i + 1) + e (i - 1) := by
      ext j
      by_cases h : i = j <;> simp [hdegrees, hIntersection, e, Pi.single_apply, h, eq_comm]
    have hzero := DFunLike.congr_fun (LinearMap.range_mkQ_comp degrees) (D i)
    simpa only [v, q, Function.comp_apply, LinearMap.comp_apply, LinearMap.zero_apply, heq,
      map_add, map_zsmul] using hzero
  have hstep (i : ZMod n) : v (i + 1) - v i = v i - v (i - 1) := by
    have h := hrel i
    rw [neg_smul, two_smul] at h
    calc
      v (i + 1) - v i = (-(v i + v i) + v (i + 1) + v (i - 1)) + (v i - v (i - 1)) := by abel
      _ = _ := by rw [h, zero_add]
  let d := v 1 - v 0
  have hdiff (k : ℕ) : v ((k : ZMod n) + 1) - v k = d := by
    induction k with
    | zero => simp [d]
    | succ k ih =>
      rw [Nat.cast_succ]
      exact (hstep ((k : ZMod n) + 1)).trans (by simpa using ih)
  have hval (k : ℕ) : v (k : ZMod n) = v 0 + k • d := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ, ← sub_add_cancel (v ((k : ZMod n) + 1)) (v k), hdiff, ih, succ_nsmul]
      abel
  have hn : (n : ℤ) • d = 0 := by
    have h := hval n
    rw [ZMod.natCast_self] at h
    have hcancel : v 0 + n • d = v 0 + 0 := h.symm.trans (add_zero _).symm
    simpa using add_left_cancel hcancel
  let l : ZMod n →+ _ := ZMod.lift n
    ⟨(LinearMap.toSpanSingleton ℤ _ d).toAddMonoidHom, hn⟩
  have hv (i : ZMod n) : v i = v 0 + l i := by
    have hl := ZMod.lift_coe n
      ⟨(LinearMap.toSpanSingleton ℤ _ d).toAddMonoidHom, hn⟩ (i.val : ℤ)
    rw [Int.cast_natCast, ZMod.natCast_zmod_val] at hl
    dsimp only [l]
    rw [hl]
    simpa only [ZMod.natCast_zmod_val, LinearMap.toAddMonoidHom_coe,
      LinearMap.toSpanSingleton_apply, natCast_zsmul] using hval i.val
  have hsum : ∑ i : ZMod n, degrees x i = 1 := by
    simpa only [hdegrees, map_sum] using hx
  have hcoords : (∑ i : ZMod n, degrees x i • e i) = degrees x := by
    simpa only [e, ← Pi.single_smul, smul_eq_mul, mul_one] using Finset.univ_sum_single (degrees x)
  let j₀ : ZMod n := ∑ i : ZMod n, degrees x i • i
  have hq : q (e j₀) = 0 := calc
    q (e j₀) = v 0 + l j₀ := hv _
    _ = ∑ i : ZMod n, degrees x i • v i := by
      calc
        _ = ∑ i : ZMod n, degrees x i • (v 0 + l i) := by
          simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hsum, one_smul,
            j₀, map_sum, map_zsmul]
        _ = _ := Finset.sum_congr rfl fun i _ ↦ congrArg (degrees x i • ·) (hv i).symm
    _ = q (degrees x) := by
      simpa only [map_sum, map_smul, v, Function.comp_apply] using congrArg q hcoords
    _ = 0 := DFunLike.congr_fun (LinearMap.range_mkQ_comp degrees) x
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
  obtain ⟨y, hy⟩ := hq
  refine ⟨j₀, y, fun j ↦ ?_⟩
  simpa [hdegrees, e, Pi.single_apply, eq_comm] using congrFun hy j

/-- The sum of the first `k` components after cutting the cycle at `j₀`. -/
private def boundaryPrefix (D : ZMod n → L) (j₀ : ZMod n) (k : ℕ) : L :=
  ∑ a ∈ Finset.range k, D (j₀ + ((a + 1 : ℕ) : ZMod n))

omit [NeZero n] in
private theorem boundaryPrefix_succ (j₀ : ZMod n) (k : ℕ) :
    boundaryPrefix D j₀ (k + 1) = boundaryPrefix D j₀ k + D (j₀ + ((k + 1 : ℕ) : ZMod n)) :=
  Finset.sum_range_succ _ _

private theorem boundaryPrefix_pairing
    (hIntersection : ∀ i j : ZMod n,
      B (D i) (D j) = (-2 : ℤ) * (if i = j then 1 else 0) +
        (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))
    (j₀ : ZMod n) (i j : Fin n) :
    B (boundaryPrefix D j₀ i) (boundaryPrefix D j₀ j) =
      -(if i = j then 1 else 0) + (if i = 0 then 1 else 0) + (if j = 0 then 1 else 0) - 1 := by
  classical
  let e (a b : ℕ) : ℤ := if (a : ZMod n) = (b : ZMod n) then 1 else 0
  have hdiff (a b : ℕ) :
      B (D (j₀ + ((a + 1 : ℕ) : ZMod n))) (D (j₀ + ((b + 1 : ℕ) : ZMod n))) =
        (e a (b + 1) - e (a + 1) (b + 1)) - (e a b - e (a + 1) b) := by
    have hnext : (b : ZMod n) + 1 = a + 1 + 1 ↔ (a : ZMod n) + 1 = b := by
      rw [add_right_cancel_iff]
      exact eq_comm
    have hprev : (b : ZMod n) + 1 = (a : ZMod n) + 1 - 1 ↔ (a : ZMod n) = b + 1 := by
      rw [add_sub_cancel_right]
      exact eq_comm
    have hn' : j₀ + ((b : ZMod n) + 1) = j₀ + ((a : ZMod n) + 1) + 1 ↔
        (a : ZMod n) + 1 = b := by
      rw [add_assoc j₀, add_right_inj, hnext]
    have hp' : j₀ + ((b : ZMod n) + 1) = j₀ + ((a : ZMod n) + 1) - 1 ↔
        (a : ZMod n) = b + 1 := by
      rw [add_sub_assoc, add_right_inj, hprev]
    simp only [hIntersection, Nat.cast_add, Nat.cast_one, add_right_inj, hn', hp', e]
    simp only [add_left_inj]
    ring
  have hcast (a b : Fin n) : e a b = if a = b then 1 else 0 := by
    have h : ((a : ℕ) : ZMod n) = ((b : ℕ) : ZMod n) ↔ a = b := by
      constructor
      · intro hab
        apply Fin.ext
        simpa only [ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt]
          using congrArg ZMod.val hab
      · rintro rfl
        rfl
    simp only [e, h]
  -- The cycle Gram matrix is the negative pairing of first differences.
  -- Summing first in the second variable and then in the first gives the endpoints.
  have hright (a : ℕ) : B (D (j₀ + ((a + 1 : ℕ) : ZMod n))) (boundaryPrefix D j₀ j) =
      (e a j - e (a + 1) j) - (e a 0 - e (a + 1) 0) := by
    rw [boundaryPrefix, map_sum]
    simp_rw [hdiff]
    exact Finset.sum_range_sub (fun b ↦ e a b - e (a + 1) b) j
  rw [boundaryPrefix, sum_left]
  simp_rw [hright]
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub', Finset.sum_range_sub']
  have h0j : e 0 j = if j = 0 then 1 else 0 := by
    simpa only [Fin.val_zero, eq_comm (a := (0 : Fin n))] using hcast 0 j
  have hi0 : e i 0 = if i = 0 then 1 else 0 := by
    simpa only [Fin.val_zero] using hcast i 0
  have h00 : e 0 0 = 1 := ite_eq_left rfl
  rw [h0j, hi0, hcast, h00]
  ring

/-- The type-A coordinate reversal, expressed via the prefix roots. -/
private def prefixReversal (B : LinearMap.BilinForm ℤ L) (T : Fin n → L) : L →ₗ[ℤ] L :=
  LinearMap.id + ∑ i : Fin n, LinearMap.toSpanSingleton ℤ L (T i - T i.rev) ∘ₗ B.flip (T i)

omit [NeZero n] in
private theorem prefixReversal_apply (T : Fin n → L) (x : L) :
    prefixReversal B T x = x + ∑ i : Fin n, B x (T i) • (T i - T i.rev) := by
  simp [prefixReversal, LinearMap.sum_apply]

private theorem prefixReversal_prefix (T : Fin n → L)
    (hGram : ∀ i j : Fin n, B (T i) (T j) =
      -(if i = j then 1 else 0) + (if i = 0 then 1 else 0) + (if j = 0 then 1 else 0) - 1)
    (j : Fin n) :
    prefixReversal B T (T j) = T j.rev + (T 0 - T (0 : Fin n).rev) := by
  classical
  let R (i : Fin n) := T i - T i.rev
  have hsum : ∑ i : Fin n, R i = 0 := by
    simp only [R, Finset.sum_sub_distrib, Fin.rev_bijective.sum_comp T, sub_self]
  calc
    _ = T j + ∑ i : Fin n, B (T j) (T i) • R i := prefixReversal_apply T _
    _ = T j + (-(R j) + R 0) := by
      simp only [hGram, sub_zsmul, add_zsmul, neg_zsmul, Finset.sum_add_distrib,
        Finset.sum_neg_distrib, hsum, ite_smul, zero_smul, one_smul, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      by_cases hj : j = 0 <;> simp [hj, hsum]
    _ = _ := by dsimp only [R]; abel

omit [NeZero n] in
private theorem prefixReversal_selfAdjoint (T : Fin n → L) (hSymm : B.IsSymm) (x y : L) :
    B (prefixReversal B T x) y = B x (prefixReversal B T y) := by
  simp only [prefixReversal_apply, map_add, map_sum, map_smul, map_sub, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
  congr 1
  have hs (i : Fin n) : B (T i) y = B y (T i) := hSymm.eq _ _
  simp_rw [hs, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  · calc
      _ = ∑ i : Fin n, B x (T i.rev) * B y (T i) := by
        simpa only [Fin.rev_rev, Function.comp_apply] using
          (Fin.rev_bijective.sum_comp fun i ↦ B x (T i) * B y (T i.rev)).symm
      _ = _ := Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

private theorem prefixReversal_involutive (T : Fin n → L)
    (hGram : ∀ i j : Fin n, B (T i) (T j) =
      -(if i = j then 1 else 0) + (if i = 0 then 1 else 0) + (if j = 0 then 1 else 0) - 1) :
    Function.Involutive (prefixReversal B T) := by
  intro x
  have hneg (i : Fin n) : prefixReversal B T (T i - T i.rev) = -(T i - T i.rev) := by
    simp only [map_sub, prefixReversal_prefix T hGram, Fin.rev_rev]
    abel
  rw [prefixReversal_apply T x]
  simp only [map_add, map_sum, map_zsmul, hneg, zsmul_neg, Finset.sum_neg_distrib]
  rw [prefixReversal_apply T x, add_neg_cancel_right]

omit [NeZero n] in
private theorem prefixReversal_eq_of_pairing_zero (T : Fin n → L) {x : L}
    (hx : ∀ i, B x (T i) = 0) :
    prefixReversal B T x = x := by
  simp [prefixReversal_apply, hx]

omit [NeZero n] in
private theorem prefixReversal_eq_self_of_boundary_pairing_eq_zero (j₀ : ZMod n) {x : L}
    (hx : ∀ j, j ≠ j₀ → B x (D j) = 0) :
    prefixReversal B (fun i : Fin n ↦ boundaryPrefix D j₀ i) x = x := by
  apply prefixReversal_eq_of_pairing_zero
  intro i
  let : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)⟩
  simp only [boundaryPrefix, map_sum]
  refine Finset.sum_eq_zero fun k hk ↦ hx _ ?_
  have hk' : k + 1 < n := by
    have := Finset.mem_range.mp hk
    omega
  have hne : ((k + 1 : ℕ) : ZMod n) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    simp only [ZMod.val_natCast_of_lt hk', ZMod.val_zero, Nat.add_one_ne_zero] at hv
  simpa using hne

private theorem prefixReversal_component
    (j₀ j : ZMod n) (hj : j ≠ j₀)
    (hGram : ∀ i j : Fin n, B (boundaryPrefix D j₀ i) (boundaryPrefix D j₀ j) =
      -(if i = j then 1 else 0) + (if i = 0 then 1 else 0) + (if j = 0 then 1 else 0) - 1) :
    prefixReversal B (fun i : Fin n ↦ boundaryPrefix D j₀ i) (D j) = -D (2 * j₀ - j) := by
  have hval : 0 < (j - j₀).val :=
    Nat.pos_of_ne_zero (fun h ↦ hj (sub_eq_zero.mp ((ZMod.val_eq_zero _).mp h)))
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hval.ne'
  have hk' : (j - j₀).val = k + 1 := hk
  have hlt : k + 1 < n := hk' ▸ (j - j₀).val_lt
  have hj' : j = j₀ + ((k + 1 : ℕ) : ZMod n) := by
    rw [← hk', ZMod.natCast_zmod_val]
    abel
  have hindex : 2 * j₀ - (j₀ + ((k + 1 : ℕ) : ZMod n)) =
      j₀ - ((k + 1 : ℕ) : ZMod n) := by ring
  rw [hj', hindex]
  let i : Fin n := ⟨k, by omega⟩
  let j : Fin n := ⟨k + 1, hlt⟩
  have hdiff : D (j₀ + ((k + 1 : ℕ) : ZMod n)) =
      boundaryPrefix D j₀ j - boundaryPrefix D j₀ i := by
    simpa [i, j] using (eq_sub_of_add_eq' (boundaryPrefix_succ (D := D) j₀ k).symm)
  have hrev : (i.rev : ℕ) = (j.rev : ℕ) + 1 := by
    simp only [i, j, Fin.val_rev]
    omega
  have hmod : ((i.rev : ℕ) : ZMod n) = -((k + 1 : ℕ) : ZMod n) := by
    have hval : (i.rev : ℕ) + (k + 1) = n := by
      simp only [i, Fin.val_rev]
      omega
    have h := congrArg (fun a : ℕ ↦ (a : ZMod n)) hval
    exact eq_neg_of_add_eq_zero_left (by simpa using h)
  rw [hdiff, map_sub, prefixReversal_prefix _ hGram, prefixReversal_prefix _ hGram]
  simp only [add_sub_add_right_eq_sub]
  rw [hrev, boundaryPrefix_succ]
  have hcast : (((j.rev : ℕ) + 1 : ℕ) : ZMod n) = -((k + 1 : ℕ) : ZMod n) := by
    rw [← hrev, hmod]
  rw [hcast, ← sub_eq_add_neg]
  abel

/-- The projection onto the plane with Gram matrix `[[0, 1], [1, -1]]`, in the order
`δ, f`. -/
private def boundaryPlaneProjection (B : LinearMap.BilinForm ℤ L) (δ f : L) : L →ₗ[ℤ] L :=
  (LinearMap.toSpanSingleton ℤ L f ∘ₗ B.flip δ) +
    (LinearMap.toSpanSingleton ℤ L δ ∘ₗ (B.flip f + B.flip δ))

omit [NeZero n] in
private theorem boundaryPlaneProjection_apply (δ f x : L) :
    boundaryPlaneProjection B δ f x = B x δ • f + (B x f + B x δ) • δ := by
  simp [boundaryPlaneProjection]

omit [NeZero n] in
private theorem boundaryPlaneProjection_selfAdjoint (δ f : L) (hSymm : B.IsSymm) (x y : L) :
    B (boundaryPlaneProjection B δ f x) y = B x (boundaryPlaneProjection B δ f y) := by
  simp only [boundaryPlaneProjection_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hSymm.eq f y, hSymm.eq δ y]
  ring

private theorem exists_boundary_square_neg_one (hSymm : B.IsSymm)
    (hIntersection : ∀ i j : ZMod n,
      B (D i) (D j) = (-2 : ℤ) * (if i = j then 1 else 0) +
        (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))
    (hCharacteristic : B.IsCharacteristic (∑ i, D i))
    {x : L} (hx : B x (∑ i, D i) = 1) :
    ∃ j₀ : ZMod n, ∃ f : L, B f f = -1 ∧
      ∀ j : ZMod n, B f (D j) = if j = j₀ then 1 else 0 := by
  classical
  let δ := ∑ i, D i
  obtain ⟨j₀, y, hy⟩ := exists_boundary_unit_pairing hIntersection hx
  have hδD (j : ZMod n) : B δ (D j) = 0 := BoundaryCycle.pairing_sum hIntersection j
  have hδδ : B δ δ = 0 := BoundaryCycle.pairing_sum_sum hIntersection
  have hyδ : B y δ = 1 := by simp [δ, hy]
  have heven : Even (B y y - B y δ) := by
    rw [even_iff_two_dvd, dvd_sub_comm, hSymm.eq y δ]
    exact (isCharacteristic_iff.mp hCharacteristic) y
  obtain ⟨a, ha⟩ := heven
  let f := y - (a + 1) • δ
  have hfD (j : ZMod n) : B f (D j) = if j = j₀ then 1 else 0 := by
    simp [f, hδD, hy]
  have hff : B f f = -1 := by
    have hya : B y y - B y δ = a + a := ha
    rw [hyδ] at hya
    simp only [f, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hδδ, hyδ, hSymm.eq δ y, mul_zero, mul_one, sub_zero]
    omega
  exact ⟨j₀, f, hff, hfD⟩

private theorem exists_cycle_reversing_isometry_eq (hSymm : B.IsSymm)
    (hIntersection : ∀ i j : ZMod n,
      B (D i) (D j) = (-2 : ℤ) * (if i = j then 1 else 0) +
        (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))
    {j₀ : ZMod n} {f : L} (hff : B f f = -1)
    (hfD : ∀ j : ZMod n, B f (D j) = if j = j₀ then 1 else 0) :
    let δ := ∑ i, D i
    let P := boundaryPlaneProjection B δ f
    let w := prefixReversal B (fun i : Fin n ↦ boundaryPrefix D j₀ i)
    ∃ g : B.IsometryEquiv B, Function.Involutive g ∧ ∀ z, g z = P z + P z - w z := by
  classical
  let δ := ∑ i, D i
  have hδD (j : ZMod n) : B δ (D j) = 0 := BoundaryCycle.pairing_sum hIntersection j
  have hδδ : B δ δ = 0 := BoundaryCycle.pairing_sum_sum hIntersection
  have hfδ : B f δ = 1 := by simp [δ, hfD]
  have hδf : B δ f = 1 := (hSymm.eq _ _).trans hfδ
  -- Reverse the type-A coordinates of the chain obtained by cutting at j₀.
  let T (i : Fin n) := boundaryPrefix D j₀ i
  have hGram := boundaryPrefix_pairing hIntersection j₀
  let w := prefixReversal B T
  let P := boundaryPlaneProjection B δ f
  have hwδ : w δ = δ :=
    prefixReversal_eq_self_of_boundary_pairing_eq_zero j₀ fun j _ ↦ hδD j
  have hwf : w f = f :=
    prefixReversal_eq_self_of_boundary_pairing_eq_zero j₀ fun j hj ↦ by simp [hfD, hj]
  have hP (z : L) : P z = B z δ • f + (B z f + B z δ) • δ :=
    boundaryPlaneProjection_apply δ f z
  have hPδ : P δ = δ := by simp [hP, hδδ, hδf]
  have hPf : P f = f := by simp [hP, hfδ, hff]
  have hPP (z : L) : P (P z) = P z := by simp [hP z, hPδ, hPf]
  have hwP (z : L) : w (P z) = P z := by simp [hP z, hwδ, hwf]
  have hwAdj (z z' : L) : B (w z) z' = B z (w z') := prefixReversal_selfAdjoint T hSymm _ _
  have hPw (z : L) : P (w z) = P z := by simp [hP, hwAdj, hwδ, hwf]
  have hww : Function.Involutive w := prefixReversal_involutive T hGram
  -- The coordinate reversal fixes the plane pointwise. Subtract it from twice the
  -- orthogonal projection to act as the identity on the plane and as minus w off it.
  let G : L →ₗ[ℤ] L := (2 : ℤ) • P - w
  have hG (z : L) : G z = P z + P z - w z := by simp [G, two_smul]
  have hGG : Function.Involutive G := by
    intro z
    rw [hG z]
    simp only [map_sub, map_add, hG (P z), hG (w z), hPP, hwP, hPw, hww z]
    abel
  have hGAdj (z z' : L) : B (G z) z' = B z (G z') := by
    have hpAdj : B (P z) z' = B z (P z') := boundaryPlaneProjection_selfAdjoint δ f hSymm _ _
    simp only [hG, map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, hwAdj, hpAdj]
  let g : B.IsometryEquiv B :=
    { LinearEquiv.ofInvolutive G hGG with
      map_app' := fun z z' ↦ (hGAdj z (G z')).trans (congrArg (B z) (hGG z')) }
  exact ⟨g, hGG, hG⟩

private theorem exists_cycle_reversing_isometry_of_cut (hSymm : B.IsSymm)
    (hIntersection : ∀ i j : ZMod n,
      B (D i) (D j) = (-2 : ℤ) * (if i = j then 1 else 0) +
        (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))
    {j₀ : ZMod n} {f : L} (hff : B f f = -1)
    (hfD : ∀ j : ZMod n, B f (D j) = if j = j₀ then 1 else 0) :
    ∃ g : B.IsometryEquiv B, Function.Involutive g ∧
      g f = f ∧ g (∑ i : ZMod n, D i) = (∑ i : ZMod n, D i) ∧
      (∀ j : ZMod n, g (D j) = D (2 * j₀ - j)) ∧
      (∀ κ : L, (∀ j : ZMod n, B κ (D j) = 0) →
        g κ = -κ + (2 * B κ f) • (∑ i : ZMod n, D i)) := by
  classical
  let δ := ∑ i, D i
  have hδD (j : ZMod n) : B δ (D j) = 0 := BoundaryCycle.pairing_sum hIntersection j
  have hδδ : B δ δ = 0 := BoundaryCycle.pairing_sum_sum hIntersection
  have hfδ : B f δ = 1 := by simp [δ, hfD]
  have hP (z : L) : boundaryPlaneProjection B (∑ i, D i) f z =
      B z δ • f + (B z f + B z δ) • δ := boundaryPlaneProjection_apply δ f z
  obtain ⟨g, hinv, hg⟩ := exists_cycle_reversing_isometry_eq hSymm hIntersection hff hfD
  have hgδ : g δ = δ := by
    rw [hg, prefixReversal_eq_self_of_boundary_pairing_eq_zero j₀ fun j _ ↦ hδD j]
    simp [hP, hδδ, (hSymm.eq δ f).trans hfδ]
  have hgD (j : ZMod n) (hj : j ≠ j₀) : g (D j) = D (2 * j₀ - j) := by
    have hjδ : B (D j) δ = 0 := (hSymm.eq _ _).trans (hδD j)
    have hjf : B (D j) f = 0 := by rw [hSymm.eq (D j), hfD, ite_eq_right hj]
    rw [hg, prefixReversal_component j₀ j hj (boundaryPrefix_pairing hIntersection j₀)]
    simp [hP, hjδ, hjf]
  -- The total class determines the remaining component once the chain is reversed.
  have hcut : g (D j₀) = D j₀ := by
    let σ : Equiv.Perm (ZMod n) := (Equiv.neg (ZMod n)).trans (Equiv.addLeft (2 * j₀))
    have hσ (j : ZMod n) : σ j = 2 * j₀ - j := by simp [σ, sub_eq_add_neg]
    have hσ₀ : σ j₀ = j₀ := by rw [hσ, two_mul, add_sub_cancel_right]
    have hs : ∑ j : ZMod n, g (D j) = ∑ j : ZMod n, D (σ j) := by
      rw [← map_sum, hgδ]
      exact (Equiv.sum_comp σ D).symm
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j₀),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ j₀), hσ₀] at hs
    have hrest : ∑ j ∈ Finset.univ.erase j₀, g (D j) =
        ∑ j ∈ Finset.univ.erase j₀, D (σ j) :=
      Finset.sum_congr rfl fun j hj ↦
        (hgD j (Finset.ne_of_mem_erase hj)).trans (congrArg D (hσ j).symm)
    rwa [hrest, add_right_inj] at hs
  refine ⟨g, hinv, ?_, hgδ, ?_, ?_⟩
  · rw [hg, prefixReversal_eq_self_of_boundary_pairing_eq_zero j₀
      (fun j hj ↦ by simp [hfD, hj])]
    simp [hP, hfδ, hff]
  · intro j
    by_cases hj : j = j₀
    · simpa [hj, two_mul] using hcut
    · exact hgD j hj
  · intro κ hκ
    have hκδ : B κ δ = 0 := by simp [δ, hκ]
    rw [hg, prefixReversal_eq_self_of_boundary_pairing_eq_zero j₀ (fun j _ ↦ hκ j),
      hP, hκδ]
    simp only [zero_smul, zero_add, add_zero]
    rw [← add_zsmul, two_mul, sub_eq_neg_add]

/-- A primitive characteristic boundary sum in a unimodular symmetric integral lattice admits a
reflection of the cycle. The involution fixes the total class and a square `-1` class that meets
just the component at the cut. On the orthogonal complement of the boundary it is negation
corrected by twice the pairing with that class, in the direction of the boundary sum.

The two neighbor terms are counted separately, also for cycles of length one and two. -/
theorem exists_cycle_reversing_involution
    (L : Type*) [AddCommGroup L] [scalar : Module ℤ L]
    [Module.Free ℤ L] [Module.Finite ℤ L]
    (B : LinearMap.BilinForm ℤ L) [B.IsPerfPair]
    (hSymm : B.IsSymm)
    (n : ℕ) [NeZero n]
    (D : ZMod n → L)
    (hIntersection : ∀ i j : ZMod n,
      B (D i) (D j) =
        (-2 : ℤ) * (if i = j then 1 else 0) +
          (if j = i + 1 then 1 else 0) +
          (if j = i - 1 then 1 else 0))
    (hPrimitive : TauCeti.IsPrimitive (∑ i : ZMod n, D i))
    (hCharacteristic : B.IsCharacteristic (∑ i : ZMod n, D i)) :
    ∃ (j₀ : ZMod n) (f : L) (g : B.IsometryEquiv B),
      B f f = -1 ∧
      (∀ j : ZMod n, B f (D j) = if j = j₀ then 1 else 0) ∧
      Function.Involutive g ∧
      g f = f ∧
      g (∑ i : ZMod n, D i) = (∑ i : ZMod n, D i) ∧
      (∀ j : ZMod n, g (D j) = D (2 * j₀ - j)) ∧
      (∀ κ : L, κ ∈ B.orthogonal (Submodule.span ℤ (Set.range D)) →
        g κ = -κ + (2 * B κ f) • (∑ i : ZMod n, D i)) := by
  classical
  -- Use the canonical integer action for arithmetic with lattice vectors.
  have hscalar : scalar = (AddCommGroup.uniqueIntModule (M := L)).default := Subsingleton.elim _ _
  subst scalar
  obtain ⟨ℓ, hℓ⟩ := TauCeti.isPrimitive_def.mp hPrimitive
  have hx : B (B.toPerfPair.symm ℓ) (∑ i, D i) = 1 := by
    rw [B.apply_symm_toPerfPair_self, hℓ]
  obtain ⟨j₀, f, hff, hfD⟩ := exists_boundary_square_neg_one hSymm hIntersection hCharacteristic hx
  obtain ⟨g, hinv, hfix, hsum, hboundary, horthogonal⟩ :=
    exists_cycle_reversing_isometry_of_cut hSymm hIntersection hff hfD
  refine ⟨j₀, f, g, hff, hfD, hinv, hfix, hsum, hboundary, fun x hx ↦ horthogonal x ?_⟩
  intro j
  rw [hSymm.eq]
  exact B.mem_orthogonal_iff.mp hx _ (Submodule.subset_span (Set.mem_range_self j))

end QPainleve
