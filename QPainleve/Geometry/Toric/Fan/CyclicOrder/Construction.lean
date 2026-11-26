/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import QPainleve.Geometry.Toric.Fan.Ray

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Order.Fin.Basic
import QPainleve.Analysis.SpecialFunctions.Trigonometric.Basic
import QPainleve.Geometry.Toric.Cone.TwoDimensional
import QPainleve.Order.Sequence
import TauCeti.Geometry.Toric.Algebraic.Ray.Face

/-!
# Constructing a regular complete fan from cyclic ray coordinates

Consecutive determinant-one pairs in a list winding once around the origin give the
two-dimensional cones of a complete fan. The winding condition counts the positive
horizontal axis crossings. Cutting the list at its unique crossing orders the
arguments of the rays and shows that the cones cover the plane and meet in faces.
The winding criterion comes from the [signed cluster modular group comparator challenge][challenge].

[challenge]: https://github.com/q-painleve-lean/QPainleve/pull/841
-/

open Module PointedCone

namespace TauCeti.Toric.Fan

private noncomputable def asComplex : (Fin 2 → ℝ) ≃ₗ[ℝ] ℂ :=
  (LinearEquiv.finTwoArrow ℝ ℝ).trans Complex.equivRealProdLm.symm

private theorem asComplex_ne_zero {x : Fin 2 → ℝ} (hx : x ≠ 0) : asComplex x ≠ 0 :=
  (map_ne_zero_iff _ asComplex.injective).mpr hx

private noncomputable def polarAngle (x : Fin 2 → ℝ) : ℝ :=
  (asComplex x).arg + if x 1 < 0 then 2 * Real.pi else 0

private theorem polarAngle_bounds (x : Fin 2 → ℝ) :
    0 ≤ polarAngle x ∧ polarAngle x < 2 * Real.pi := by
  by_cases h : x 1 < 0
  · have ha : (asComplex x).arg < 0 := Complex.arg_neg_iff.mpr h
    simp only [polarAngle, ite_eq_left h]
    constructor <;> linarith [Complex.neg_pi_lt_arg (asComplex x), Real.pi_pos]
  · have ha : 0 ≤ (asComplex x).arg := Complex.arg_nonneg_iff.mpr (le_of_not_gt h)
    simp only [polarAngle, ite_eq_right h, add_zero]
    exact ⟨ha, by linarith [Complex.arg_le_pi (asComplex x), Real.pi_pos]⟩

private theorem polarAngle_le_pi_iff (x : Fin 2 → ℝ) : polarAngle x ≤ Real.pi ↔ 0 ≤ x 1 := by
  by_cases h : x 1 < 0
  · have harg := Complex.neg_pi_lt_arg (asComplex x)
    simp only [polarAngle, ite_eq_left h, not_le.mpr h, iff_false, not_le]
    linarith
  · simp [polarAngle, h, le_of_not_gt h, Complex.arg_le_pi]

private theorem norm_mul_cos_polarAngle (x : Fin 2 → ℝ) :
    ‖asComplex x‖ * Real.cos (polarAngle x) = x 0 := by
  have hre : (asComplex x).re = x 0 := rfl
  unfold polarAngle
  split <;> simpa only [hre, Real.cos_add_two_pi, add_zero] using
    (Complex.norm_mul_cos_arg (asComplex x) : _ = (asComplex x).re)

private theorem norm_mul_sin_polarAngle (x : Fin 2 → ℝ) :
    ‖asComplex x‖ * Real.sin (polarAngle x) = x 1 := by
  have him : (asComplex x).im = x 1 := rfl
  unfold polarAngle
  split <;> simpa only [him, Real.sin_add_two_pi, add_zero] using
    (Complex.norm_mul_sin_arg (asComplex x) : _ = (asComplex x).im)

private theorem eq_pos_smul_of_polarAngle_eq {x y : Fin 2 → ℝ} (hy : y ≠ 0)
    (hx : x ≠ 0) (h : polarAngle x = polarAngle y) :
    ∃ c : ℝ, 0 < c ∧ x = c • y := by
  have hhalf : x 1 < 0 ↔ y 1 < 0 := by
    apply lt_iff_lt_of_le_iff_le
    rw [← polarAngle_le_pi_iff, ← polarAngle_le_pi_iff, h]
  have harg : (asComplex y).arg = (asComplex x).arg := by
    symm
    by_cases hx' : x 1 < 0
    · simpa [polarAngle, hx', hhalf.mp hx'] using h
    · have hy' : ¬ y 1 < 0 := fun hy' ↦ hx' (hhalf.mpr hy')
      simpa [polarAngle, hx', hy'] using h
  refine ⟨_, div_pos (norm_pos_iff.mpr (asComplex_ne_zero hx))
    (norm_pos_iff.mpr (asComplex_ne_zero hy)), asComplex.injective ?_⟩
  rw [map_smul, Complex.real_smul, Complex.ofReal_div, eq_comm]
  exact (Complex.arg_eq_arg_iff (asComplex_ne_zero hy) (asComplex_ne_zero hx)).mp harg

local notation "det₂" => Module.Basis.detDualEquiv (Pi.basisFun _ (Fin 2))

private theorem det₂_eq_sin (x y : Fin 2 → ℝ) :
    det₂ x y = (‖asComplex x‖ * ‖asComplex y‖) *
      Real.sin (polarAngle y - polarAngle x) := by
  rw [Real.sin_sub]
  simp only [Basis.detDualEquiv_pi_basisFun]
  rw [← norm_mul_cos_polarAngle x, ← norm_mul_sin_polarAngle x,
    ← norm_mul_cos_polarAngle y, ← norm_mul_sin_polarAngle y]
  ring

private theorem polarAngle_step {x y : Fin 2 → ℝ} (hxy : 0 < det₂ x y) :
    if x 1 < 0 ∧ 0 ≤ y 1 then
      0 < polarAngle y + 2 * Real.pi - polarAngle x ∧
        polarAngle y + 2 * Real.pi - polarAngle x < Real.pi
    else
      0 < polarAngle y - polarAngle x ∧ polarAngle y - polarAngle x < Real.pi := by
  rw [det₂_eq_sin] at hxy
  have hs := pos_of_mul_pos_right hxy (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hx := polarAngle_bounds x
  have hy := polarAngle_bounds y
  by_cases hyx : polarAngle y < polarAngle x
  · have hsin : 0 < Real.sin (polarAngle y + 2 * Real.pi - polarAngle x) := by
      rwa [add_sub_right_comm, Real.sin_add_two_pi]
    have hgap :=
      (Real.sin_pos_iff_of_nonneg_of_lt_two_pi (by linarith [hy.1]) (by linarith)).mp hsin
    have h₁ : Real.pi < polarAngle x := by linarith [hy.1, hgap.2]
    have h₂ : polarAngle y ≤ Real.pi := by linarith [hx.2, hgap.2]
    have hx' : x 1 < 0 := lt_of_not_ge fun h ↦ h₁.not_ge ((polarAngle_le_pi_iff x).mpr h)
    simp [hx', (polarAngle_le_pi_iff y).mp h₂, hgap]
  · have hgap :=
      (Real.sin_pos_iff_of_nonneg_of_lt_two_pi (by linarith) (by linarith [hx.1, hy.2])).mp hs
    have hn : ¬ (x 1 < 0 ∧ 0 ≤ y 1) := fun ⟨hx', hy'⟩ ↦
      ((polarAngle_le_pi_iff x).not.mpr hx'.not_ge)
        ((le_of_not_gt hyx).trans ((polarAngle_le_pi_iff y).mpr hy'))
    simp [hn, hgap]

private theorem det₂_nonneg_iff_mem_angleInterval {x y v : Fin 2 → ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hv : v ≠ 0) {a b : ℝ}
    (ha : a = polarAngle x) (hb : b = polarAngle y ∨ b = polarAngle y + 2 * Real.pi)
    (hab : 0 < b - a ∧ b - a < Real.pi) :
    0 ≤ det₂ x v ∧ 0 ≤ det₂ v y ↔
      ∃ t : ℝ, (t = polarAngle v ∨ t = polarAngle v + 2 * Real.pi) ∧ a ≤ t ∧ t ≤ b := by
  have hn : ∀ w : Fin 2 → ℝ, w ≠ 0 → 0 < ‖asComplex w‖ :=
    fun w hn ↦ norm_pos_iff.mpr (asComplex_ne_zero hn)
  -- Lift the direction into the full turn starting at the first ray.
  let t := if polarAngle v < a then polarAngle v + 2 * Real.pi else polarAngle v
  have ht : t = polarAngle v ∨ t = polarAngle v + 2 * Real.pi := by
    unfold t
    split <;> simp
  have hta : a ≤ t ∧ t < a + 2 * Real.pi := by
    have hx' := polarAngle_bounds x
    have hv' := polarAngle_bounds v
    unfold t
    split <;> constructor <;> linarith
  have hsin₁ (s : ℝ) (hs : s = polarAngle v ∨ s = polarAngle v + 2 * Real.pi) :
      Real.sin (s - a) = Real.sin (polarAngle v - polarAngle x) := by
    rcases hs with rfl | rfl <;> simp [ha, add_sub_right_comm, Real.sin_add_two_pi]
  have hsin₂ (s : ℝ) (hs : s = polarAngle v ∨ s = polarAngle v + 2 * Real.pi) :
      Real.sin (b - s) = Real.sin (polarAngle y - polarAngle v) := by
    rcases hb with rfl | rfl <;> rcases hs with rfl | rfl <;>
      simp [add_sub_right_comm, sub_add_eq_sub_sub, Real.sin_add_two_pi, Real.sin_sub_two_pi]
  rw [det₂_eq_sin, det₂_eq_sin, mul_nonneg_iff_of_pos_left (mul_pos (hn _ hx) (hn _ hv)),
    mul_nonneg_iff_of_pos_left (mul_pos (hn _ hv) (hn _ hy))]
  constructor
  · rw [← hsin₁ t ht, ← hsin₂ t ht]
    rintro ⟨hs, hs'⟩
    have hπ := (Real.sin_nonneg_iff_of_nonneg_of_lt_two_pi (by linarith [hta.1])
      (by linarith [hta.2])).mp hs
    exact ⟨t, ht, hta.1, le_of_not_gt fun h ↦
      (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith [hab.1])).not_ge hs'⟩
  · rintro ⟨s, hs, has, hsb⟩
    rw [← hsin₁ s hs, ← hsin₂ s hs]
    constructor <;> apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith [hab.2]

private abbrev latticeInclusion := AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin 2)

local notation "adjacentCone" => fun (x y : Fin 2 → ℝ) ↦ hull ℝ (Set.range ![x, y])

section Unroll

variable {r : ℕ} [NeZero r]

private def cycleIndex (start : ZMod r) (k : ℕ) : ZMod r := (k : ZMod r) + start

omit [NeZero r] in
private theorem cycleIndex_succ (start : ZMod r) (k : ℕ) :
    cycleIndex start (k + 1) = cycleIndex start k + 1 := by
  simp [cycleIndex, Nat.cast_succ, add_right_comm]

omit [NeZero r] in
private theorem cycleIndex_end (start : ZMod r) : cycleIndex start r = start := by
  simp [cycleIndex]

omit [NeZero r] in
private theorem cycleIndex_eq_iff_of_lt {start : ZMod r} {k l : ℕ}
    (hk : k < r) (hl : l < r) : cycleIndex start k = cycleIndex start l ↔ k = l := by
  simp only [cycleIndex, add_left_inj]
  constructor
  · intro h
    simpa only [ZMod.val_natCast_of_lt hk, ZMod.val_natCast_of_lt hl] using
      congrArg ZMod.val h
  · exact congrArg (Nat.cast : ℕ → ZMod r)

private theorem exists_cycleIndex (start j : ZMod r) :
    ∃ k < r, cycleIndex start k = j :=
  ⟨(j - start).val, ZMod.val_lt _, by simp [cycleIndex]⟩

private noncomputable def unrolledAngle (v : ZMod r → Fin 2 → ℝ) (start : ZMod r) (k : ℕ) : ℝ :=
  if k < r then polarAngle (v (cycleIndex start k)) else polarAngle (v start) + 2 * Real.pi

private theorem unrolledAngle_zero (v : ZMod r → Fin 2 → ℝ) (start : ZMod r) :
    unrolledAngle v start 0 = polarAngle (v start) := by
  simp [unrolledAngle, cycleIndex, NeZero.pos r]

omit [NeZero r] in
private theorem unrolledAngle_lt {v : ZMod r → Fin 2 → ℝ} {start : ZMod r} {k : ℕ} (hk : k < r) :
    unrolledAngle v start k = polarAngle (v (cycleIndex start k)) := by
  simp [unrolledAngle, hk]

private theorem unrolledAngle_end (v : ZMod r → Fin 2 → ℝ) (start : ZMod r) :
    unrolledAngle v start r = unrolledAngle v start 0 + 2 * Real.pi := by
  simp [unrolledAngle, cycleIndex, NeZero.pos r]

private theorem unrolledAngle_succ {v : ZMod r → Fin 2 → ℝ} {start : ZMod r} {k : ℕ} (hk : k < r) :
    unrolledAngle v start (k + 1) = polarAngle (v (cycleIndex start k + 1)) ∨
      unrolledAngle v start (k + 1) = polarAngle (v (cycleIndex start k + 1)) + 2 * Real.pi := by
  by_cases hs : k + 1 < r
  · exact Or.inl (by rw [unrolledAngle_lt hs, cycleIndex_succ])
  · have hkr : k + 1 = r := by omega
    rw [← cycleIndex_succ, hkr, cycleIndex_end, unrolledAngle_end, unrolledAngle_zero]
    exact Or.inr rfl

private theorem unrolledAngle_step {v : ZMod r → Fin 2 → ℝ}
    (hdet : ∀ j, 0 < det₂ (v j) (v (j + 1))) {start : ZMod r}
    (hc : ∀ j, (v j 1 < 0 ∧ 0 ≤ v (j + 1) 1) ↔ j + 1 = start) {k : ℕ} (hk : k < r) :
    0 < unrolledAngle v start (k + 1) - unrolledAngle v start k ∧
      unrolledAngle v start (k + 1) - unrolledAngle v start k < Real.pi := by
  have h := polarAngle_step (hdet (cycleIndex start k))
  rw [unrolledAngle_lt hk]
  by_cases hs : k + 1 < r
  · have hn : cycleIndex start (k + 1) ≠ start := by
      intro he
      have he' : cycleIndex start (k + 1) = cycleIndex start 0 := by
        simpa [cycleIndex] using he
      exact Nat.succ_ne_zero k ((cycleIndex_eq_iff_of_lt hs (NeZero.pos r)).mp he')
    have hnc : ¬ (v (cycleIndex start k) 1 < 0 ∧ 0 ≤ v (cycleIndex start k + 1) 1) :=
      fun hh ↦ hn (by simpa only [cycleIndex_succ] using (hc _).mp hh)
    rw [ite_eq_right hnc] at h
    simpa only [← cycleIndex_succ, unrolledAngle_lt hs] using h
  · have hkr : k + 1 = r := by omega
    have hend : cycleIndex start k + 1 = start := by rw [← cycleIndex_succ, hkr, cycleIndex_end]
    rw [ite_eq_left ((hc _).mpr hend)] at h
    simpa only [hend, hkr, unrolledAngle_end,
      unrolledAngle_zero] using h

private theorem unrolledAngle_strictMonoOn {v : ZMod r → Fin 2 → ℝ}
    (hdet : ∀ j, 0 < det₂ (v j) (v (j + 1))) {start : ZMod r}
    (hc : ∀ j, (v j 1 < 0 ∧ 0 ≤ v (j + 1) 1) ↔ j + 1 = start) :
    StrictMonoOn (unrolledAngle v start) (Set.Iic r) := by
  have hmono : StrictMono (fun j : Fin (r + 1) ↦ unrolledAngle v start j) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro j
    exact sub_pos.mp (unrolledAngle_step hdet hc j.isLt).1
  intro a ha b hb hab
  let i : Fin (r + 1) := ⟨a, Nat.lt_succ_of_le ha⟩
  let j : Fin (r + 1) := ⟨b, Nat.lt_succ_of_le hb⟩
  exact hmono (a := i) (b := j) hab

omit [NeZero r] in
private theorem endpoint_of_two_angleIntervals {θ : ℕ → ℝ}
    (hmono : MonotoneOn θ (Set.Iic r)) (hperiod : θ r = θ 0 + 2 * Real.pi)
    {k l : ℕ} (hk : k < r) (hl : l < r) (hne : k ≠ l)
    {s t a : ℝ} (hs : s = a ∨ s = a + 2 * Real.pi) (ht : t = a ∨ t = a + 2 * Real.pi)
    (hks : θ k ≤ s ∧ s ≤ θ (k + 1)) (hlt : θ l ≤ t ∧ t ≤ θ (l + 1)) :
    s = θ k ∨ s = θ (k + 1) := by
  have hle {i j : ℕ} (hj : j ≤ r) (hij : i ≤ j) : θ i ≤ θ j :=
    hmono (hij.trans hj) hj hij
  rcases eq_or_ne s t with rfl | hst
  · rcases lt_or_gt_of_ne hne with hkl | hlk
    · exact Or.inr (hks.2.antisymm ((hle hl.le (by omega)).trans hlt.1))
    · exact Or.inl (le_antisymm (hlt.2.trans (hle hk.le (by omega))) hks.1)
  · -- Two distinct lifts differ by one turn, so they lie at opposite ends of the cut.
    have hsb : θ 0 ≤ s ∧ s ≤ θ r :=
      ⟨(hle hk.le (Nat.zero_le _)).trans hks.1, hks.2.trans (hle le_rfl (by omega))⟩
    have htb : θ 0 ≤ t ∧ t ≤ θ r :=
      ⟨(hle hl.le (Nat.zero_le _)).trans hlt.1, hlt.2.trans (hle le_rfl (by omega))⟩
    rcases hs with rfl | rfl <;> rcases ht with ht | ht
    · exact (hst ht.symm).elim
    · exact Or.inl (by linarith [hks.1, hsb.1, htb.2, hle hk.le (Nat.zero_le k)])
    · have hk' : k + 1 ≤ r := by omega
      exact Or.inr (by linarith [hks.2, hsb.2, htb.1, hle le_rfl hk'])
    · exact (hst ht.symm).elim

variable {v : ZMod r → Fin 2 → ℝ} {start : ZMod r}
  (hdet : ∀ j, det₂ (v j) (v (j + 1)) = 1)
  (hc : ∀ j, (v j 1 < 0 ∧ 0 ≤ v (j + 1) 1) ↔ j + 1 = start)

include hdet hc

omit [NeZero r] hc in
private theorem linearIndependent_consecutive (j : ZMod r) :
    LinearIndependent ℝ ![v j, v (j + 1)] :=
  ((Pi.basisFun ℝ (Fin 2)).is_basis_iff_det.mpr
    (by rw [← Basis.detDualEquiv_apply, hdet j]; exact isUnit_one)).1

private theorem mem_adjacentCone_iff_exists_angle {k : ℕ} (hk : k < r)
    {x : Fin 2 → ℝ} (hx : x ≠ 0) :
    x ∈ adjacentCone (v (cycleIndex start k)) (v (cycleIndex start k + 1)) ↔
      ∃ t : ℝ, (t = polarAngle x ∨ t = polarAngle x + 2 * Real.pi) ∧
        unrolledAngle v start k ≤ t ∧ t ≤ unrolledAngle v start (k + 1) := by
  have h := hdet (cycleIndex start k)
  rw [mem_hull_pair_iff_detDualEquiv_nonneg (h.symm ▸ zero_lt_one)]
  have hind := linearIndependent_consecutive hdet (cycleIndex start k)
  exact det₂_nonneg_iff_mem_angleInterval (hind.ne_zero 0) (hind.ne_zero 1)
    hx (unrolledAngle_lt hk) (unrolledAngle_succ hk)
    (unrolledAngle_step (fun j ↦ (hdet j).symm ▸ zero_lt_one) hc hk)

private theorem exists_mem_adjacentCone (x : Fin 2 → ℝ) :
    ∃ j, x ∈ adjacentCone (v j) (v (j + 1)) := by
  by_cases hx : x = 0
  · exact ⟨0, hx.symm ▸ Submodule.zero_mem _⟩
  let θ := unrolledAngle v start
  have hperiod : θ r = θ 0 + 2 * Real.pi := unrolledAngle_end v start
  have h₀ : θ 0 = polarAngle (v start) := unrolledAngle_zero v start
  have hangle : ∃ t, (t = polarAngle x ∨ t = polarAngle x + 2 * Real.pi) ∧ θ 0 ≤ t ∧ t ≤ θ r := by
    have ⟨hx₀, hx₂⟩ := polarAngle_bounds x
    have ⟨hv₀, hv₂⟩ := polarAngle_bounds (v start)
    by_cases h : polarAngle x < θ 0
    · exact ⟨_, Or.inr rfl, by linarith, by linarith⟩
    · exact ⟨_, Or.inl rfl, by linarith, by linarith⟩
  obtain ⟨t, ht, ht₀, htr⟩ := hangle
  obtain ⟨k, hk, hkt, htk⟩ := QPainleve.exists_le_le_succ_of_le_endpoints (NeZero.pos r) ht₀ htr
  exact ⟨cycleIndex start k, (mem_adjacentCone_iff_exists_angle hdet hc hk hx).2 ⟨t, ht, hkt, htk⟩⟩

private theorem angle_eq_endpoint_of_mem_two_adjacentCones {j l : ZMod r} (hne : j ≠ l)
    {x : Fin 2 → ℝ} (hx : x ≠ 0) (hj : x ∈ adjacentCone (v j) (v (j + 1)))
    (hl : x ∈ adjacentCone (v l) (v (l + 1))) :
    polarAngle x = polarAngle (v j) ∨ polarAngle x = polarAngle (v (j + 1)) := by
  obtain ⟨k, hk, rfl⟩ := exists_cycleIndex start j
  obtain ⟨m, hm, rfl⟩ := exists_cycleIndex start l
  obtain ⟨s, hs, hs₁, hs₂⟩ := (mem_adjacentCone_iff_exists_angle hdet hc hk hx).mp hj
  obtain ⟨t, ht, ht₁, ht₂⟩ := (mem_adjacentCone_iff_exists_angle hdet hc hm hx).mp hl
  have hmono := unrolledAngle_strictMonoOn (fun j ↦ (hdet j).symm ▸ zero_lt_one) hc
  have hθ := endpoint_of_two_angleIntervals hmono.monotoneOn (unrolledAngle_end v start)
    hk hm (fun h ↦ hne (congrArg _ h)) hs ht ⟨hs₁, hs₂⟩ ⟨ht₁, ht₂⟩
  have huniq {a b s : ℝ} (ha : a ∈ Set.Ico 0 (2 * Real.pi)) (hb : b ∈ Set.Ico 0 (2 * Real.pi))
      (h₁ : s = a ∨ s = a + 2 * Real.pi) (h₂ : s = b ∨ s = b + 2 * Real.pi) : a = b := by
    rcases ha with ⟨ha₀, ha₂⟩
    rcases hb with ⟨hb₀, hb₂⟩
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> linarith
  rcases hθ with hθ | hθ
  · exact Or.inl (huniq (polarAngle_bounds x) (polarAngle_bounds _) hs
      (Or.inl (hθ.trans (unrolledAngle_lt hk))))
  · exact Or.inr (huniq (polarAngle_bounds x) (polarAngle_bounds _) hs
      ((unrolledAngle_succ hk).imp (hθ.trans ·) (hθ.trans ·)))

private theorem inf_adjacentCone_isFaceOf (j l : ZMod r) :
    (adjacentCone (v j) (v (j + 1)) ⊓ adjacentCone (v l) (v (l + 1))).IsFaceOf
      (adjacentCone (v j) (v (j + 1))) := by
  by_cases hjl : j = l
  · subst l
    simp only [inf_idem]
    exact IsFaceOf.refl _
  let w := ![v j, v (j + 1)]
  let C := adjacentCone (v j) (v (j + 1))
  let D := adjacentCone (v l) (v (l + 1))
  -- The intersection is generated by the endpoints of the first cone that lie in the second.
  let A := {a : Fin 2 | w a ∈ D}
  have hf := isFaceOf_hull_image (linearIndependent_consecutive hdet j) (C := C) rfl A
  suffices he : C ⊓ D = hull ℝ (w '' A) from he.symm ▸ hf
  refine le_antisymm (fun x hx ↦ ?_)
    (Submodule.span_le.mpr (by rintro _ ⟨a, ha, rfl⟩; exact ⟨subset_hull ⟨a, rfl⟩, ha⟩))
  by_cases h₀ : x = 0
  · exact h₀.symm ▸ Submodule.zero_mem _
  have hangle := angle_eq_endpoint_of_mem_two_adjacentCones hdet hc hjl h₀ hx.1 hx.2
  have hind := linearIndependent_consecutive hdet j
  have hmem (a : Fin 2) (ha : w a ≠ 0) (he : polarAngle x = polarAngle (w a)) :
      x ∈ hull ℝ (w '' A) := by
    obtain ⟨c, hc, hcx⟩ := eq_pos_smul_of_polarAngle_eq ha h₀ he
    have hw : w a ∈ D := by
      have hp := D.smul_mem (inv_nonneg.mpr hc.le) hx.2
      simpa [hcx, smul_smul, inv_mul_cancel₀ hc.ne'] using hp
    rw [hcx]
    exact (hull ℝ (w '' A)).smul_mem hc.le (subset_hull ⟨a, hw, rfl⟩)
  exact hangle.elim (hmem 0 (hind.ne_zero 0)) (hmem 1 (hind.ne_zero 1))

private theorem injective_of_unrolledAngles : Function.Injective v := by
  have hmono := unrolledAngle_strictMonoOn (fun j ↦ (hdet j).symm ▸ zero_lt_one) hc
  intro a b hab
  obtain ⟨k, hk, rfl⟩ := exists_cycleIndex start a
  obtain ⟨l, hl, rfl⟩ := exists_cycleIndex start b
  have he := hmono.injOn hk.le hl.le (by rw [unrolledAngle_lt hk, unrolledAngle_lt hl, hab])
  exact congrArg (cycleIndex start) he

end Unroll

private theorem primitiveGenerator_eq_of_isFaceOf_adjacentCone {Φ : Fan latticeInclusion}
    (a : Φ.Ray) {x y : Fin 2 → ℤ}
    (hxy : LinearIndependent ℝ ![latticeInclusion x, latticeInclusion y])
    (hx : IsPrimitive x) (hy : IsPrimitive y)
    (ha : a.toCone.val.IsFaceOf (adjacentCone (latticeInclusion x) (latticeInclusion y))) :
    a.primitiveGenerator = x ∨ a.primitiveGenerator = y := by
  let w := ![latticeInclusion x, latticeInclusion y]
  let ρ : ToricRay (adjacentCone (latticeInclusion x) (latticeInclusion y)) :=
    ⟨⟨a.toCone.val, ha⟩, a.property⟩
  let m := toricRayEquivOfLinearIndependent w hxy rfl ρ
  have hm : w m ∈ a.toCone.val := by
    exact (apply_mem_iff_toricRayEquivOfLinearIndependent w
      hxy rfl ρ m).2 rfl
  have hcases : ∀ j : Fin 2, j = 0 ∨ j = 1 :=
    Fin.forall_fin_two.mpr ⟨Or.inl rfl, Or.inr rfl⟩
  rcases hcases m with he | he
  · exact Or.inl (a.primitiveGenerator_eq_of_mem_of_isPrimitive
      (by simpa [he, w] using hm) hx)
  · exact Or.inr (a.primitiveGenerator_eq_of_mem_of_isPrimitive
      (by simpa [he, w] using hm) hy)

public section

/-- A cyclic list of integral vectors with consecutive determinant one and a single crossing
from the lower half-plane to the closed upper half-plane is the positively ordered ray list of
a regular complete fan. Its ray equivalence retains the input numbering, and consecutive rays
span a cone of the fan. -/
theorem exists_fan_of_cyclic_rays {r : ℕ} [NeZero r] (u : ZMod r → Fin 2 → ℤ)
    (hdet : ∀ j, (Pi.basisFun ℤ (Fin 2)).detDualEquiv (u j) (u (j + 1)) = 1)
    (hwind : (Finset.univ.filter fun j ↦ u j 1 < 0 ∧ 0 ≤ u (j + 1) 1).card = 1) :
    ∃ Φ : Fan (AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin 2)),
      Φ.IsRegular ∧ Φ.IsComplete ∧ ∃ e : ZMod r ≃ Φ.Ray,
        (∀ j, (e j).primitiveGenerator = u j) ∧
        ∀ j, (e j).toCone.val ⊔ (e (j + 1)).toCone.val ∈ Φ.cones := by
  classical
  let v := latticeInclusion ∘ u
  have hℝ (j : ZMod r) : det₂ (v j) (v (j + 1)) = 1 := by
    change det₂ (Int.castRingHom ℝ ∘ u j) (Int.castRingHom ℝ ∘ u (j + 1)) = 1
    rw [(Int.castRingHom ℝ).map_detDualEquiv_pi_basisFun, hdet, map_one]
  obtain ⟨cut, hcut⟩ := Finset.card_eq_one.mp hwind
  have hc (j : ZMod r) : (v j 1 < 0 ∧ 0 ≤ v (j + 1) 1) ↔ j + 1 = cut + 1 := by
    have h := Finset.ext_iff.mp hcut j
    simpa [v, latticeInclusion] using h
  let K := fun j : ZMod r ↦ adjacentCone (v j) (v (j + 1))
  have hreg : ∀ ⦃σ⦄, σ ∈ Set.range K → IsRegularCone latticeInclusion σ := by
    rintro _ ⟨j, rfl⟩
    apply isRegularCone_hull_pair_of_isUnit_det (isIntegralLattice_intCast 2)
      (Pi.basisFun ℤ (Fin 2))
    rw [← Basis.detDualEquiv_apply, hdet]
    exact isUnit_one
  let Φ := Fan.ofCones (isIntegralLattice_intCast 2) (Set.range K) (Set.finite_range K)
    (fun _ h ↦ (hreg h).toIsToricCone)
    (by rintro _ _ ⟨j, rfl⟩ ⟨k, rfl⟩; exact inf_adjacentCone_isFaceOf hℝ hc j k)
  have hK (j : ZMod r) : K j ∈ Φ.cones := (Fan.mem_ofCones_cones ..).2
    ⟨K j, Set.mem_range_self j, IsFaceOf.refl _⟩
  have hp (j : ZMod r) : IsPrimitive (u j) :=
    (Pi.basisFun ℤ (Fin 2)).isPrimitive_of_detDualEquiv_eq_one (hdet j)
  let q (j : ZMod r) : Φ.Ray := Ray.ofPrimitiveGenerator (hp j)
    (Φ.mem_of_isFaceOf (hK j) (isFaceOf_hull_pair_left (linearIndependent_consecutive hℝ j)))
  have hq (j : ZMod r) : (q j).primitiveGenerator = u j :=
    Ray.primitiveGenerator_ofPrimitiveGenerator ..
  have hsurj : Function.Surjective q := by
    intro a
    obtain ⟨_, ⟨j, rfl⟩, ha⟩ := (Fan.mem_ofCones_cones ..).1 a.toCone.property
    rcases primitiveGenerator_eq_of_isFaceOf_adjacentCone a (linearIndependent_consecutive hℝ j)
      (hp j) (hp (j + 1)) ha with h | h
    · exact ⟨j, Ray.primitiveGenerator_injective ((hq j).trans h.symm)⟩
    · exact ⟨j + 1, Ray.primitiveGenerator_injective ((hq (j + 1)).trans h.symm)⟩
  let e := Equiv.ofBijective q ⟨fun a b hab ↦ injective_of_unrolledAngles hℝ hc (by
    have he : u a = u b := (hq a).symm.trans ((congrArg Ray.primitiveGenerator hab).trans (hq b))
    simp only [v, Function.comp_apply, he]), hsurj⟩
  refine ⟨Φ, (Fan.isRegular_ofCones_iff ..).mpr (fun _ h ↦ hreg h), ?_, e, hq, ?_⟩
  · apply Φ.isComplete_iff.mpr
    intro x
    obtain ⟨j, hx⟩ := exists_mem_adjacentCone hℝ hc x
    exact ⟨K j, hK j, hx⟩
  · intro j
    have he₀ : (e j).toCone.val = hull ℝ {v j} := Ray.ofPrimitiveGenerator_toCone ..
    have he₁ : (e (j + 1)).toCone.val = hull ℝ {v (j + 1)} := Ray.ofPrimitiveGenerator_toCone ..
    rw [he₀, he₁, hull, hull, ← Submodule.span_union]
    simpa [K, hull, Matrix.range_cons] using hK j

end

end TauCeti.Toric.Fan
