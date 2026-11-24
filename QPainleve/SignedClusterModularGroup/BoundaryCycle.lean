/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import TauCeti.Algebra.Module.Primitive
import Mathlib.Algebra.Ring.Periodic
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.BilinearForm.BaseChange
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Index
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA.Basic
import TauCeti.LinearAlgebra.TensorProduct.Kernel

/-!
# Boundary cycles in bilinear lattices

A cycle of boundary classes has the negative cycle Laplacian as its Gram matrix, with
both incidences counted when the cycle has length one or two. Its total class generates
the radical of the boundary span. If this class satisfies Tau Ceti's `IsPrimitive`, the
saturation quotient embeds into the additive group of `ZMod n` via the weighted sum of
the component degrees.
The boundary form makes the image square-zero. In the type-A discriminant group this gives an
integral overlattice, whose index square divides `n` by the discriminant formula.
The radical calculation gives the rational orthogonal decomposition via Tau Ceti's
`LinearMap.BilinForm.orthogonal_inf` and `LinearMap.ker_baseChange_of_flat`.
-/

public section

open LinearMap

namespace QPainleve.BoundaryCycle

variable {n : ℕ} [NeZero n]

private theorem eq_zero_index_of_add_one {A : Type*} (a : ZMod n → A)
    (ha : ∀ i, a (i + 1) = a i) (i : ZMod n) : a i = a 0 := by
  have h : Function.Periodic a 1 := ha
  simpa only [mul_one, ZMod.natCast_zmod_val] using h.nat_mul_eq i.val

private theorem sum_sub_prev {A : Type*} [AddCommGroup A] (a : ZMod n → A) :
    ∑ i, (a i - a (i - 1)) = 0 := by
  have h : ∑ i : ZMod n, a (i - 1) = ∑ i, a i :=
    Equiv.sum_comp (Equiv.subRight (1 : ZMod n)) a
  rw [Finset.sum_sub_distrib, h, sub_self]

section IntegralGram

variable {L : Type*} [AddCommGroup L] [Module ℤ L]

omit [NeZero n] in
/-- The diagonal of the cycle intersection matrix is minus two for cycles of
length at least two. -/
theorem diagonal_eq_neg_two_of_cycle_gram (B : LinearMap.BilinForm ℤ L) (D : ZMod n → L)
    (hgram : ∀ i j : ZMod n, B (D i) (D j) = (-2 : ℤ) * (if i = j then 1 else 0) +
      (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))
    (hn : 2 ≤ n) (i : ZMod n) : B (D i) (D i) = -2 := by
  let : Fact (1 < n) := ⟨hn⟩
  rw [hgram]
  simp [eq_sub_iff_add_eq]

omit [NeZero n] in
/-- The components of a cycle intersection matrix of length at least two are distinct. -/
theorem injective_of_cycle_gram (B : LinearMap.BilinForm ℤ L) (D : ZMod n → L)
    (hgram : ∀ i j : ZMod n, B (D i) (D j) = (-2 : ℤ) * (if i = j then 1 else 0) +
      (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))
    (hn : 2 ≤ n) : Function.Injective D := by
  intro i j h
  by_contra hij
  have he := congrArg (B (D i)) h
  rw [diagonal_eq_neg_two_of_cycle_gram B D hgram hn, hgram i j] at he
  simp only [ite_eq_right hij, mul_zero, zero_add] at he
  split at he <;> split at he <;> omega

end IntegralGram

section Gram

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  {B : LinearMap.BilinForm R V} {D : ZMod n → V}
  (hGram : ∀ i j, B (D i) (D j) =
    (-2 : R) * (if i = j then 1 else 0) +
      (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))

local notation "M" => Submodule.span R (Set.range D)
local notation "δ" => ∑ i, D i

include hGram in
/-- Pairing a boundary combination with a component takes the second cyclic difference
of the coefficients. -/
theorem pairing_sum_smul (a : ZMod n → R) (j : ZMod n) :
    B (∑ i, a i • D i) (D j) = (a (j + 1) - a j) - (a j - a (j - 1)) := by
  classical
  simp only [BilinForm.sum_left, BilinForm.smul_left, hGram, mul_add,
    Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  have hplus (i : ZMod n) : j = i + 1 ↔ i = j - 1 := by
    rw [eq_comm, eq_sub_iff_add_eq]
  have hminus (i : ZMod n) : j = i - 1 ↔ i = j + 1 := by
    exact ⟨fun h ↦ sub_eq_iff_eq_add.mp h.symm, fun h ↦ (sub_eq_iff_eq_add.mpr h).symm⟩
  simp only [hplus, hminus, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

include hGram in
/-- The square of a boundary combination is the negative sum of squares of its cyclic
first differences. -/
theorem pairing_sum_smul_self (a : ZMod n → R) :
    B (∑ i, a i • D i) (∑ i, a i • D i) = -∑ i, (a i - a (i - 1)) ^ 2 := by
  let d (j : ZMod n) := a j - a (j - 1)
  have hshift : ∑ i, a i * d (i + 1) = ∑ i, a (i - 1) * d i := by
    simpa using (Equiv.sum_comp (Equiv.subRight (1 : ZMod n))
      (fun i ↦ a i * d (i + 1))).symm
  simp only [BilinForm.sum_right, BilinForm.smul_right, pairing_sum_smul hGram]
  have hd (j : ZMod n) : a (j + 1) - a j = d (j + 1) := by simp [d]
  have hp (j : ZMod n) : a j - a (j - 1) = d j := rfl
  simp only [hd, hp, mul_sub, Finset.sum_sub_distrib, hshift, ← Finset.sum_neg_distrib]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by dsimp [d]; ring

include hGram in
/-- Each boundary component pairs to zero with the total class. -/
theorem pairing_sum (j : ZMod n) : B δ (D j) = 0 := by
  simpa using pairing_sum_smul hGram (fun _ ↦ 1) j

include hGram in
/-- The span of the boundary components is orthogonal to their sum. -/
theorem span_le_orthogonal_total : M ≤ B.orthogonal (R ∙ δ) := by
  rw [BilinForm.orthogonal, Submodule.orthogonalBilin_span_singleton, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact mem_ker.mpr (pairing_sum hGram i)

include hGram in
/-- The total boundary class has square zero. -/
theorem pairing_sum_sum : B δ δ = 0 := by
  simp only [BilinForm.sum_right, pairing_sum hGram, Finset.sum_const_zero]

include hGram in
private theorem coeff_eq_const_of_pairing_eq_zero [IsAddTorsionFree R] (a : ZMod n → R)
    (ha : ∀ j, B (∑ i, a i • D i) (D j) = 0) (i : ZMod n) : a i = a 0 := by
  let d (j : ZMod n) := a j - a (j - 1)
  have hd (j : ZMod n) : d (j + 1) = d j := by
    have hj := ha j
    rw [pairing_sum_smul hGram] at hj
    simpa only [d, add_sub_cancel_right, sub_eq_zero] using hj
  have hconst := eq_zero_index_of_add_one d hd
  have hzero : d 0 = 0 := by
    have hsum : ∑ j, d j = 0 := sum_sub_prev a
    simp only [hconst, Finset.sum_const, Finset.card_univ, ZMod.card] at hsum
    exact eq_of_nsmul_eq_nsmul_of_addCommute (NeZero.ne n) (AddCommute.all _ _)
      (hsum.trans (nsmul_zero n).symm)
  apply eq_zero_index_of_add_one a _ i
  intro j
  simpa [d, sub_eq_zero] using (hconst (j + 1)).trans hzero

include hGram in
/-- A cycle with nonzero total class is linearly independent over a characteristic-zero domain
when the ambient module is torsion-free. -/
theorem linearIndependent [IsDomain R] [CharZero R] [Module.IsTorsionFree R V]
    (hδ : δ ≠ 0) : LinearIndependent R D := by
  refine Fintype.linearIndependent_iff.mpr fun a ha i ↦ ?_
  have hconst := coeff_eq_const_of_pairing_eq_zero hGram a (by simp [ha])
  simp only [hconst, ← Finset.smul_sum] at ha
  exact (hconst i).trans ((smul_eq_zero.mp ha).resolve_right hδ)

include hGram in
/-- The radical of the boundary span is the line generated by the total boundary class. -/
theorem span_inf_orthogonal [IsAddTorsionFree R] (hSymm : B.IsSymm) :
    M ⊓ B.orthogonal M = R ∙ δ := by
  refine le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
  · rintro x ⟨hx, hxorth⟩
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
    have hconst := coeff_eq_const_of_pairing_eq_zero hGram a fun j ↦
      (hSymm.eq _ _).trans (hxorth _ (Submodule.subset_span (Set.mem_range_self j)))
    simp only [hconst, ← Finset.smul_sum]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · refine ⟨Submodule.sum_mem _ fun i _ ↦ Submodule.subset_span (Set.mem_range_self i), ?_⟩
    exact Submodule.mem_orthogonalBilin_span.mpr
      (by rintro _ ⟨i, rfl⟩; exact (hSymm.eq _ _).trans (pairing_sum hGram i))

end Gram

section Field

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {B : LinearMap.BilinForm K V} {D : ZMod n → V}
  (hGram : ∀ i j, B (D i) (D j) =
    (-2 : K) * (if i = j then 1 else 0) +
      (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))

local notation "M" => Submodule.span K (Set.range D)
local notation "δ" => ∑ i, D i

include hGram in
/-- Over a characteristic-zero field, the boundary span and its orthogonal complement sum
to the orthogonal complement of the total boundary class. -/
theorem span_sup_orthogonal (hSymm : B.IsSymm) (hB : B.Nondegenerate) :
    M ⊔ B.orthogonal M = B.orthogonal (K ∙ δ) := by
  rw [← span_inf_orthogonal hGram hSymm, B.orthogonal_inf hB,
    B.orthogonal_orthogonal hB hSymm.isRefl, sup_comm]

end Field

section Int

variable {L : Type*} [AddCommGroup L] [intModule : Module ℤ L]
  {B : LinearMap.BilinForm ℤ L} {D : ZMod n → L}
  (hGram : ∀ i j, B (D i) (D j) =
    (-2 : ℤ) * (if i = j then 1 else 0) +
      (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))

local notation "M" => Submodule.span ℤ (Set.range D)
local notation "δ" => ∑ i, D i

private theorem int_val_sub_one (i : ZMod n) :
    ((i - 1).val : ℤ) = (i.val : ℤ) - 1 + if i = 0 then (n : ℤ) else 0 := by
  have hn := NeZero.pos n
  by_cases hi : i = 0
  · subst i
    have h : ((n - 1 : ℕ) : ZMod n) = 0 - 1 := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one]
    rw [← h, ZMod.val_natCast_of_lt (by omega), ZMod.val_zero, ite_eq_left rfl]
    omega
  · have hv : i.val ≠ 0 := fun h ↦ hi ((ZMod.val_eq_zero i).mp h)
    have h : ((i.val - 1 : ℕ) : ZMod n) = i - 1 := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_zmod_val, Nat.cast_one]
    have hin := i.val_lt
    rw [← h, ZMod.val_natCast_of_lt (by omega), ite_eq_right hi]
    omega

-- Summation by parts leaves the jump of the integer index at zero.
private theorem sum_val_mul_sub_next (d : ZMod n → ℤ) :
    ∑ i, (i.val : ℤ) * (d (i + 1) - d i) = (n : ℤ) * d 0 - ∑ i, d i := by
  have hshift :
      ∑ i, (i.val : ℤ) * d (i + 1) = ∑ i, ((i - 1).val : ℤ) * d i := by
    simpa using (Equiv.sum_comp (Equiv.subRight (1 : ZMod n))
      (fun i ↦ (i.val : ℤ) * d (i + 1))).symm
  simp only [mul_sub, Finset.sum_sub_distrib, hshift, int_val_sub_one,
    add_mul, sub_mul, one_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  abel

include hGram in
/-- The cyclic moment of the boundary degrees descends to the quotient by the boundary span. -/
noncomputable def degreeMoment : (L ⧸ M) →ₗ[ℤ] ZMod n :=
  (M).liftQ (∑ j, j • (Int.castAddHom (ZMod n)).toIntLinearMap.comp (B.flip (D j))) (by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine LinearMap.mem_ker.mpr ?_
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      AddMonoidHom.coe_toIntLinearMap, Int.coe_castAddHom, BilinForm.flip_apply,
      hGram, Int.cast_add, Int.cast_neg, Int.cast_ofNat,
      Int.cast_ite, Int.cast_one, Int.cast_zero, smul_eq_mul, mul_add, Finset.sum_add_distrib,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    ring)

include hGram in
/-- Evaluate the degree moment on an ambient class using its pairings with the components. -/
@[simp] theorem degreeMoment_mk (x : L) :
    degreeMoment hGram (Submodule.Quotient.mk x) = ∑ j, j * (B x (D j) : ZMod n) := by
  simp [degreeMoment]

include hGram in
private theorem mul_pairing_eq_sub_differences {x : L} {k : ℕ} {a : ZMod n → ℤ}
    (ha : Fintype.linearCombination ℤ D a = k • x) (j : ZMod n) :
    (k : ℤ) * B x (D j) = (a (j + 1) - a j) - (a j - a (j - 1)) := by
  have hj := pairing_sum_smul hGram a j
  rw [← Fintype.linearCombination_apply, ha, map_nsmul] at hj
  simpa using hj

include hGram in
private theorem mul_sum_val_mul_pairing {x : L} {k : ℕ} {a : ZMod n → ℤ}
    (ha : Fintype.linearCombination ℤ D a = k • x) :
    (k : ℤ) * (∑ j, (j.val : ℤ) * B x (D j)) = (n : ℤ) * (a 0 - a (0 - 1)) := by
  let d (j : ZMod n) := a j - a (j - 1)
  calc
    _ = ∑ j, (j.val : ℤ) * (d (j + 1) - d j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hj : (k : ℤ) * B x (D j) = d (j + 1) - d j := by
        simpa [d] using mul_pairing_eq_sub_differences hGram ha j
      rw [← hj]
      ring
    _ = _ := by rw [sum_val_mul_sub_next, sum_sub_prev a, sub_zero]

include hGram in
private theorem difference_cast_eq_const {x : L} {k : ℕ} {a : ZMod n → ℤ}
    (ha : Fintype.linearCombination ℤ D a = k • x) (j : ZMod n) :
    ((a j - a (j - 1) : ℤ) : ZMod k) = ((a 0 - a (0 - 1) : ℤ) : ZMod k) := by
  let d (i : ZMod n) := a i - a (i - 1)
  apply eq_zero_index_of_add_one (fun i ↦ (d i : ZMod k)) _ j
  intro i
  have hi := congrArg (fun z : ℤ ↦ (z : ZMod k)) (mul_pairing_eq_sub_differences hGram ha i)
  simpa [d, eq_comm, sub_eq_zero] using hi

include hGram in
private theorem intCast_sum_val_mul_pairing (x : L) :
    ((∑ j, (j.val : ℤ) * B x (D j) : ℤ) : ZMod n) = degreeMoment hGram ((M).mkQ x) := by
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val,
    Submodule.mkQ_apply, degreeMoment_mk]

include hGram in
private theorem dvd_coeff_sub_of_degreeMoment_eq_zero {x : L} {k : ℕ} (a : ZMod n → ℤ)
    (ha : Fintype.linearCombination ℤ D a = k • x) (hx : degreeMoment hGram ((M).mkQ x) = 0)
    (i : ZMod n) : (k : ℤ) ∣ a i - a 0 := by
  let d (j : ZMod n) := a j - a (j - 1)
  have hn : (n : ℤ) ∣ ∑ j, (j.val : ℤ) * B x (D j) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp
    simpa only [intCast_sum_val_mul_pairing hGram] using hx
  obtain ⟨m, hm⟩ := hn
  have hd0 : a 0 - a (0 - 1) = (k : ℤ) * m := by
    have heq := mul_sum_val_mul_pairing hGram ha
    apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n))
    rw [hm] at heq
    simpa only [mul_left_comm] using heq.symm
  have hzero (j : ZMod n) : (d j : ZMod k) = 0 := by
    rw [difference_cast_eq_const hGram ha j, hd0]
    simp
  have ha' (j : ZMod n) : (a (j + 1) : ZMod k) = (a j : ZMod k) := by
    simpa [d, sub_eq_zero] using hzero (j + 1)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).mp (by
    rw [Int.cast_sub, sub_eq_zero]
    exact eq_zero_index_of_add_one (fun j ↦ (a j : ZMod k)) ha' i)

include hGram in
private theorem mem_span_of_nsmul_mem_of_degreeMoment_eq_zero [IsAddTorsionFree L]
    (hPrimitive : TauCeti.IsPrimitive δ) {x : L} {k : ℕ} (hk : k ≠ 0) (hx : k • x ∈ M)
    (hm : degreeMoment hGram ((M).mkQ x) = 0) : x ∈ M := by
  rw [← Fintype.range_linearCombination] at hx ⊢
  obtain ⟨a, ha⟩ := hx
  choose b hb using fun i ↦ dvd_coeff_sub_of_degreeMoment_eq_zero hGram a ha hm i
  let e := Fintype.linearCombination ℤ D
  let ones : ZMod n → ℤ := fun _ ↦ 1
  have hδ : e ones = δ := by
    rw [Fintype.linearCombination_apply]
    exact Finset.sum_congr rfl fun i _ ↦ intModule.one_smul (D i)
  have ha' : a = k • b + a 0 • ones := by
    funext i
    simpa [ones, add_comm] using eq_add_of_sub_eq (hb i)
  have hshift : k • (x - e b) = a 0 • δ := calc
    _ = e (a - k • b) := by rw [map_sub, map_nsmul, ha, nsmul_sub]
    _ = e (a 0 • ones) := congrArg e (sub_eq_iff_eq_add.mpr (ha'.trans (add_comm _ _)))
    _ = _ := by rw [map_zsmul, hδ]
  obtain ⟨ℓ, hℓ⟩ := TauCeti.isPrimitive_def.mp hPrimitive
  have hcoeff : (k : ℤ) * ℓ (x - e b) = a 0 := by
    simpa only [map_nsmul, map_zsmul, hℓ, nsmul_eq_mul, zsmul_eq_mul, Int.cast_id, mul_one] using
      congrArg ℓ hshift
  -- Primitivity recovers the coefficient of the total class integrally.
  have hrestore : ℓ (x - e b) • δ = x - e b := by
    apply eq_of_nsmul_eq_nsmul_of_addCommute hk (AddCommute.all _ _)
    calc
      _ = ((k : ℤ) * ℓ (x - e b)) • δ := by rw [mul_smul, natCast_zsmul]
      _ = _ := by rw [hcoeff, hshift]
  refine ⟨b + ℓ (x - e b) • ones, ?_⟩
  calc
    _ = e b + ℓ (x - e b) • δ := by rw [map_add, map_zsmul, hδ]
    _ = x := by rw [hrestore, add_sub_cancel]

include hGram in
/-- On the saturation quotient (the torsion of the ambient quotient), the degree moment is
injective if the total boundary class is primitive. -/
theorem degreeMoment_injective_on_torsion [IsAddTorsionFree L]
    (hPrimitive : TauCeti.IsPrimitive δ) :
    Function.Injective ((degreeMoment hGram).toAddMonoidHom.comp
      (AddCommGroup.torsion (L ⧸ M)).subtype) := by
  apply (AddMonoidHom.ker_eq_bot_iff _).mp
  rw [AddSubgroup.eq_bot_iff_forall]
  rintro ⟨q, hq⟩ hzero
  obtain ⟨x, rfl⟩ := (M).mkQ_surjective q
  obtain ⟨k, hk, hkill⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp
    ((AddCommGroup.mem_torsion _).mp hq)
  apply Subtype.ext
  apply (Submodule.Quotient.mk_eq_zero M).mpr
  exact mem_span_of_nsmul_mem_of_degreeMoment_eq_zero hGram hPrimitive hk.ne'
    ((Submodule.Quotient.mk_eq_zero M).mp (by rwa [← Submodule.mkQ_apply, map_nsmul])) hzero

include hGram in
/-- The saturation quotient is a finite cyclic group of order dividing the cycle length. -/
theorem torsion_quotient_cyclic [IsAddTorsionFree L]
    (hPrimitive : TauCeti.IsPrimitive δ) :
    Finite (AddCommGroup.torsion (L ⧸ M)) ∧ IsAddCyclic (AddCommGroup.torsion (L ⧸ M)) ∧
      Nat.card (AddCommGroup.torsion (L ⧸ M)) ∣ n := by
  let f := (degreeMoment hGram).toAddMonoidHom.comp (AddCommGroup.torsion (L ⧸ M)).subtype
  have hf : Function.Injective f := degreeMoment_injective_on_torsion hGram hPrimitive
  exact ⟨Finite.of_injective f hf, isAddCyclic_of_injective f hf,
    by simpa only [Nat.card_zmod] using AddSubgroup.card_dvd_of_injective f hf⟩

include hGram in
private theorem sq_dvd_length_mul_difference_sq {x : L} {k : ℕ} {a : ZMod n → ℤ}
    (ha : Fintype.linearCombination ℤ D a = k • x) :
    (k : ℤ) ^ 2 ∣ (n : ℤ) * (a 0 - a (0 - 1)) ^ 2 := by
  let d (j : ZMod n) := a j - a (j - 1)
  have hdvd (j : ZMod n) : (k : ℤ) ∣ d j - d 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).mp
    rw [Int.cast_sub, sub_eq_zero]
    exact difference_cast_eq_const hGram ha j
  choose b hb using hdvd
  have hd (j : ZMod n) : d j = d 0 + (k : ℤ) * b j := by
    simpa only [add_comm] using eq_add_of_sub_eq (hb j)
  -- The first differences sum to zero. Use this to eliminate the cross term in their norm.
  have hsum : (n : ℤ) * d 0 + (k : ℤ) * ∑ j, b j = 0 := by
    calc
      _ = ∑ j, (d 0 + (k : ℤ) * b j) := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ j, d j := Finset.sum_congr rfl fun j _ ↦ (hd j).symm
      _ = 0 := sum_sub_prev a
  have hnorm : (k : ℤ) ^ 2 * B x x = -∑ j, d j ^ 2 := by
    have h := pairing_sum_smul_self hGram a
    rw [← Fintype.linearCombination_apply, ha] at h
    have hscale : B (k • x) (k • x) = k • (k • B x x) := calc
      _ = k • B x (k • x) := LinearMap.congr_fun (map_nsmul B k x) _
      _ = _ := by rw [map_nsmul]
    rw [hscale] at h
    simpa [d, pow_two, mul_assoc] using h
  have hexpand : ∑ j, d j ^ 2 =
      (n : ℤ) * d 0 ^ 2 + (2 * (k : ℤ) * d 0) * (∑ j, b j) + (k : ℤ) ^ 2 * ∑ j, b j ^ 2 := by
    calc
      _ = ∑ j, (d 0 ^ 2 + (2 * (k : ℤ) * d 0) * b j + (k : ℤ) ^ 2 * b j ^ 2) :=
        Finset.sum_congr rfl fun j _ ↦ by rw [hd]; ring
      _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum]
  refine ⟨B x x + ∑ j, b j ^ 2, ?_⟩
  linear_combination hexpand - hnorm + 2 * d 0 * hsum

include hGram in
/-- Every torsion class has square-zero degree moment. -/
theorem degreeMoment_sq_eq_zero_of_isOfFinAddOrder {q : L ⧸ M} (hq : IsOfFinAddOrder q) :
    degreeMoment hGram q ^ 2 = 0 := by
  obtain ⟨x, rfl⟩ := (M).mkQ_surjective q
  obtain ⟨k, hk, hkill⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hq
  have hmem : k • x ∈ M :=
    (Submodule.Quotient.mk_eq_zero M).mp (by rwa [← Submodule.mkQ_apply, map_nsmul])
  rw [← Fintype.range_linearCombination] at hmem
  obtain ⟨a, ha⟩ := hmem
  let m := ∑ j, (j.val : ℤ) * B x (D j)
  rw [← intCast_sum_val_mul_pairing hGram, ← Int.cast_pow, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hmul : (k : ℤ) * m = (n : ℤ) * (a 0 - a (0 - 1)) :=
    mul_sum_val_mul_pairing hGram ha
  obtain ⟨b, hb⟩ := sq_dvd_length_mul_difference_sq hGram ha
  refine ⟨b, mul_left_cancel₀ (pow_ne_zero 2 (Nat.cast_ne_zero.mpr hk.ne')) ?_⟩
  calc
    (k : ℤ) ^ 2 * m ^ 2 = ((k : ℤ) * m) ^ 2 := by ring
    _ = (n : ℤ) * ((n : ℤ) * (a 0 - a (0 - 1)) ^ 2) := by rw [hmul]; ring
    _ = (k : ℤ) ^ 2 * ((n : ℤ) * b) := by rw [hb]; ring

open TauCeti.IntegralLattice TauCeti.FiniteBilinearModule in
include hGram in
/-- The square of the saturation index divides the cycle length. -/
theorem natCard_torsion_quotient_sq_dvd [IsAddTorsionFree L]
    (hPrimitive : TauCeti.IsPrimitive δ) :
    Nat.card (AddCommGroup.torsion (L ⧸ M)) ^ 2 ∣ n := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  let T := AddCommGroup.torsion (L ⧸ Submodule.span ℤ (Set.range D))
  let f := (degreeMoment hGram).toAddMonoidHom.comp T.subtype
  obtain ⟨t, ht⟩ :=
    isAddCyclic_iff_exists_zmultiples_eq_top.mp (torsion_quotient_cyclic hGram hPrimitive).2.1
  let e := typeADiscriminantGroupEquiv r
  let A := typeARootLattice r
  let g := e.toAddMonoidHom.comp f
  let H := g.range
  have hg : Function.Injective g :=
    e.injective.comp (degreeMoment_injective_on_torsion hGram hPrimitive)
  have hcard : Nat.card H = Nat.card T := (Nat.card_congr (Equiv.ofInjective g hg)).symm
  have hgen : AddSubgroup.zmultiples (g t) = H := by
    rw [← g.map_zmultiples, ht, AddSubgroup.map_top]
  have hH : A.discriminantBilinearModule.IsIsotropic H := by
    refine hgen ▸ (isIsotropic_zmultiples_iff A.discriminantBilinearModule (g t)).mpr ?_
    refine (isIsotropicElem_def A.discriminantBilinearModule (g t)).mpr
      ((A.discriminantBilinearModule_pairing _ _).trans ?_)
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective (f t)
    have hsq : (m : ZMod (r + 1)) ^ 2 = 0 := hm ▸
      degreeMoment_sq_eq_zero_of_isOfFinAddOrder hGram ((AddCommGroup.mem_torsion _).mp t.property)
    have hzero : ((m ^ 2 * (r : ℤ) : ℤ) : ZMod (r + 1)) = 0 := by simp [hsq]
    have he : g t = m • typeAFundamentalWeightClass r := calc
      g t = e (f t) := rfl
      _ = _ := by
        rw [← hm, ← zsmul_one, map_zsmul]
        exact congrArg (m • ·) (typeADiscriminantGroupEquiv_apply_one r)
    rw [he, discriminantPairing_zsmul_typeAFundamentalWeightClass]
    have h := congrArg (ZMod.toRatAddCircle (r + 1)) hzero
    rw [ZMod.toRatAddCircle_intCast, map_zero] at h
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Nat.cast_add, Nat.cast_one,
      pow_two] using h
  have hIntegral := (A.isIntegral_intermediateCarrierOfDiscriminantSubgroup_iff H).mpr hH
  simpa only [IntermediateCarrier.index_intermediateCarrierOfDiscriminantSubgroup,
    hcard, A, discriminant_typeARootLattice] using hIntegral.index_sq_dvd_discriminant

include hGram in
/-- In a nondegenerate integral lattice with nonzero total boundary class, the cycle length is
strictly less than the ambient rank. -/
theorem length_lt_finrank [Module.Finite ℤ L] [Module.IsTorsionFree ℤ L]
    (hB : B.Nondegenerate) (hδ : δ ≠ 0) : n < Module.finrank ℤ L := by
  let f := B δ
  have hM : M ≤ LinearMap.ker f := by
    simpa only [f, BilinForm.orthogonal, Submodule.orthogonalBilin_span_singleton]
      using span_le_orthogonal_total hGram
  have hn := Submodule.finrank_mono hM
  rw [finrank_span_eq_card (linearIndependent hGram hδ), ZMod.card] at hn
  have hnull := f.finrank_range_add_finrank_ker
  have hf : f ≠ 0 := fun h ↦ hδ (hB.1 δ fun y ↦ by
    simpa only [LinearMap.zero_apply] using LinearMap.congr_fun h y)
  have hrange : 0 < Module.finrank ℤ (LinearMap.range f) := by
    have h := LinearMap.range_eq_bot.not.mpr hf
    have := Submodule.nontrivial_iff_ne_bot.mpr h
    exact Module.finrank_pos
  omega

open TensorProduct

include hGram in
/-- For an integral cycle, the rationalizations of the boundary span and its integral orthogonal
complement sum to the rational orthogonal complement of the total class. -/
theorem span_sup_orthogonal_rat [Module.Free ℤ L] [Module.Finite ℤ L]
    (hSymm : B.IsSymm) (hB : B.Nondegenerate) :
    (M).baseChange ℚ ⊔ (B.orthogonal M).baseChange ℚ =
      (B.baseChange ℚ).orthogonal ((ℤ ∙ δ).baseChange ℚ) := by
  let u := TensorProduct.mk ℤ ℚ L 1
  let b := B.baseChange ℚ
  let W := Submodule.span ℚ (Set.range (u ∘ D))
  have hW : (M).baseChange ℚ = W := by
    rw [Submodule.baseChange_span, ← Set.range_comp]
  -- Orthogonality is the kernel of the map of pairings with the boundary components.
  let degrees := LinearMap.pi fun i ↦ B (D i)
  let e := TensorProduct.piScalarRight ℤ ℚ ℚ (ZMod n)
  have hdegrees : e.toLinearMap.comp (degrees.baseChange ℚ) =
      LinearMap.pi fun i ↦ b (u (D i)) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    ext i
    simp [e, degrees, b, u, TensorProduct.mk_apply, Algebra.smul_def]
  have hker : LinearMap.ker degrees = B.orthogonal M := by
    ext x
    simp [degrees, BilinForm.orthogonal, LinearMap.mem_ker, funext_iff]
  have horth : (B.orthogonal M).baseChange ℚ = b.orthogonal W := by
    have : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
    rw [← hker, ← LinearMap.ker_baseChange_of_flat,
      ← LinearMap.ker_comp_of_ker_eq_bot _ e.ker, hdegrees]
    ext x
    simp [W, BilinForm.orthogonal, LinearMap.mem_ker, funext_iff]
  have hg (i j : ZMod n) : b (u (D i)) (u (D j)) =
      (-2 : ℚ) * (if i = j then 1 else 0) +
        (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0) := by
    simp [b, u, TensorProduct.mk_apply, hGram]
  have hs : b.IsSymm := BilinForm.isSymm_iff.mpr
    (BilinForm.IsSymm.baseChange ℚ (BilinForm.isSymm_iff.mp hSymm))
  have hb : b.Nondegenerate :=
    (B.nondegenerate_baseChange_iff (Module.Free.chooseBasis ℤ L)).mpr hB
  rw [hW, horth, span_sup_orthogonal (D := u ∘ D) hg hs hb, Submodule.baseChange_span,
    Set.image_singleton, map_sum]
  rfl

end Int

end QPainleve.BoundaryCycle
