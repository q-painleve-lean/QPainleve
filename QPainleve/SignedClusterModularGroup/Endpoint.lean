/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel

import QPainleve.LinearAlgebra.BilinearForm.Index
import QPainleve.LinearAlgebra.Submodule.FiniteIndex
import Mathlib.Algebra.Field.ZMod

/-!
# Integral identification of endpoint charge lattices

Equality of exchange matrices identifies the images of two full-rank charge maps.
For primitive charges, the ambient rank-two lattices can be recovered from the images
at index two, and at index three when a primitive three-term relation has square sum
zero modulo three. The quotient characters of the images detect ambient divisibility
by the common index. The charge-image comparison uses `ker_chargeExchangeMatrix`
and Mathlib's first isomorphism theorem for linear maps.
-/

public section

namespace QPainleve.Cluster

open LinearMap (BilinForm)

variable {ι N₁ N₂ : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup N₁] [AddCommGroup N₂]

private theorem det_toMatrix_chargeForm {N : Type*} [AddCommGroup N]
    (b : Module.Basis (Fin 2) ℤ N) (ω : BilinForm ℤ N) (hω : ω.IsAlt)
    (hb : ω (b 0) (b 1) = 1) : (ω.toMatrix b).det = 1 := by
  have h₁₀ : ω (b 1) (b 0) = -1 := by rw [← hω.neg_eq, hb]
  simp [Matrix.det_fin_two, BilinForm.toMatrix_apply, hω (b 0), hω (b 1), hb, h₁₀]

private theorem exists_charge_range_equiv {ω₁ : BilinForm ℤ N₁} {ω₂ : BilinForm ℤ N₂}
    {v₁ : (ι → ℤ) →ₗ[ℤ] N₁} {v₂ : (ι → ℤ) →ₗ[ℤ] N₂}
    [Module.Free ℤ N₁] [Module.Free ℤ N₂] [Module.Finite ℤ N₁] [Module.Finite ℤ N₂]
    (hω₁ : ω₁.SeparatingRight) (hω₂ : ω₂.SeparatingRight)
    (h₁ : v₁.range.toAddSubgroup.index ≠ 0) (h₂ : v₂.range.toAddSubgroup.index ≠ 0)
    (h : chargeExchangeMatrix ω₁ v₁ = chargeExchangeMatrix ω₂ v₂) :
    ∃ e : v₁.range ≃ₗ[ℤ] v₂.range,
      (∀ x, e (v₁.rangeRestrict x) = v₂.rangeRestrict x) ∧
      ∀ x y : v₁.range, ω₂ (e x).val (e y).val = ω₁ x.val y.val := by
  let : v₁.range.toAddSubgroup.FiniteIndex := AddSubgroup.finiteIndex_iff.mpr h₁
  let : v₂.range.toAddSubgroup.FiniteIndex := AddSubgroup.finiteIndex_iff.mpr h₂
  have hker : v₁.ker = v₂.ker := calc
    _ = (chargeExchangeMatrix ω₁ v₁).mulVecLin.ker :=
      (ker_chargeExchangeMatrix ω₁ v₁ hω₁
        (AddSubgroup.finrank_eq_of_finiteIndex v₁.range.toAddSubgroup)).symm
    _ = _ := h ▸ ker_chargeExchangeMatrix ω₂ v₂ hω₂
      (AddSubgroup.finrank_eq_of_finiteIndex v₂.range.toAddSubgroup)
  let e := v₁.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans v₂.quotKerEquivRange)
  have he (x) : e (v₁.rangeRestrict x) = v₂.rangeRestrict x := by
    have h₁x : v₁.quotKerEquivRange (Submodule.Quotient.mk x) = v₁.rangeRestrict x :=
      Subtype.ext (v₁.quotKerEquivRange_apply_mk x)
    have h₂x : v₂.quotKerEquivRange (Submodule.Quotient.mk x) = v₂.rangeRestrict x :=
      Subtype.ext (v₂.quotKerEquivRange_apply_mk x)
    rw [← h₁x]
    simp [e, h₂x]
  refine ⟨e, he, ?_⟩
  have hform : ω₁.comp v₁ v₁ = ω₂.comp v₂ v₂ := by
    apply BilinForm.ext_basis (Pi.basisFun ℤ ι)
    intro i j
    simpa only [Pi.basisFun_apply, BilinForm.comp_apply, chargeExchangeMatrix_apply]
      using congr($h i j)
  intro x y
  obtain ⟨x, rfl⟩ := v₁.surjective_rangeRestrict x
  obtain ⟨y, rfl⟩ := v₁.surjective_rangeRestrict y
  rw [he, he]
  exact (congr($hform x y)).symm

private theorem charge_index_eq {ω₁ : BilinForm ℤ N₁} {ω₂ : BilinForm ℤ N₂}
    (b₁ : Module.Basis (Fin 2) ℤ N₁) (b₂ : Module.Basis (Fin 2) ℤ N₂)
    (h₁ : (ω₁.toMatrix b₁).det = 1) (h₂ : (ω₂.toMatrix b₂).det = 1)
    {H : Submodule ℤ N₁} {K : Submodule ℤ N₂}
    (hf : H.toAddSubgroup.index ≠ 0) (e : H ≃ₗ[ℤ] K)
    (he : ∀ x y : H, ω₂ (e x).val (e y).val = ω₁ x.val y.val) :
    H.toAddSubgroup.index = K.toAddSubgroup.index := by
  let : Module.Finite ℤ N₁ := Module.Finite.of_basis b₁
  let : Module.Free ℤ N₁ := Module.Free.of_basis b₁
  let : H.toAddSubgroup.FiniteIndex := AddSubgroup.finiteIndex_iff.mpr hf
  have hr : Module.finrank ℤ H = Fintype.card (Fin 2) :=
    (AddSubgroup.finrank_eq_of_finiteIndex H.toAddSubgroup).trans
      (Module.finrank_eq_card_basis b₁)
  let c : Module.Basis (Fin 2) ℤ H :=
    (Module.finBasis ℤ H).reindex (Fintype.equivOfCardEq ((Fintype.card_fin _).trans hr))
  have hmat : (ω₁.restrict H).toMatrix c = (ω₂.restrict K).toMatrix (c.map e) := by
    ext i j
    simpa [BilinForm.toMatrix_apply, BilinForm.restrict_apply] using (he (c i) (c j)).symm
  have hsq := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ ↦ M.det.natAbs) hmat
  simp only [ω₁.natAbs_det_toMatrix_restrict H b₁ c,
    ω₂.natAbs_det_toMatrix_restrict K b₂ (c.map e), h₁, h₂, Int.natAbs_one, one_mul] at hsq
  exact (Nat.pow_left_inj (n := 2) (by decide)).mp hsq

omit [Fintype ι] in
private theorem charge_residue_ne_zero {N : Type*} [AddCommGroup N]
    {p : ℕ} [Fact p.Prime] (v : (ι → ℤ) →ₗ[ℤ] N)
    (hprim : ∀ i, ∃ l : N →ₗ[ℤ] ℤ, l (v (Pi.single i 1)) = 1)
    (χ : v.range →ₗ[ℤ] ZMod p)
    (hχ : χ.ker = (p • (LinearMap.id : N →ₗ[ℤ] N)).range.comap v.range.subtype)
    (i : ι) : χ (v.rangeRestrict (Pi.single i 1)) ≠ 0 := by
  intro hz
  have hm := LinearMap.mem_ker.mpr hz
  rw [hχ] at hm
  obtain ⟨y, hy⟩ : ∃ y : N, p • y = v (Pi.single i 1) := hm
  obtain ⟨l, hl⟩ := hprim i
  have hdiv : (p : ℤ) ∣ (1 : ℤ) := ⟨l y, by simpa [map_nsmul, nsmul_eq_mul, hl]
    using (congrArg l hy).symm⟩
  exact (Fact.out : p.Prime).not_dvd_one (Int.natCast_dvd_natCast.mp (by simpa using hdiv))

omit [Fintype ι] in
private theorem exists_charge_lattice_equiv_of_prime_index {p : ℕ} [Fact p.Prime]
    {v₁ : (ι → ℤ) →ₗ[ℤ] N₁} {v₂ : (ι → ℤ) →ₗ[ℤ] N₂}
    [Module.Free ℤ N₁] [Module.Free ℤ N₂] [Module.Finite ℤ N₁] [Module.Finite ℤ N₂]
    (hr₁ : Module.finrank ℤ N₁ = 2) (hr₂ : Module.finrank ℤ N₂ = 2)
    (hs₁ : v₁.range.toAddSubgroup.index = p) (hs₂ : v₂.range.toAddSubgroup.index = p)
    (hp₁ : ∀ i, ∃ l : N₁ →ₗ[ℤ] ℤ, l (v₁ (Pi.single i 1)) = 1)
    (hp₂ : ∀ i, ∃ l : N₂ →ₗ[ℤ] ℤ, l (v₂ (Pi.single i 1)) = 1)
    (agree : ∀ f g : (ι → ℤ) →ₗ[ℤ] ZMod p, v₁.ker ≤ f.ker → v₁.ker ≤ g.ker →
      (∀ i, f (Pi.single i 1) ≠ 0) → (∀ i, g (Pi.single i 1) ≠ 0) → f.ker = g.ker)
    (e : v₁.range ≃ₗ[ℤ] v₂.range)
    (he : ∀ x, e (v₁.rangeRestrict x) = v₂.rangeRestrict x) :
    ∃ E : N₁ ≃ₗ[ℤ] N₂, ∀ x : v₁.range, E x = (e x).val := by
  obtain ⟨χ₁, hχ₁⟩ := v₁.range.exists_ker_eq_comap_range_nsmul hr₁ hs₁
  obtain ⟨χ₂, hχ₂⟩ := v₂.range.exists_ker_eq_comap_range_nsmul hr₂ hs₂
  have hker (χ : v₁.range →ₗ[ℤ] ZMod p) : v₁.ker ≤ (χ.comp v₁.rangeRestrict).ker := by
    simpa only [LinearMap.ker_comp, Submodule.comap_bot, v₁.ker_rangeRestrict] using
      (Submodule.comap_mono (f := v₁.rangeRestrict) (bot_le : ⊥ ≤ χ.ker))
  have hcomp : e.toLinearMap.comp v₁.rangeRestrict = v₂.rangeRestrict := LinearMap.ext he
  have hχ := agree (χ₁.comp v₁.rangeRestrict) (χ₂.comp v₂.rangeRestrict) (hker χ₁)
    (by simpa only [LinearMap.comp_assoc, hcomp] using hker (χ₂.comp e.toLinearMap))
    (charge_residue_ne_zero v₁ hp₁ χ₁ hχ₁) (charge_residue_ne_zero v₂ hp₂ χ₂ hχ₂)
  refine (e.existsUnique_extend_of_nsmul (Fact.out : p.Prime).ne_zero
    (hs₁ ▸ v₁.range.toAddSubgroup.nsmul_index_mem)
    (hs₂ ▸ v₂.range.toAddSubgroup.nsmul_index_mem) ?_).exists
  intro x
  obtain ⟨a, rfl⟩ := v₁.surjective_rangeRestrict x
  rw [he]
  have ha := SetLike.ext_iff.mp hχ a
  rwa [LinearMap.ker_comp, LinearMap.ker_comp, hχ₁, hχ₂] at ha

omit [Fintype ι] in
private theorem ker_eq_of_zmod_two [Finite ι] (f g : (ι → ℤ) →ₗ[ℤ] ZMod 2)
    (hf : ∀ i, f (Pi.single i 1) ≠ 0) (hg : ∀ i, g (Pi.single i 1) ≠ 0) :
    f.ker = g.ker := by
  let := Fintype.ofFinite ι
  have h : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  congr 1
  apply (Pi.basisFun ℤ ι).ext
  simpa only [Pi.basisFun_apply] using fun i ↦ (h _ (hf i)).trans (h _ (hg i)).symm

private theorem ker_eq_of_zmod_three [Module.IsTorsionFree ℤ N₁]
    {v : (ι → ℤ) →ₗ[ℤ] N₁} (t : Fin 3 ≃ ι)
    (x : v.ker) (hprim : ∃ l : v.ker →ₗ[ℤ] ℤ, l x = 1)
    (hsq : (3 : ℤ) ∣ ∑ i, x.val i ^ 2)
    (f g : (ι → ℤ) →ₗ[ℤ] ZMod 3)
    (hf : v.ker ≤ f.ker) (hg : v.ker ≤ g.ker)
    (hf' : ∀ i, f (Pi.single i 1) ≠ 0) (hg' : ∀ i, g (Pi.single i 1) ≠ 0) :
    f.ker = g.ker := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let a : Fin 3 → ZMod 3 := fun i ↦ (x.val (t i) : ℤ)
  have ha_nonzero : ∃ i, a i ≠ 0 := by
    by_contra! ha
    have hdiv (i : ι) : (3 : ℤ) ∣ x.val i := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 (by simpa [a] using ha (t.symm i))
    choose y hy using hdiv
    have hxy : x.val = (3 : ℤ) • y := funext hy
    have hy' : y ∈ v.ker := by
      have hzero := LinearMap.mem_ker.mp x.property
      rw [hxy, map_smul, smul_eq_zero] at hzero
      exact LinearMap.mem_ker.mpr (hzero.resolve_left (by decide))
    have hx' : x = (3 : ℤ) • (⟨y, hy'⟩ : v.ker) := Subtype.ext hxy
    obtain ⟨l, hl⟩ := hprim
    rw [hx', map_smul, smul_eq_mul] at hl
    omega
  have ha_sq : ∑ i, a i ^ 2 = 0 := by
    have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 hsq
    rw [Int.cast_sum] at hzero
    simpa only [a, ← Int.cast_pow, ← t.sum_comp] using hzero
  -- A nonzero square contributes one, so all three coordinates must be nonzero.
  have hall : ∀ (a : Fin 3 → ZMod 3), (∃ i, a i ≠ 0) →
      (∑ i, a i ^ 2) = 0 → ∀ i, a i ≠ 0 := by decide
  -- Three nonzero residues sum to zero only when they are all equal.
  have hconst : ∀ (z : Fin 3 → ZMod 3), (∀ i, z i ≠ 0) →
      (∑ i, z i) = 0 → ∀ i, z i = z 0 := by decide
  have hproducts (j : (ι → ℤ) →ₗ[ℤ] ZMod 3) (hj : j x.val = 0)
      (hj' : ∀ i, j (Pi.single i 1) ≠ 0) (i : Fin 3) :
      a i * j (Pi.single (t i) 1) = a 0 * j (Pi.single (t 0) 1) := by
    apply hconst _ (fun k ↦ mul_ne_zero (hall a ha_nonzero ha_sq k) (hj' (t k))) _ i
    have hs := congrArg j ((Pi.basisFun ℤ ι).sum_repr x.val)
    rw [t.sum_comp (fun k ↦ (x.val k : ZMod 3) * j (Pi.single k 1))]
    simpa only [Pi.basisFun_apply, Pi.basisFun_repr, map_sum, map_smul,
      ← Int.cast_smul_eq_zsmul (R := ZMod 3), smul_eq_mul, a, hj] using hs
  have hpoint (i : Fin 3) :
      g (Pi.single (t i) 1) = (g (Pi.single (t 0) 1) / f (Pi.single (t 0) 1)) *
        f (Pi.single (t i) 1) := by
    apply (mul_left_cancel₀ (hall a ha_nonzero ha_sq i))
    rw [hproducts g (LinearMap.mem_ker.mp (hg x.property)) hg', mul_left_comm,
      hproducts f (LinearMap.mem_ker.mp (hf x.property)) hf']
    field_simp [hf' (t 0)]
  have hmaps : g = (g (Pi.single (t 0) 1) / f (Pi.single (t 0) 1)) • f := by
    apply (Pi.basisFun ℤ ι).ext
    intro i
    obtain ⟨i, rfl⟩ := t.surjective i
    simpa only [Pi.basisFun_apply, LinearMap.smul_apply, smul_eq_mul] using hpoint i
  rw [hmaps]
  ext i
  simp [LinearMap.mem_ker, div_ne_zero (hg' (t 0)) (hf' (t 0))]

private theorem exists_charge_lattice_equiv_extend
    {v₁ : (ι → ℤ) →ₗ[ℤ] N₁} {v₂ : (ι → ℤ) →ₗ[ℤ] N₂}
    [Module.Free ℤ N₁] [Module.Free ℤ N₂] [Module.Finite ℤ N₁] [Module.Finite ℤ N₂]
    (hr₁ : Module.finrank ℤ N₁ = 2) (hr₂ : Module.finrank ℤ N₂ = 2)
    (hp₁ : ∀ i, ∃ l : N₁ →ₗ[ℤ] ℤ, l (v₁ (Pi.single i 1)) = 1)
    (hp₂ : ∀ i, ∃ l : N₂ →ₗ[ℤ] ℤ, l (v₂ (Pi.single i 1)) = 1)
    {s : ℕ} (hs : s = 1 ∨ s = 2 ∨ s = 3)
    (hs₁ : v₁.range.toAddSubgroup.index = s) (hs₂ : v₂.range.toAddSubgroup.index = s)
    (hrel : s = 3 → Fintype.card ι = 3 ∧ ∃ x : v₁.ker,
      (∃ l : v₁.ker →ₗ[ℤ] ℤ, l x = 1) ∧ (3 : ℤ) ∣ ∑ i, x.val i ^ 2)
    (e : v₁.range ≃ₗ[ℤ] v₂.range)
    (he : ∀ x, e (v₁.rangeRestrict x) = v₂.rangeRestrict x) :
    ∃ E : N₁ ≃ₗ[ℤ] N₂, ∀ x : v₁.range, E x = (e x).val := by
  rcases hs with h | h | h
  · rw [h] at hs₁ hs₂
    exact (e.existsUnique_extend_of_nsmul Nat.one_ne_zero
      (hs₁ ▸ v₁.range.toAddSubgroup.nsmul_index_mem)
      (hs₂ ▸ v₂.range.toAddSubgroup.nsmul_index_mem)
      (fun x ↦ ⟨fun _ ↦ ⟨(e x).val, one_nsmul _⟩, fun _ ↦ ⟨x.val, one_nsmul _⟩⟩)).exists
  · rw [h] at hs₁ hs₂
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact exists_charge_lattice_equiv_of_prime_index (p := 2) hr₁ hr₂ hs₁ hs₂ hp₁ hp₂
      (fun f g _ _ ↦ ker_eq_of_zmod_two f g) e he
  · obtain ⟨hc, x, hx, hsq⟩ := hrel h
    let t : Fin 3 ≃ ι := Fintype.equivOfCardEq ((Fintype.card_fin 3).trans hc.symm)
    rw [h] at hs₁ hs₂
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact exists_charge_lattice_equiv_of_prime_index (p := 3) hr₁ hr₂ hs₁ hs₂ hp₁ hp₂
      (ker_eq_of_zmod_three t x hx hsq) e he

/-- The lattice part of integral endpoint identification. Two rank-two oriented lattices
with primitive labeled charges and the same exchange matrix are related by an integral
isomorphism that takes each charge to its counterpart and preserves the determinant forms.

The numerical inputs are the boundary length `n ≤ 9`, the label count `12 - n`,
and the divisibility of `n` by the square of the first charge index. The second
charge image has finite index, and the proof shows that the indices agree. At index
three, the primitive isotropic boundary class gives a primitive charge relation
with square sum zero modulo three. -/
theorem exists_charge_lattice_equiv
    (b₁ : Module.Basis (Fin 2) ℤ N₁) (b₂ : Module.Basis (Fin 2) ℤ N₂)
    {ω₁ : BilinForm ℤ N₁} {ω₂ : BilinForm ℤ N₂}
    (hω₁ : ω₁.IsAlt) (hω₂ : ω₂.IsAlt)
    (hb₁ : ω₁ (b₁ 0) (b₁ 1) = 1) (hb₂ : ω₂ (b₂ 0) (b₂ 1) = 1)
    {v₁ : (ι → ℤ) →ₗ[ℤ] N₁} {v₂ : (ι → ℤ) →ₗ[ℤ] N₂}
    (hprim₁ : ∀ i, ∃ l : N₁ →ₗ[ℤ] ℤ, l (v₁ (Pi.single i 1)) = 1)
    (hprim₂ : ∀ i, ∃ l : N₂ →ₗ[ℤ] ℤ, l (v₂ (Pi.single i 1)) = 1)
    (hmat : chargeExchangeMatrix ω₁ v₁ = chargeExchangeMatrix ω₂ v₂)
    {n : ℕ} (hn : 0 < n) (hn' : n ≤ 9) (hc : Fintype.card ι + n = 12)
    (hindex₁ : v₁.range.toAddSubgroup.index ^ 2 ∣ n)
    (hnz₂ : v₂.range.toAddSubgroup.index ≠ 0)
    (hrel : v₁.range.toAddSubgroup.index = 3 → ∃ x : v₁.ker,
      (∃ l : v₁.ker →ₗ[ℤ] ℤ, l x = 1) ∧ (3 : ℤ) ∣ ∑ i, x.val i ^ 2) :
    ∃ E : N₁ ≃ₗ[ℤ] N₂, (∀ x, E (v₁ x) = v₂ x) ∧
      ∀ x y, ω₂ (E x) (E y) = ω₁ x y := by
  let := Module.Free.of_basis b₁
  let := Module.Free.of_basis b₂
  let := Module.Finite.of_basis b₁
  let := Module.Finite.of_basis b₂
  have hd₁ := det_toMatrix_chargeForm b₁ ω₁ hω₁ hb₁
  have hd₂ := det_toMatrix_chargeForm b₂ ω₂ hω₂ hb₂
  have hnz₁ : v₁.range.toAddSubgroup.index ≠ 0 := by
    intro hz
    simp [hz, hn.ne'] at hindex₁
  obtain ⟨e, he, hpair⟩ := exists_charge_range_equiv
    (ω₁.nondegenerate_of_det_ne_zero b₁ (hd₁ ▸ one_ne_zero)).2
    (ω₂.nondegenerate_of_det_ne_zero b₂ (hd₂ ▸ one_ne_zero)).2 hnz₁ hnz₂ hmat
  have hindex := charge_index_eq b₁ b₂ hd₁ hd₂ hnz₁ e hpair
  let s := v₁.range.toAddSubgroup.index
  have hs_le : s ≤ 3 := by
    by_contra! hs
    have hlo : 4 ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left (by omega) _
    have hhi : s ^ 2 ≤ 9 := (Nat.le_of_dvd hn hindex₁).trans hn'
    omega
  have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
  have hthree (h : s = 3) : Fintype.card ι = 3 ∧ ∃ x : v₁.ker,
      (∃ l : v₁.ker →ₗ[ℤ] ℤ, l x = 1) ∧ (3 : ℤ) ∣ ∑ i, x.val i ^ 2 := by
    have hdiv : s ^ 2 ∣ n := hindex₁
    rw [h] at hdiv
    have hnine := Nat.le_of_dvd hn hdiv
    exact ⟨by omega, hrel h⟩
  obtain ⟨E, hE⟩ := exists_charge_lattice_equiv_extend
    (by simpa using Module.finrank_eq_card_basis b₁)
    (by simpa using Module.finrank_eq_card_basis b₂) hprim₁ hprim₂ hs rfl hindex.symm hthree e he
  refine ⟨E, fun x ↦ (hE (v₁.rangeRestrict x)).trans (congrArg Subtype.val (he x)), ?_⟩
  intro x y
  let xs : v₁.range := ⟨s • x, v₁.range.toAddSubgroup.nsmul_index_mem x⟩
  let ys : v₁.range := ⟨s • y, v₁.range.toAddSubgroup.nsmul_index_mem y⟩
  have hxy := hpair xs ys
  rw [← hE xs, ← hE ys] at hxy
  have hcancel : (s : ℤ) * (s : ℤ) ≠ 0 := mul_ne_zero
    (Int.natCast_ne_zero.mpr hnz₁) (Int.natCast_ne_zero.mpr hnz₁)
  apply mul_left_cancel₀ hcancel
  dsimp only [xs, ys] at hxy
  rw [map_nsmul E, map_nsmul E] at hxy
  simpa only [← Nat.cast_smul_eq_nsmul ℤ, BilinForm.smul_left, BilinForm.smul_right, ← mul_assoc]
    using hxy

end QPainleve.Cluster
