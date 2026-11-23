/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.RingTheory.Ideal.AssociatedGraded
public import TauCeti.RingTheory.Ideal.AffineBlowup

/-!
# Exceptional multiplicity on an affine blowup chart

On a chart indexed by a regular element of order one, an equation of order `m` pulls
back to the exceptional parameter to the power `m` times a strict-transform equation.
The latter generates the kernel of restriction to the localized hypersurface.

The calculation uses Tau Ceti's fraction description `Ideal.mem_affineBlowup_iff` and
`Ideal.AssociatedGraded.mul_notMem_pow_succ` for multiplication of initial forms.
-/

public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {I : Ideal R} {a : R} [IsLocalization.Away a S]

local notation "B" => I.affineBlowup a S
local notation "aB" => algebraMap R B a

/-- An element of `I ^ m` pulls back to a multiple of the `m`th power of the exceptional
parameter on every chart indexed by an element of `I`. -/
theorem pow_dvd_algebraMap_affineBlowup (ha : a ∈ I) {m : ℕ} {f : R}
    (hf : f ∈ I ^ m) : aB ^ m ∣ algebraMap R B f := by
  let q : S := (IsLocalization.Away.algebraMap_isUnit (S := S) a).unit⁻¹ ^ m *
    algebraMap R S f
  have hq : algebraMap R S a ^ m * q = algebraMap R S f := by
    simp [q, ← mul_assoc, ← mul_pow]
  refine ⟨⟨q, (mem_affineBlowup_iff ha).mpr ⟨m, f, hf, hq⟩⟩, Subtype.ext hq.symm⟩

private theorem mem_pow_iff_of_affineBlowup_fraction [NoZeroDivisors I.AssociatedGraded]
    (ha : a ∈ I) (ha₂ : a ∉ I ^ 2) (haReg : a ∈ nonZeroDivisors R)
    {m n : ℕ} {z : B} {x : R} (hx : aB ^ n * z = algebraMap R B x) :
    aB ^ m ∣ z ↔ x ∈ I ^ (n + m) := by
  have reg : IsLeftRegular aB := isRegular_algebraMap_affineBlowup.left
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨k, y, hy, hw⟩ := (mem_affineBlowup_iff ha).mp w.property
    have hinj : Function.Injective (algebraMap R S) :=
      IsLocalization.injective S ((Submonoid.powers_le).mpr haReg)
    have heq : a ^ k * x = a ^ (n + m) * y := hinj (by
      have hx' := congrArg Subtype.val hx
      simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap] at hx'
      simp only [map_mul, map_pow, ← hx', ← hw, pow_add]
      ring)
    apply (pow_mul_mem_pow_add_iff_of_notMem_sq ha ha₂ k (n + m) x).mp
    rw [heq, Nat.add_comm k, pow_add]
    exact mul_mem_mul (pow_mem_pow ha _) hy
  · intro h
    obtain ⟨w, hw⟩ := pow_dvd_algebraMap_affineBlowup (S := S) ha h
    refine ⟨w, (reg.pow n) ?_⟩
    -- Write the equality of the two values of the multiplication map as a product.
    change aB ^ n * z = aB ^ n * (aB ^ m * w)
    rw [hx, hw, pow_add, mul_assoc]

/-- Divisibility of a pulled-back element by an exceptional power detects membership in the
corresponding power of the center ideal. -/
theorem pow_dvd_algebraMap_affineBlowup_iff [NoZeroDivisors I.AssociatedGraded]
    (ha : a ∈ I) (ha₂ : a ∉ I ^ 2) (haReg : a ∈ nonZeroDivisors R) (m : ℕ) (f : R) :
    aB ^ m ∣ algebraMap R B f ↔ f ∈ I ^ m := by
  simpa using mem_pow_iff_of_affineBlowup_fraction (S := S) ha ha₂ haReg
    (m := m) (n := 0) (z := algebraMap R B f) (by simp)

/-- An order-one regular chart element is prime in the chart algebra if the associated graded ring
of the center has no zero divisors. -/
theorem prime_algebraMap_affineBlowup [NoZeroDivisors I.AssociatedGraded]
    (ha : a ∈ I) (ha₂ : a ∉ I ^ 2) (haReg : a ∈ nonZeroDivisors R) : Prime aB := by
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S ((Submonoid.powers_le).mpr haReg)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hzero : a = 0 := (map_eq_zero_iff _ hinj).mp (congrArg Subtype.val h)
    exact ha₂ (hzero ▸ zero_mem _)
  · intro hu
    have h := (pow_dvd_algebraMap_affineBlowup_iff (S := S) ha ha₂ haReg 1 1).mp
      (by simpa using isUnit_iff_dvd_one.mp hu)
    have htop : I = ⊤ := eq_top_of_isUnit_mem I (by simpa using h) isUnit_one
    exact ha₂ (by rw [htop, pow_two, Ideal.top_mul]; simp)
  intro z w hzw
  obtain ⟨n, x, hx, hzx⟩ := (mem_affineBlowup_iff ha).mp z.property
  obtain ⟨m, y, hy, hwy⟩ := (mem_affineBlowup_iff ha).mp w.property
  have hz : aB ^ n * z = algebraMap R B x := Subtype.ext hzx
  have hw : aB ^ m * w = algebraMap R B y := Subtype.ext hwy
  have hmul : aB ^ (n + m) * (z * w) = algebraMap R B (x * y) := by
    rw [map_mul, ← hz, ← hw, pow_add]
    ring
  have hprime {z : B} {x : R} {k : ℕ} (h : aB ^ k * z = algebraMap R B x) :
      aB ∣ z ↔ x ∈ I ^ (k + 1) := by
    simpa only [pow_one] using mem_pow_iff_of_affineBlowup_fraction ha ha₂ haReg (m := 1) h
  rw [hprime hz, hprime hw]
  by_contra! h
  exact AssociatedGraded.mul_notMem_pow_succ hx h.1 hy h.2 ((hprime hmul).mp hzw)

/-- On a chart indexed by an order-one regular element of the center, an equation of
exact order `m` factors as `a ^ m * g`, with `g` nonzero modulo the exceptional ideal.
The ideal of the scheme-theoretic closure of the hypersurface off the exceptional locus
is the kernel of the map to the quotient by the pulled-back equation localized at `a`.
That ideal is generated by `g`. -/
theorem exists_ker_away_quotient_eq_span_affineBlowup [NoZeroDivisors I.AssociatedGraded]
    (ha : a ∈ I) (ha₂ : a ∉ I ^ 2) (haReg : a ∈ nonZeroDivisors R)
    {m : ℕ} {f : R} (hf : f ∈ I ^ m) (hf' : f ∉ I ^ (m + 1)) :
    ∃ g : B, algebraMap R B f = aB ^ m * g ∧ ¬aB ∣ g ∧
      let q := Ideal.Quotient.mk (Ideal.span {algebraMap R B f})
      RingHom.ker ((algebraMap _ (Localization.Away (q aB))).comp q) = Ideal.span {g} := by
  obtain ⟨g, hg⟩ := pow_dvd_algebraMap_affineBlowup (S := S) ha hf
  have hg' : ¬aB ∣ g := by
    rintro ⟨z, hz⟩
    apply hf'
    exact (pow_dvd_algebraMap_affineBlowup_iff (S := S) ha ha₂ haReg (m + 1) f).mp
      ⟨z, by rw [hg, hz, pow_succ, mul_assoc]⟩
  have hp := prime_algebraMap_affineBlowup (S := S) ha ha₂ haReg
  have hsat (n : ℕ) (x : B) (h : g ∣ aB ^ n * x) : g ∣ x := by
    induction n with
    | zero => simpa using h
    | succ n ih =>
      obtain ⟨y, hy⟩ := h
      rw [pow_succ', mul_assoc] at hy
      have hay : aB ∣ y := (hp.dvd_mul.mp (hy ▸ dvd_mul_right aB _)).resolve_left hg'
      obtain ⟨w, rfl⟩ := hay
      have hcancel : aB * (aB ^ n * x) = aB * (g * w) := by
        rw [hy, mul_left_comm]
      exact ih ⟨w, isRegular_algebraMap_affineBlowup.left hcancel⟩
  refine ⟨g, hg, hg', ?_⟩
  let J : Ideal B := Ideal.span {algebraMap R B f}
  let q : B →+* B ⧸ J := Ideal.Quotient.mk J
  -- A class vanishes in the localization exactly when some power of the exceptional
  -- parameter carries its representative into the total-transform ideal.
  ext x
  simp only [RingHom.mem_ker, RingHom.comp_apply, mem_span_singleton]
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (q aB))]
  constructor
  · rintro ⟨⟨_, n, rfl⟩, hn⟩
    -- Read the coerced element of the powers submonoid in the quotient ring.
    change q aB ^ n * q x = 0 at hn
    rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton, hg] at hn
    exact hsat n x (dvd_trans (dvd_mul_left g _) hn)
  · rintro ⟨y, rfl⟩
    refine ⟨⟨_, m, rfl⟩, ?_⟩
    -- Read the denominator as an ordinary power in the quotient ring.
    change q aB ^ m * q (g * y) = 0
    rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton, hg, ← mul_assoc]
    exact dvd_mul_right _ _

/-- On the same chart the total-transform ideal is the product of the strict-transform
ideal and the `m`th power of the extended center ideal. -/
theorem map_span_singleton_eq_pow_mul_ker_away_quotient_affineBlowup
    [NoZeroDivisors I.AssociatedGraded]
    (ha : a ∈ I) (ha₂ : a ∉ I ^ 2) (haReg : a ∈ nonZeroDivisors R)
    {m : ℕ} {f : R} (hf : f ∈ I ^ m) (hf' : f ∉ I ^ (m + 1)) :
    let q := Ideal.Quotient.mk (Ideal.span {algebraMap R B f})
    (Ideal.span {f}).map (algebraMap R B) = (I.map (algebraMap R B)) ^ m *
      RingHom.ker ((algebraMap _ (Localization.Away (q aB))).comp q) := by
  obtain ⟨g, hg, _, hker⟩ := exists_ker_away_quotient_eq_span_affineBlowup (S := S)
    ha ha₂ haReg hf hf'
  simp only [Ideal.map_span, Set.image_singleton]
  conv_lhs => rw [hg]
  rw [hker, map_algebraMap_affineBlowup ha, Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_span_singleton]

end Ideal
