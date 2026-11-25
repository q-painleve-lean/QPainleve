/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Tropical.BigOperators
public import Mathlib.Algebra.Polynomial.Div
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.ElementaryTransform
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.PositiveSection.Selection

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A high-fiber example on the second Hirzebruch surface

Three binomial transformations followed by a change of lattice frame give a
plane map from the second Hirzebruch surface. Its two open-fiber centers have
orders five and three. Changing to the quadric on the side of the order-three
center exhibits two more order-three stages over the same corner. The degrees
computed from the marked orders distinguish the largest-order preparation from
one that uses two order-zero corners.

The setup uses the elementary transformations in [Lutz's appendix to
Hacking and Keating, Lemma 8.9 and Proposition 8.11][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open scoped BigOperators

namespace QPainleve.SarkisovHighFiber

section Coordinates

variable {R : Type*} [CommSemiring R]

/-- The factor occurring twice in the first homogeneous coordinate of the plane map. -/
def firstFactor (x y : R) : R := (1 + x) ^ 2 + x * y ^ 2

/-- The factor left after cancelling `1 + x` in the third coordinate. -/
def secondFactor (x y : R) : R := (1 + x) ^ 3 + 2 * x * (1 + x) * y ^ 2 + x ^ 2 * y ^ 4

/-- Cancellation of the factor `1 + x` in the numerator of the second plane character. -/
theorem mul_secondFactor (x y : R) :
    (1 + x) * secondFactor x y = firstFactor x y ^ 2 + x ^ 3 * y ^ 4 := by
  unfold firstFactor secondFactor
  ring

/-- The homogeneous coordinates of the specified plane map on the torus. -/
def planeCoordinates (x y : R) : R × R × R :=
  (x * y * firstFactor x y ^ 2, x ^ 4 * y ^ 5, firstFactor x y * secondFactor x y)

/-- The net restricts to the fifth power of `1 + x` on the fiber `y = 0`. -/
@[simp]
theorem planeCoordinates_zero (x : R) : planeCoordinates x 0 = (0, 0, (1 + x) ^ 5) := by
  simp [planeCoordinates, firstFactor, secondFactor, ← pow_add]

private def cornerCoordinates (u v l j z : R) : R × R × R :=
  let b := (1 + u) ^ 2 * l + z
  let c := (1 + u) ^ 3 * l ^ 2 + 2 * z * (1 + u) * l + z ^ 2
  (z * v * b ^ 2, j * z ^ 4 * v, b * c)

/-- The coordinates in the quadric chart `x = z`, `y = 1/v` after clearing the poles. -/
def quadricCorner (z v : R) : R × R × R := cornerCoordinates z v (v ^ 2) 1 z

/-- The coordinates after the first corner blowup and removal of its common exceptional factor. -/
def firstCorner (z v : R) : R × R × R := cornerCoordinates (v * z) v v v z

/-- The coordinates after the second corner blowup, at the ray `(2,-1)`. -/
def secondCorner (z v : R) : R × R × R := cornerCoordinates (v ^ 2 * z) v 1 (v ^ 2) z

/-- The first corner blowup introduces a common factor of `v³`. -/
theorem quadricCorner_mul (z v : R) :
    quadricCorner (v * z) v = v ^ 3 • firstCorner z v := by
  unfold quadricCorner firstCorner cornerCoordinates
  ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- The next blowup on the same corner chain introduces another common factor of `v³`. -/
theorem firstCorner_mul (z v : R) :
    firstCorner (v * z) v = v ^ 3 • secondCorner z v := by
  unfold firstCorner secondCorner cornerCoordinates
  ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- The first corner transform has exceptional restriction with third coordinate `z³`. -/
@[simp]
theorem firstCorner_zero (z : R) : firstCorner z 0 = (0, 0, z ^ 3) := by
  unfold firstCorner cornerCoordinates
  simp [pow_succ, mul_assoc]

/-- The next corner transform has exceptional restriction with third coordinate `(1 + z)³`. -/
@[simp]
theorem secondCorner_zero (z : R) : secondCorner z 0 = (0, 0, (1 + z) ^ 3) := by
  unfold secondCorner cornerCoordinates
  ext <;> simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero, one_pow, mul_one,
    mul_zero]
  ring

end Coordinates

section Fibers

variable {R : Type*} [CommRing R]

/-- The transform at the open-fiber center `(-1,0)` after dividing by `v⁵`. -/
def retainedFiber (t v : R) : R × R × R :=
  let x := -1 + v * t
  let b := t ^ 2 + x
  let c := t ^ 3 + 2 * x * t + x ^ 2 * v
  (x * b ^ 2, x ^ 4, b * c)

/-- The transform at `z = -1` on the ray `(2,-1)` after dividing by `v³`. -/
def oppositeFiber (t v : R) : R × R × R :=
  let z := -1 + v * t
  let b := t + 2 * v * z + v ^ 3 * z ^ 2
  let c := t ^ 2 + z * (3 + 2 * z) + 3 * v ^ 2 * z ^ 2 + v ^ 4 * z ^ 3
  (z * b ^ 2, z ^ 4, b * c)

/-- The first open-fiber center has a common exceptional factor of `v⁵`. -/
theorem planeCoordinates_neg_one_add (t v : R) :
    planeCoordinates (-1 + v * t) v = v ^ 5 • retainedFiber t v := by
  unfold planeCoordinates retainedFiber firstFactor secondFactor
  ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- The other open-fiber center has a common exceptional factor of `v³`. -/
theorem secondCorner_neg_one_add (t v : R) :
    secondCorner (-1 + v * t) v = v ^ 3 • oppositeFiber t v := by
  unfold secondCorner cornerCoordinates oppositeFiber
  ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- The second retained-fiber coordinate is a unit along the exceptional divisor. -/
@[simp]
theorem retainedFiber_snd_fst_zero (t : R) : (retainedFiber t 0).2.1 = 1 := by
  norm_num [retainedFiber]

/-- The second opposite-fiber coordinate is a unit along the exceptional divisor. -/
@[simp]
theorem oppositeFiber_snd_fst_zero (t : R) : (oppositeFiber t 0).2.1 = 1 := by
  norm_num [oppositeFiber]

end Fibers

section Field

variable {K : Type*} [Field K]

/-- Clearing the poles in the quadric chart gives the displayed corner coordinates. -/
theorem quadricCorner_eq_smul_planeCoordinates (x v : K) (hv : v ≠ 0) :
    quadricCorner x v = v ^ 6 • planeCoordinates x v⁻¹ := by
  unfold quadricCorner cornerCoordinates planeCoordinates firstFactor secondFactor
  ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> field_simp

/-- On the open-fiber chart of `F₂` with coordinates `v = 1/y`, `z = xy²`,
the net obtained after two quadric blowups agrees with the specified torus net. -/
theorem secondCorner_eq_planeCoordinates (z v : K) (hv : v ≠ 0) :
    secondCorner z v = planeCoordinates (v ^ 2 * z) v⁻¹ := by
  have h : v ^ 6 • secondCorner z v = v ^ 6 • planeCoordinates (v ^ 2 * z) v⁻¹ := calc
    _ = v ^ 3 • firstCorner (v * z) v := by rw [firstCorner_mul, smul_smul, ← pow_add]
    _ = quadricCorner (v ^ 2 * z) v := by rw [pow_two, mul_assoc, quadricCorner_mul]
    _ = _ := quadricCorner_eq_smul_planeCoordinates _ _ hv
  apply Prod.ext
  · exact mul_left_cancel₀ (pow_ne_zero 6 hv) (congrArg Prod.fst h)
  · exact Prod.ext (mul_left_cancel₀ (pow_ne_zero 6 hv) (congrArg (fun p ↦ p.2.1) h))
      (mul_left_cancel₀ (pow_ne_zero 6 hv) (congrArg (fun p ↦ p.2.2) h))

/-- The zero loci of the restricted nets on the two invariant fibers are
each the single point with fiber coordinate `-1`. -/
theorem fiber_zeros (x z : K) :
    (planeCoordinates x 0 = 0 ↔ x = -1) ∧ (secondCorner z 0 = 0 ↔ z = -1) := by
  simp [Prod.ext_iff, add_eq_zero_iff_eq_neg']

private theorem plane_characters (x y : K)
    (hx : x ≠ 0) (hy : y ≠ 0) (hp : 1 + x ≠ 0) (hb : firstFactor x y ≠ 0) :
    let y₁ := x * y / (1 + x)
    let r := 1 + y₁ ^ 2 / x
    let u := y₁ ^ 4 / (x * r ^ 2)
    u = x ^ 3 * y ^ 4 / firstFactor x y ^ 2 ∧
      (1 + u) * r / y₁ = secondFactor x y / (x * y * firstFactor x y) := by
  dsimp only
  have hr : 1 + (x * y / (1 + x)) ^ 2 / x = firstFactor x y / (1 + x) ^ 2 := by
    unfold firstFactor
    field_simp
  rw [hr]
  constructor
  · field_simp
  · field_simp
    exact (mul_secondFactor x y).symm

private theorem terminal_frame (x y r : K)
    (hx : x ≠ 0) (hy : y ≠ 0) (hr : r ≠ 0)
    (hs : 1 + (y / r) ^ 4 / (x / r ^ 2) ≠ 0) :
    let u := (y / r) ^ 4 / (x / r ^ 2)
    let x₃ := (x / r ^ 2) / (1 + u) ^ 4
    let y₃ := (y / r) / (1 + u)
    y₃ ^ 4 / x₃ = y ^ 4 / (x * r ^ 2) ∧
      y₃⁻¹ = (1 + y ^ 4 / (x * r ^ 2)) * r / y := by
  have hu : (y / r) ^ 4 / (x / r ^ 2) = y ^ 4 / (x * r ^ 2) := by field_simp
  dsimp only
  rw [hu] at hs ⊢
  constructor <;> field_simp
  field_simp at hs
  apply div_self
  intro h
  apply hs
  simp_all [mul_comm]

/-- The three specified binomial transformations and the terminal lattice frame
induce the two affine coordinates of the plane map on their common torus open. -/
theorem binomial_transformations_eq_planeCoordinates (x y : K)
    (hx : x ≠ 0) (hy : y ≠ 0) (hp : 1 + x ≠ 0)
    (hb : firstFactor x y ≠ 0) (hc : secondFactor x y ≠ 0) :
    let y₁ := x * y / (1 + x)
    let r := 1 + y₁ ^ 2 / x
    let x₂ := x / r ^ 2
    let y₂ := y₁ / r
    let u := y₂ ^ 4 / x₂
    let x₃ := x₂ / (1 + u) ^ 4
    let y₃ := y₂ / (1 + u)
    (y₃ ^ 4 / x₃, y₃⁻¹) =
      ((planeCoordinates x y).2.1 / (planeCoordinates x y).1,
        (planeCoordinates x y).2.2 / (planeCoordinates x y).1) := by
  let y₁ := x * y / (1 + x)
  let r := 1 + y₁ ^ 2 / x
  have hy₁ : y₁ ≠ 0 := div_ne_zero (mul_ne_zero hx hy) hp
  have hr' : r = firstFactor x y / (1 + x) ^ 2 := by unfold r y₁ firstFactor; field_simp
  have hr : r ≠ 0 := hr' ▸ div_ne_zero hb (pow_ne_zero _ hp)
  obtain ⟨hu, hw⟩ := plane_characters x y hx hy hp hb
  have hu' : (y₁ / r) ^ 4 / (x / r ^ 2) = y₁ ^ 4 / (x * r ^ 2) := by field_simp
  have hlast : 1 + (y₁ / r) ^ 4 / (x / r ^ 2) ≠ 0 := by
    rw [hu']
    intro h
    -- Rewrite the numerator in the second plane character using the local chart coordinates.
    have hw' : (1 + y₁ ^ 4 / (x * r ^ 2)) * r / y₁ =
        secondFactor x y / (x * y * firstFactor x y) := hw
    rw [h, zero_mul, zero_div] at hw'
    exact div_ne_zero hc (mul_ne_zero (mul_ne_zero hx hy) hb) hw'.symm
  obtain ⟨h₁, h₂⟩ := terminal_frame x y₁ r hx hy₁ hr hlast
  apply Prod.ext
  · exact h₁.trans (hu.trans (by unfold planeCoordinates; dsimp; field_simp))
  · exact h₂.trans (hw.trans (by unfold planeCoordinates; dsimp; field_simp))

end Field

section Vanishing

open Polynomial

variable (R : Type*) [CommRing R] [Nontrivial R]

local notation "u" => C (X : Polynomial R)
local notation "v" => (X : Polynomial (Polynomial R))

/-- The four chart substitutions have common exceptional orders `5, 3, 3, 3`
exactly. Each order is the largest power of the outer polynomial variable
that divides all three homogeneous coordinates. -/
theorem exceptional_orders :
    let exactOrder (m : ℕ) (p : Polynomial (Polynomial R) × Polynomial (Polynomial R) ×
        Polynomial (Polynomial R)) :=
      (∃ q, p = v ^ m • q) ∧ ¬ ∃ q, p = v ^ (m + 1) • q
    exactOrder 5 (planeCoordinates (-1 + v * u) v) ∧
      exactOrder 3 (quadricCorner (v * u) v) ∧
      exactOrder 3 (firstCorner (v * u) v) ∧
      exactOrder 3 (secondCorner (-1 + v * u) v) := by
  intro exactOrder
  have hexact {m : ℕ} {p q} (hq : p = v ^ m • q)
      {f : Polynomial (Polynomial R) × Polynomial (Polynomial R) × Polynomial (Polynomial R) →
        Polynomial (Polynomial R)} (hf : ∀ a t, f (a • t) = a * f t)
      (h₀ : (f q).eval 0 ≠ 0) : exactOrder m p := by
    refine ⟨⟨q, hq⟩, ?_⟩
    rintro ⟨s, hs⟩
    have he := congrArg (fun w ↦ (f w).coeff m) (hq.symm.trans hs)
    simp only [hf, coeff_X_pow_mul', le_rfl, ↓reduceIte, tsub_self,
      Nat.not_succ_le_self, coeff_zero_eq_eval_zero] at he
    exact h₀ he
  refine ⟨hexact (planeCoordinates_neg_one_add u v) (f := fun p ↦ p.2.1) (fun _ _ ↦ rfl) ?_,
    hexact (quadricCorner_mul u v) (f := fun p ↦ p.2.2) (fun _ _ ↦ rfl) ?_,
    hexact (firstCorner_mul u v) (f := fun p ↦ p.2.2) (fun _ _ ↦ rfl) ?_,
    hexact (secondCorner_neg_one_add u v) (f := fun p ↦ p.2.1) (fun _ _ ↦ rfl) ?_⟩
  · simp [retainedFiber, show (-1 : Polynomial R) ^ 4 = 1 by ring]
  · simp [firstCorner, cornerCoordinates, pow_succ, mul_assoc]
  · have hn : (1 + (X : Polynomial R)) ^ 3 ≠ 0 := by
      intro h
      simpa using congrArg (fun f : Polynomial R ↦ f.eval 0) h
    have h : ((secondCorner u v).2.2).eval 0 = (1 + (X : Polynomial R)) ^ 3 := by
      simp [secondCorner, cornerCoordinates]
      ring
    exact h.symm ▸ hn
  · simp [oppositeFiber, show (-1 : Polynomial R) ^ 4 = 1 by ring]

end Vanishing

section Weights

open MinTropical

/-- The minimum weight obtained by evaluating the three plane coordinates in
Mathlib's min-plus semiring. The coefficient map takes positive naturals to
multiplicative one, so the resulting weight depends on the support. -/
def supportWeight (w : ℤ × ℤ) : WithTop ℤ :=
  let p := planeCoordinates (trop (w.1 : WithTop ℤ)) (trop (w.2 : WithTop ℤ))
  untrop (p.1 + p.2.1 + p.2.2)

/-- The computed weight is the minimum over the union of the monomial supports
of the three plane coordinates over `ℕ`. -/
theorem supportWeight_eq_inf (w : ℤ × ℤ) :
    let p := planeCoordinates (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℕ)
      (MvPolynomial.X (1 : Fin 2))
    supportWeight w = (p.1.support ∪ p.2.1.support ∪ p.2.2.support).inf
      (fun m ↦ (((m 0 : ℤ) * w.1 + (m 1 : ℤ) * w.2 : ℤ) : WithTop ℤ)) := by
  intro p
  let value : Fin 2 → MinTropical (WithTop ℤ) := ![trop ↑w.1, trop ↑w.2]
  let e := MvPolynomial.eval₂Hom (Nat.castRingHom (MinTropical (WithTop ℤ))) value
  have h : supportWeight w = untrop (e (p.1 + p.2.1 + p.2.2)) := by
    simp [supportWeight, p, e, value, planeCoordinates, firstFactor, secondFactor]
  have hs : (p.1 + p.2.1 + p.2.2).support = p.1.support ∪ p.2.1.support ∪ p.2.2.support := by
    ext m
    simp [Nat.add_eq_zero_iff]
    omega
  rw [h, ← hs]
  dsimp only [e]
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq', Finset.untrop_sum']
  refine Finset.inf_congr rfl ?_
  intro m hm
  have hcoeff : untrop ((p.1 + p.2.1 + p.2.2).coeff m : MinTropical (WithTop ℤ)) = 0 := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (MvPolynomial.mem_support_iff.mp hm)
    rw [hj, ← nsmul_one, MinTropical.succ_nsmul, untrop_one]
  simp only [Function.comp_apply, untrop_mul, Nat.coe_castRingHom,
    hcoeff, zero_add, MinTropical.untrop_prod, untrop_pow,
    Fin.sum_univ_two, value, Matrix.cons_val_zero, Matrix.cons_val_one, untrop_trop,
    ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul]

/-- The monomial second coordinate gives a finite upper bound for the
minimum weight, at every integral ray. -/
theorem supportWeight_ne_top (w : ℤ × ℤ) : supportWeight w ≠ ⊤ := by
  have hle : supportWeight w ≤ ((4 • w.1 + 5 • w.2 : ℤ) : WithTop ℤ) := by
    simp only [supportWeight, planeCoordinates, untrop_add, untrop_mul, untrop_pow,
      untrop_trop, ← WithTop.coe_nsmul, ← WithTop.coe_add]
    exact (min_le_left _ _).trans (min_le_right _ _)
  exact fun h ↦ WithTop.coe_ne_top (top_unique (h ▸ hle))

/-- Removing the fixed components on two adjacent rays leaves the order at
their corner as the minimum total degree in the two local coordinates. -/
def cornerOrder (u v : ℤ × ℤ) : ℤ :=
  (supportWeight (u + v)).untop (supportWeight_ne_top _) -
    (supportWeight u).untop (supportWeight_ne_top _) -
    (supportWeight v).untop (supportWeight_ne_top _)

end Weights

/-- The support weights in cyclic order on `F₂`. Only the positive section
has a negative weight, giving moving class `5(S + 2A)`. -/
theorem hirzebruch_supportWeights :
    ([(1, 0), (0, 1), (-1, 0), (2, -1)] : List (ℤ × ℤ)).map supportWeight =
      [0, 0, (-5 : ℤ), 0] := by decide

/-- The support weights on the quadric give fiber coefficients five and six. -/
theorem quadric_supportWeights :
    ([(1, 0), (0, 1), (-1, 0), (0, -1)] : List (ℤ × ℤ)).map supportWeight =
      [0, 0, (-5 : ℤ), (-6 : ℤ)] := by decide

/-- The successive corner orders on the positive section, starting at
its intersection with the fiber of ray `(2,-1)`. -/
def sectionOrder (j : Fin 6) : ℤ := cornerOrder (-1, 0) (2 - (j.val : ℤ), -1)

/-- The six nonzero corner orders, in the order of the successive blowups. -/
theorem sectionOrder_eq : sectionOrder = ![2, 2, 2, 1, 1, 1] := by
  funext j
  fin_cases j <;> decide

/-- The other three original corners of `F₂` have order zero. The additional
corner on the zero-order preparation side still has order zero. -/
theorem other_cornerOrders :
    cornerOrder (1, 0) (0, 1) = 0 ∧ cornerOrder (0, 1) (-1, 0) = 0 ∧
    cornerOrder (2, -1) (1, 0) = 0 ∧ cornerOrder (-1, 0) (-1, 1) = 0 := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- The positive-section rule selects the first two order-two stages. -/
theorem select_first_two :
    IsPositiveSectionSelection Finset.univ sectionOrder 2 ({0, 1} : Finset (Fin 6)) := by
  rw [sectionOrder_eq]
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- The section orders have total nine, and the orders selected by the
positive-section rule have total four. -/
theorem sum_sectionOrder : (∑ j, sectionOrder j) = 9 ∧
    (∑ j ∈ ({0, 1} : Finset (Fin 6)), sectionOrder j) = 4 := by
  rw [sectionOrder_eq]
  exact ⟨by decide, by decide⟩

/-- The two open-fiber orders together with the six corner orders account
for both homaloidal sums of the initial moving class `10A + 5S`. -/
theorem homaloidal_sums :
    (∑ j, sectionOrder j ^ 2) + 5 ^ 2 + 3 ^ 2 = 2 * 10 * 5 - 2 * 5 ^ 2 - 1 ∧
    (∑ j, sectionOrder j) + 5 + 3 = 2 * 10 + (2 - 2) * 5 - 3 := by
  rw [sectionOrder_eq]
  exact ⟨by decide, by decide⟩

/-- With the two extra corner stages of the quadric chart, the same net has
four high orders. The remaining four stages have the orders of the tail of
the original positive section. Their two homaloidal sums give square `59`
and total order `19` for the bidegree `(6,5)`. -/
theorem quadric_homaloidal_sums :
    let m : List ℤ := [5, 3, 3, 3] ++ (List.ofFn sectionOrder).drop 2
    m.filter (fun u ↦ 5 < 2 * u) = [5, 3, 3, 3] ∧
      (m.map (· ^ 2)).sum = 2 * 6 * 5 - 1 ∧ m.sum = 19 := by
  rw [sectionOrder_eq]
  exact ⟨by decide, by decide, by decide⟩

/-- The case-C preparation chooses orders two and two, giving fiber
coefficient six on the quadric. The retained orders five and three then
satisfy the strict two-center bound and give exit fiber degree three. -/
theorem selected_orders_degree_drop :
    let a := (10 : ℤ) - ∑ j ∈ ({0, 1} : Finset (Fin 6)), sectionOrder j
    let b := (5 : ℤ)
    a = 6 ∧ a < 5 + 3 ∧ a + b - 5 - 3 = 3 ∧
      ∀ M, hirzebruchSarkisovBidegree (a + b - 5 - 3).toNat M <
        hirzebruchSarkisovBidegree b.toNat 17 := by
  simp only [sum_sectionOrder.2]
  refine ⟨rfl, by decide, rfl, fun M ↦ ?_⟩
  simp only [Prod.Lex.lt_iff, ofLex_hirzebruchSarkisovBidegree]
  exact Or.inl (by decide)

/-- Choosing the two zero-order corners on the other side leaves coefficient
ten. The retained orders fail the strict two-center bound and the proposed
exit formula gives seven, above the original fiber degree five. -/
theorem zero_order_preparation_degree_increases :
    let a := (10 : ℤ) - cornerOrder (-1, 0) (0, 1) - cornerOrder (-1, 0) (-1, 1)
    let b := (5 : ℤ)
    a = 10 ∧ 3 + 5 ≤ a ∧ a + b - 3 - 5 = 7 ∧ b < a + b - 3 - 5 := by
  simp only [other_cornerOrders.2.2.2, sub_zero]
  decide

end QPainleve.SarkisovHighFiber
