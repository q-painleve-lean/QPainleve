/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Signature
public import Mathlib.Analysis.Convex.Cone.Basic
public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
public import TauCeti.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.Chow.Ample
import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
import QPainleve.AlgebraicGeometry.IntersectionNumber.GlobalGeneration
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The closed cone of curves on a smooth projective surface

The cone is generated in the real Picard space by the classes of integral curves and then
closed. In a finite-dimensional real Picard space with nondegenerate intersection form,
an integral curve of negative self-intersection spans an exposed ray. An ample class adjusted
by a multiple of the curve annihilates it. Bounds from nef twists of ample powers ensure
that the supporting functional cuts out exactly the ray even after taking the closure.

See [O. Debarre, *Introduction to Mori Theory*, Proposition 5.9(b)][Debarre] for the extremal
ray theorem.

[Debarre]: https://perso.imj-prg.fr/wp-content/uploads/debarre-pub/M2.pdf#page=50
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Filter TopologicalSpace
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry.Chow

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "f" => (X ↘ Spec (CommRingCat.of k))
local notation "V(" S ")" => (ℝ ⊗[ℤ] Additive (LineBundleClass S))
local notation "B" => realIntersectionBilinForm k X
local notation "ι" => (fun a : LineBundleClass X ↦ (1 : ℝ) ⊗ₜ[ℤ] Additive.ofMul a)

/-- The class of the prime divisor of a codimension-one point in the real Picard space. -/
def realPrimeDivisorClass (p : CodimensionOnePoint X) : V(X) :=
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  ι (LineBundleClass.primeDivisorClass p)

/-- The real prime divisor class is the image of its integral class under extension of
scalars. -/
theorem realPrimeDivisorClass_def (p : CodimensionOnePoint X) :
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    realPrimeDivisorClass k p = ι (LineBundleClass.primeDivisorClass p) := (rfl)

local notation "c" => realPrimeDivisorClass k (X := X)

section IntersectionBounds

variable [Infinite k]

/-- Pairing an integral line-bundle class with a real prime divisor class recovers the
integral intersection number. -/
@[simp]
theorem realIntersectionBilinForm_one_tmul_realPrimeDivisorClass
    (a : LineBundleClass X) (p : CodimensionOnePoint X) :
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    B (ι a) (c p) = (classIntersectionNumber k X a (LineBundleClass.primeDivisorClass p) : ℝ) := by
  simp only [realPrimeDivisorClass_def, realIntersectionBilinForm_tmul, one_mul, toMul_ofMul]

/-- An ample class has positive real intersection with every prime divisor class. -/
theorem realIntersectionBilinForm_realPrimeDivisorClass_pos
    {a : LineBundleClass X} (ha : a.IsAmple) (p : CodimensionOnePoint X) :
    0 < B (ι a) (c p) := by
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  rw [realIntersectionBilinForm_one_tmul_realPrimeDivisorClass]
  exact_mod_cast classIntersectionNumber_primeDivisorClass_pos_of_isAmple k hX ha p

/-- Distinct prime divisors have nonnegative real intersection. -/
theorem realIntersectionBilinForm_realPrimeDivisorClass_nonneg
    {p q : CodimensionOnePoint X} (hpq : p ≠ q) :
    0 ≤ B (c p) (c q) := by
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  rw [realPrimeDivisorClass_def k p, realIntersectionBilinForm_one_tmul_realPrimeDivisorClass]
  exact_mod_cast classIntersectionNumber_primeDivisorClass_nonneg_of_ne k hX hpq

private theorem exists_abs_realIntersectionBilinForm_le
    {a : LineBundleClass X} (ha : a.IsAmple) (b : LineBundleClass X) :
    ∃ n : ℕ, ∀ p, |B (ι b) (c p)| ≤ (n : ℝ) * B (ι a) (c p) := by
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  obtain ⟨n, hn, hn'⟩ := ((ha.eventually_isNef_mul_pow b f).and
    (ha.eventually_isNef_mul_pow b⁻¹ f)).exists
  have integral (d : LineBundleClass X) (hd : (d * a ^ n).IsNef k f) (p : CodimensionOnePoint X) :
      0 ≤ B (ι d) (c p) + (n : ℝ) * B (ι a) (c p) := by
    have h := (isNef_iff_classIntersectionNumber_nonneg k hX _).mp hd p
    have he : ι (d * a ^ n) = ι d + n • ι a := by
      dsimp only
      rw [← Nat.cast_smul_eq_nsmul ℤ, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_add]
      rfl
    have hreal : 0 ≤ B (ι (d * a ^ n)) (c p) := by
      rw [realIntersectionBilinForm_one_tmul_realPrimeDivisorClass]
      exact_mod_cast h
    rw [he, ← Nat.cast_smul_eq_nsmul ℝ, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hreal
    exact hreal
  refine ⟨n, fun p ↦ abs_le.mpr ⟨by linarith [integral b hn p], ?_⟩⟩
  have hinv : ι b⁻¹ = -ι b := by
    dsimp only
    rw [← TensorProduct.tmul_neg]
    rfl
  have hp := integral b⁻¹ hn' p
  rw [hinv, map_neg, LinearMap.neg_apply] at hp
  linarith

private theorem abs_sub_le_on_primeDivisors {a b : LineBundleClass X} (ha : a.IsAmple)
    (p : CodimensionOnePoint X) (l : V(X) → ℝ) (hl : l (c p) = 0)
    (hle : ∀ q, q ≠ p → B (ι a) (c q) ≤ l (c q)) :
    ∃ M : ℝ, ∀ q,
      |B (ι b) (c q) - (B (ι b) (c p) / B (ι a) (c p)) * B (ι a) (c q)| ≤
        M * l (c q) := by
  obtain ⟨n, hn⟩ := exists_abs_realIntersectionBilinForm_le k ha b
  let t := B (ι b) (c p) / B (ι a) (c p)
  have hp := realIntersectionBilinForm_realPrimeDivisorClass_pos k ha p
  refine ⟨(n : ℝ) + |t|, fun q ↦ ?_⟩
  by_cases hqp : q = p
  · subst q
    rw [div_mul_cancel₀ _ hp.ne', sub_self, abs_zero, hl, mul_zero]
  · have hq := realIntersectionBilinForm_realPrimeDivisorClass_pos k ha q
    calc
      |B (ι b) (c q) - t * B (ι a) (c q)| ≤ |B (ι b) (c q)| + |t * B (ι a) (c q)| :=
        abs_sub _ _
      _ ≤ ((n : ℝ) + |t|) * B (ι a) (c q) := by
        rw [abs_mul, abs_of_pos hq, add_mul]
        exact add_le_add_left (hn q) _
      _ ≤ ((n : ℝ) + |t|) * l (c q) :=
        mul_le_mul_of_nonneg_left (hle q hqp) (add_nonneg (Nat.cast_nonneg _) (abs_nonneg _))

end IntersectionBounds

variable [TopologicalSpace V(X)] [IsTopologicalAddGroup V(X)] [ContinuousSMul ℝ V(X)]

/-- The closure of the cone of nonnegative real combinations of prime divisor classes. -/
def closedCurveCone : ProperCone ℝ V(X) where
  toSubmodule := (PointedCone.hull ℝ (Set.range c)).closure
  isClosed' := isClosed_closure

/-- The carrier of the closed cone of curves is the closure of the span over nonnegative
scalars of the prime divisor classes. -/
theorem coe_closedCurveCone :
    (closedCurveCone k (X := X) : Set V(X)) =
      closure (PointedCone.hull ℝ (Set.range c) : Set V(X)) := (rfl)

/-- A prime divisor class belongs to the closed cone of curves. -/
@[simp]
theorem realPrimeDivisorClass_mem_closedCurveCone (p : CodimensionOnePoint X) :
    c p ∈ closedCurveCone k := by
  rw [← SetLike.mem_coe, coe_closedCurveCone]
  exact subset_closure (Submodule.subset_span (Set.mem_range_self p))

/-- Nonnegativity of a continuous linear functional on the closed cone of curves is
equivalent to nonnegativity on every prime divisor class. -/
theorem nonneg_on_closedCurveCone_iff (l : V(X) →L[ℝ] ℝ) :
    (∀ x ∈ closedCurveCone k, 0 ≤ l x) ↔ ∀ p, 0 ≤ l (c p) := by
  refine ⟨fun h p ↦ h _ (realPrimeDivisorClass_mem_closedCurveCone k p), fun h x hx ↦ ?_⟩
  let C := (ProperCone.positive ℝ ℝ).comap l
  have hle : PointedCone.hull ℝ (Set.range c) ≤ C.toPointedCone :=
    Submodule.span_le.mpr (by rintro _ ⟨p, rfl⟩; exact h p)
  rw [← SetLike.mem_coe, coe_closedCurveCone] at hx
  exact C.isClosed.closure_subset_iff.mpr hle hx

private theorem apply_eq_zero_of_abs_le_on_primeDivisors
    {l g : V(X) →L[ℝ] ℝ} {x : V(X)} (hx : x ∈ closedCurveCone k) (hl : l x = 0)
    (M : ℝ) (h : ∀ p, |g (c p)| ≤ M * l (c p)) : g x = 0 := by
  have lower : 0 ≤ (M • l + g) x :=
    (nonneg_on_closedCurveCone_iff k _).mpr
      (fun p ↦ by
        simp only [add_apply, smul_apply, smul_eq_mul]
        linarith [(abs_le.mp (h p)).1]) x hx
  have upper : 0 ≤ (M • l - g) x :=
    (nonneg_on_closedCurveCone_iff k _).mpr
      (fun p ↦ by
        simp only [sub_apply, smul_apply, smul_eq_mul]
        linarith [(abs_le.mp (h p)).2]) x hx
  simp only [add_apply, sub_apply,
    smul_apply, smul_eq_mul, hl, mul_zero, zero_add, zero_sub] at lower upper
  linarith

variable [Infinite k] [FiniteDimensional ℝ V(X)] [T2Space V(X)]

/-- A prime curve of negative self-intersection has a supporting functional whose zero set
in the closed curve cone is exactly the ray of its class. -/
theorem exists_nonneg_closedCurveCone_eq_zero_iff_mem_hull_singleton
    (hB : (B).Nondegenerate) (p : CodimensionOnePoint X) (hp : B (c p) (c p) < 0) :
    ∃ l : V(X) →L[ℝ] ℝ, (∀ x ∈ closedCurveCone k, 0 ≤ l x) ∧
      ∀ x ∈ closedCurveCone k, l x = 0 ↔ x ∈ PointedCone.hull ℝ {c p} := by
  obtain ⟨a, ha⟩ := X.exists_isAmple_of_isProjectiveOver k
  let A := (B (ι a)).toContinuousLinearMap
  let P := (B (c p)).toContinuousLinearMap
  let l := A - (A (c p) / P (c p)) • P
  have ha' (q : CodimensionOnePoint X) : 0 < A (c q) :=
    realIntersectionBilinForm_realPrimeDivisorClass_pos k ha q
  have hp₀ : P (c p) ≠ 0 := hp.ne
  have hl : l (c p) = 0 := by
    simp only [l, sub_apply, smul_apply, smul_eq_mul, div_mul_cancel₀ _ hp₀, sub_self]
  have hle (q : CodimensionOnePoint X) (hq : q ≠ p) : A (c q) ≤ l (c q) := by
    have h : 0 ≤ P (c q) := realIntersectionBilinForm_realPrimeDivisorClass_nonneg k hq.symm
    have hneg : A (c p) / P (c p) ≤ 0 := (div_neg_of_pos_of_neg (ha' p) hp).le
    simp only [l, sub_apply, smul_apply, smul_eq_mul]
    exact (le_sub_iff_add_le).mpr (add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg hneg h))
  have nonnegA := (nonneg_on_closedCurveCone_iff k A).mpr (fun q ↦ (ha' q).le)
  refine ⟨l, (nonneg_on_closedCurveCone_iff k l).mpr (fun q ↦ ?_), ?_⟩
  · by_cases hq : q = p
    · simp [hq, hl]
    · exact (ha' q).le.trans (hle q hq)
  intro x hx
  refine ⟨fun hzero ↦ ?_, ?_⟩
  · -- Subtract the multiple of the curve with the same ample degree as x.
    -- Pairings with integral classes detect the difference and are bounded by l.
    let t := A x / A (c p)
    have hpair (b : LineBundleClass X) : B (ι b) (x - t • c p) = 0 := by
      let G := (B (ι b)).toContinuousLinearMap
      let g := G - (G (c p) / A (c p)) • A
      obtain ⟨M, hM⟩ := abs_sub_le_on_primeDivisors k ha (b := b) p l hl hle
      have hz := apply_eq_zero_of_abs_le_on_primeDivisors k (g := g) hx hzero M hM
      simp only [g, sub_apply, smul_apply, smul_eq_mul,
        G, A, LinearMap.coe_toContinuousLinearMap'] at hz
      rw [sub_eq_zero] at hz
      rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero]
      rw [hz]
      simp only [t, A, LinearMap.coe_toContinuousLinearMap']
      ring
    have hzero' : x - t • c p = 0 := by
      refine hB.2 (x - t • c p) fun y ↦ ?_
      induction y using TensorProduct.inductionOn with
      | tmul r b =>
        rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, LinearMap.smul_apply]
        have hz : B ((1 : ℝ) ⊗ₜ[ℤ] b) (x - t • c p) = 0 := hpair b.toMul
        rw [hz, smul_zero]
      | add y z hy hz => simp [map_add, hy, hz]
    exact PointedCone.mem_hull_singleton.mpr
      ⟨t, div_nonneg (nonnegA x hx) (ha' p).le, (sub_eq_zero.mp hzero').symm⟩
  · intro hx'
    obtain ⟨t, -, rfl⟩ := PointedCone.mem_hull_singleton.mp hx'
    simp [hl]

/-- A prime curve of negative self-intersection generates an extremal ray of the closed
cone of curves. -/
theorem isFaceOf_hull_singleton_realPrimeDivisorClass (hB : (B).Nondegenerate)
    (p : CodimensionOnePoint X) (hp : B (c p) (c p) < 0) :
    (PointedCone.hull ℝ {c p}).IsFaceOf (closedCurveCone k).toPointedCone := by
  obtain ⟨l, hl, hzero⟩ := exists_nonneg_closedCurveCone_eq_zero_iff_mem_hull_singleton k hB p hp
  have hle : PointedCone.hull ℝ {c p} ≤ (closedCurveCone k).toPointedCone :=
    Submodule.span_le.mpr
      (Set.singleton_subset_iff.mpr (realPrimeDivisorClass_mem_closedCurveCone k p))
  refine PointedCone.IsFaceOf.of_mem_of_add_mem_left hle (fun {x y} hx hy hxy ↦ ?_)
  have h := (hzero (x + y) ((closedCurveCone k).add_mem hx hy)).mpr hxy
  rw [map_add] at h
  exact (hzero x hx).mp (by linarith [hl x hx, hl y hy])

end TauCeti.AlgebraicGeometry.Chow
