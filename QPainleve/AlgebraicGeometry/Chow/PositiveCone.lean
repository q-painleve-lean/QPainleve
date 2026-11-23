/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Signature
public import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef
public import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
public import QPainleve.Topology.Algebra.QuadraticForm.PositiveCone
public import TauCeti.AlgebraicGeometry.LineBundle.Ample

import QPainleve.AlgebraicGeometry.Chow.Ample
import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
import QPainleve.AlgebraicGeometry.LineBundle.Ample

/-!
# The ample component of the real Picard positive cone

On a smooth integral projective surface whose real Picard space is finite-dimensional
and whose intersection form is nondegenerate of positive index one, all ample classes
select the same positive component. Its closure is given by nonnegative square and
nonnegative intersection with an ample class. A nonzero nef isotropic class lies in
this closure and detects the same component by its own intersection pairing.

For the description of the positive component by an ample class, see Gross, Hacking
and Keel, [*Moduli of surfaces with an anti-canonical cycle*, Lemma 2.14][GHK].

[GHK]: https://paulhacking.github.io/mlp.pdf#page=13
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace QuadraticMap
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry.Chow

universe u

variable (k : Type u) [Field k] [Infinite k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "Pic(" S ")" => Additive (LineBundleClass S)
local notation "V(" S ")" => (ℝ ⊗[ℤ] Pic(S))
local notation "B" => realIntersectionBilinForm k X
local notation "Q" => (LinearMap.BilinMap.toQuadraticMap B)
local notation "ι" => (fun a : LineBundleClass X ↦ (1 : ℝ) ⊗ₜ[ℤ] Additive.ofMul a)
local notation "C(" h ")" => connectedComponentIn (Set.ofPred (fun x : V(X) ↦ 0 < Q x)) (ι h)
local notation "f" => (X ↘ Spec (CommRingCat.of k))

/-- A real Picard class which pairs nonnegatively with every prime divisor also
pairs nonnegatively with every ample class. -/
theorem realIntersectionBilinForm_nonneg_of_isAmple {d : V(X)} {h : LineBundleClass X}
    (hh : h.IsAmple)
    (hd : let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
        (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      ∀ p : CodimensionOnePoint X, 0 ≤ B d (ι (LineBundleClass.primeDivisorClass p))) :
    0 ≤ B d (ι h) := by
  have : IsNoetherian X := isNoetherian_of_finiteType f
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  obtain ⟨n, D, hn, hD, -, hclass⟩ :=
    hh.exists_effectiveWeilDivisor_pow_eq f (hX.symm ▸ (by decide : (0 : WithBot ℕ∞) < 2))
  let φ : Pic(X) →+ ℝ := (B d).toAddMonoidHom.comp (TensorProduct.mk ℤ ℝ Pic(X) 1).toAddMonoidHom
  have hmul : Scheme.CartierDivisor.weilToLineBundleClassHom X D = n • Additive.ofMul h := by
    exact Additive.toMul.injective hclass
  have hp (p : CodimensionOnePoint X) :
      0 ≤ φ (Additive.ofMul (LineBundleClass.primeDivisorClass p)) := hd p
  have hexpand : φ (Scheme.CartierDivisor.weilToLineBundleClassHom X D) =
      D.sum (fun p n ↦ n • φ (Additive.ofMul (LineBundleClass.primeDivisorClass p))) := by
    calc
      _ = φ (Scheme.CartierDivisor.weilToLineBundleClassHom X (D.sum Finsupp.single)) := by
        rw [Finsupp.sum_single]
      _ = _ := by
        rw [map_finsuppSum, map_finsuppSum]
        simp only [Scheme.CartierDivisor.weilToLineBundleClassHom_single,
          ← LineBundleClass.primeDivisorClass_def, map_zsmul]
  have hsum : 0 ≤ φ (Scheme.CartierDivisor.weilToLineBundleClassHom X D) := by
    rw [hexpand]
    exact Finset.sum_nonneg fun p _ ↦ zsmul_nonneg (hp p) (hD p)
  rw [hmul, map_nsmul, nsmul_eq_mul] at hsum
  exact nonneg_of_mul_nonneg_right hsum (by exact_mod_cast hn)

/-- In the real Picard space an ample class has positive intersection with every ample
class, including itself. -/
theorem realIntersectionBilinForm_pos_of_isAmple {h h' : LineBundleClass X}
    (hh : h.IsAmple) (hh' : h'.IsAmple) : 0 < B (ι h) (ι h') := by
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  simp only [realIntersectionBilinForm_tmul, one_mul, toMul_ofMul, Int.cast_pos]
  exact classIntersectionNumber_pos_of_isAmple k hX hh hh'

variable [FiniteDimensional ℝ V(X)] [TopologicalSpace V(X)] [IsModuleTopology ℝ V(X)]
  {h : LineBundleClass X}

/-- The positive-cone component containing an ample class is given by positive square
and positive intersection with that ample class. -/
theorem connectedComponentIn_pos_eq_of_isAmple (hQ : (Q).Nondegenerate)
    (hsig : sigPos Q ≤ 1) (hh : h.IsAmple) :
    C(h) = {x | 0 < Q x ∧ 0 < B (ι h) x} := by
  have hpos : 0 < Q (ι h) := realIntersectionBilinForm_pos_of_isAmple k hh hh
  rw [QuadraticForm.connectedComponentIn_pos_eq hQ hsig hpos]
  simp only [polar_realIntersectionBilinForm, mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)]

/-- The ample classes belong to a single component of the positive cone. -/
theorem connectedComponentIn_pos_eq_of_isAmple_of_isAmple (hQ : (Q).Nondegenerate)
    (hsig : sigPos Q ≤ 1) {h' : LineBundleClass X} (hh : h.IsAmple)
    (hh' : h'.IsAmple) : C(h') = C(h) := by
  symm
  apply connectedComponentIn_eq
  rw [connectedComponentIn_pos_eq_of_isAmple k hQ hsig hh]
  exact ⟨realIntersectionBilinForm_pos_of_isAmple k hh' hh',
    realIntersectionBilinForm_pos_of_isAmple k hh hh'⟩

/-- Weakening the two inequalities defining the ample component gives its closure. -/
theorem closure_connectedComponentIn_pos_eq_of_isAmple (hQ : (Q).Nondegenerate)
    (hsig : sigPos Q ≤ 1) (hh : h.IsAmple) :
    closure C(h) = {x | 0 ≤ Q x ∧ 0 ≤ B (ι h) x} := by
  have hpos : 0 < Q (ι h) := realIntersectionBilinForm_pos_of_isAmple k hh hh
  rw [QuadraticForm.closure_connectedComponentIn_pos_eq hQ hsig hpos]
  simp only [polar_realIntersectionBilinForm,
    mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)]

/-- A nonzero real Picard class of nonnegative square which pairs nonnegatively with
every prime divisor detects the ample component. This applies to nef isotropic classes. -/
theorem connectedComponentIn_pos_eq_of_nonneg_of_isAmple (hQ : (Q).Nondegenerate)
    (hsig : sigPos Q ≤ 1) (hh : h.IsAmple) {d : V(X)} (hd₀ : d ≠ 0)
    (hdd : 0 ≤ Q d)
    (hd : let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
        (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      ∀ p : CodimensionOnePoint X, 0 ≤ B d (ι (LineBundleClass.primeDivisorClass p))) :
    C(h) = {x | 0 < Q x ∧ 0 < B d x} := by
  have hpos : 0 < Q (ι h) := realIntersectionBilinForm_pos_of_isAmple k hh hh
  have hpair : 0 ≤ polar Q (ι h) d := by
    rw [polar_comm, polar_realIntersectionBilinForm]
    exact mul_nonneg (by norm_num) (realIntersectionBilinForm_nonneg_of_isAmple k hh hd)
  rw [QuadraticForm.connectedComponentIn_pos_eq_of_nonneg hQ hsig hpos hdd hd₀ hpair]
  simp only [polar_realIntersectionBilinForm, mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)]

/-- The real image of a nef line bundle class with nonnegative square detects the
ample component as long as its real image is nonzero. -/
theorem connectedComponentIn_pos_eq_of_isNef (hQ : (Q).Nondegenerate)
    (hsig : sigPos Q ≤ 1) (hh : h.IsAmple) {d : LineBundleClass X}
    (hd : d.IsNef k (X ↘ Spec (.of k))) (hd₀ : ι d ≠ 0)
    (hdd : 0 ≤ classIntersectionNumber k X d d) :
    C(h) = {x | 0 < Q x ∧ 0 < B (ι d) x} := by
  apply connectedComponentIn_pos_eq_of_nonneg_of_isAmple k hQ hsig hh hd₀
  · simp only [LinearMap.BilinMap.toQuadraticMap_apply, realIntersectionBilinForm_tmul,
      one_mul, toMul_ofMul]
    exact_mod_cast hdd
  · have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
    intro _ _ p
    simp only [realIntersectionBilinForm_tmul, one_mul, toMul_ofMul]
    exact_mod_cast (isNef_iff_classIntersectionNumber_nonneg k hX d).mp hd p

/-- Two real Picard classes in the closure of the ample component have nonnegative
intersection. -/
theorem realIntersectionBilinForm_nonneg_of_mem_closure_connectedComponentIn_pos
    (hQ : (Q).Nondegenerate) (hsig : sigPos Q ≤ 1) (hh : h.IsAmple)
    {x y : V(X)} (hx : x ∈ closure C(h)) (hy : y ∈ closure C(h)) : 0 ≤ B x y := by
  have hpos : 0 < Q (ι h) := realIntersectionBilinForm_pos_of_isAmple k hh hh
  have h := QuadraticForm.polar_nonneg_of_mem_closure_connectedComponentIn_pos hQ hsig hpos hx hy
  rwa [polar_realIntersectionBilinForm, mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)] at h

/-- A class in the ample component pairs positively with every nonzero class in
its closure. -/
theorem realIntersectionBilinForm_pos_of_mem_connectedComponentIn_pos
    (hQ : (Q).Nondegenerate) (hsig : sigPos Q ≤ 1) (hh : h.IsAmple)
    {x y : V(X)} (hx : x ∈ C(h)) (hy : y ∈ closure C(h)) (hy₀ : y ≠ 0) :
    0 < B x y := by
  have hhpos : 0 < Q (ι h) := realIntersectionBilinForm_pos_of_isAmple k hh hh
  rw [QuadraticForm.connectedComponentIn_pos_eq_of_mem_closure hQ hsig hhpos hy₀ hy] at hx
  have hxy : 0 < polar Q y x := hx.2
  rwa [polar_comm Q y x, polar_realIntersectionBilinForm,
    mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)] at hxy

end TauCeti.AlgebraicGeometry.Chow
