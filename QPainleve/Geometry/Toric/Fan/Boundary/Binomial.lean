/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.OrderOfVanishing.Base
public import QPainleve.Geometry.Toric.Fan.Boundary.Basic
public import TauCeti.Geometry.Toric.Algebraic.Fan.Over

import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Orders of character binomials at toric boundary points

A nontrivial character of order zero cannot cancel a nonzero constant at the generic
point of a toric boundary divisor. This gives the minimum formula for the binomial
in the boundary tropicalization of a cluster mutation, as in Gross, Hacking and Keel,
*Birational geometry of cluster algebras*, (1.4).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- At an exponent of weight zero, the coefficient of every element of the ray ideal vanishes. -/
theorem coeff_eq_zero_of_mem_rayIdeal (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (hreg : IsRegularCone i σ) (ρ : ToricRay σ) {f : affineCoordinateRing hi σ}
    (hf : f ∈ rayIdeal hi hσ ρ) (m : dualSemigroup hi σ)
    (hm : (m : N →+ ℤ) (primitiveGenerator hi hσ ρ) = 0) : f.coeff (ofAdd m) = 0 := by
  obtain ⟨l, b, hb⟩ := hreg.exists_basis_sum
  let q := dualSemigroupCoord hi hσ hb (Sum.inl ρ)
  rw [rayIdeal_eq_span hi hσ hb, Ideal.mem_span_singleton] at hf
  obtain ⟨g, rfl⟩ := hf
  rw [MonoidAlgebra.of_apply]
  apply MonoidAlgebra.coeff_single_mul_of_forall_mul_ne
  intro d hd
  let u := primitiveGenerator hi hσ ρ
  have hq : (q : N →+ ℤ) u = 1 := by
    simp [q, u, ← (hb ρ).eq_primitiveGenerator hi hσ]
  have hdu : (0 : ℤ) ≤ (d.toAdd : N →+ ℤ) u := by
    have h := (mem_dualSemigroup hi _).mp d.toAdd.property
      (ρ.val.isFaceOf.le (primitiveGenerator_mem hi hσ ρ))
    exact_mod_cast (hi.realCharacter_apply _ u ▸ h)
  have h := congrArg (fun x : Multiplicative (dualSemigroup hi σ) ↦
    (x.toAdd : N →+ ℤ) u) hd
  have heq : (q : N →+ ℤ) u + (d.toAdd : N →+ ℤ) u = (m : N →+ ℤ) u := by
    simpa only [toAdd_mul, toAdd_ofAdd, AddSubmonoid.coe_add, AddMonoidHom.add_apply] using h
  have hm' : (m : N →+ ℤ) u = 0 := hm
  omega

section Complex

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

namespace Fan

variable (Φ : Fan i) [Nonempty Φ.cones]

local notation "K" => Φ.algebraicRealization.functionField
local notation "C" => algebraMap ℂ K

private theorem one_add_mul_character_nonneg (hΦ : Φ.IsRegular) (ρ : Φ.Ray)
    (c : ℂ) {m : N →+ ℤ} (hm : m ≠ 0) (hpos : 0 ≤ m ρ.primitiveGenerator) :
    1 + C c * Φ.character (ofAdd m) ≠ 0 ∧
      Φ.algebraicRealization.ord (1 + C c * Φ.character (ofAdd m))
        (Φ.rayBoundaryPoint hΦ ρ).val = 0 := by
  classical
  let σ := ρ.toCone
  let hσ := Φ.isToricCone σ.property
  let hreg := (isRegular_iff.1 hΦ) _ σ.property
  let r := Ray.toToricRay Φ ρ σ le_rfl
  let x := hreg.rayPoint Φ.lattice hσ r
  let R := CommRingCat.of (affineCoordinateRing Φ.lattice σ.val)
  let X := Φ.affineToricChart σ
  let a : dualSemigroup Φ.lattice σ.val := ⟨m, by
    rw [Ray.toCone_eq_hull_primitiveGenerator ρ, ← Set.image_singleton,
      mem_dualSemigroup_hull_image]
    simpa using hpos⟩
  let f : R := 1 + algebraMap ℂ R c * MonoidAlgebra.of ℂ _ (ofAdd a)
  let s := (Scheme.ΓSpecIso R).inv f
  let j := Φ.affineToricChartι σ
  have hcoeff : f.coeff 1 = 1 := by
    have ha : ofAdd a ≠ (1 : Multiplicative (dualSemigroup Φ.lattice σ.val)) := by
      exact fun h ↦ hm (congrArg (fun t ↦ (t.toAdd : N →+ ℤ)) h)
    simp [f, MonoidAlgebra.of_apply, R, MonoidAlgebra.coe_algebraMap, ha]
  have hf : f ∉ x.val.asIdeal := by
    rw [hreg.rayPoint_asIdeal]
    exact fun h ↦ one_ne_zero (hcoeff.symm.trans
      (coeff_eq_zero_of_mem_rayIdeal Φ.lattice hσ hreg r h 0 (by simp)))
  have hpull : j.functionFieldMap (1 + C c * Φ.character (ofAdd m)) =
      X.germToFunctionField ⊤ s := by
    rw [map_add, map_one, map_mul, j.functionFieldMap_algebraMap ℂ,
      Φ.functionFieldMap_affineToricChartι_character σ a, Scheme.Spec.algebraMap_functionField_base]
    -- Identify the chart functions with the corresponding sections of `Spec R`.
    simp only [s, f, map_add, map_mul, map_one, ConcreteCategory.comp_apply]
    rfl
  constructor
  · intro hz
    have hj : j.functionFieldMap (1 + C c * Φ.character (ofAdd m)) = 0 := hz ▸ map_zero _
    have hx : s = 0 := (X.germToFunctionField_injective ⊤)
      (hpull.symm.trans (hj.trans (map_zero _).symm))
    exact hf ((map_eq_zero_iff _ (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.injective).mp
      hx ▸ x.val.asIdeal.zero_mem)
  · have := hσ.isNoetherianRing_affineCoordinateRing Φ.lattice
    rw [coe_rayBoundaryPoint, ← TauCeti.AlgebraicGeometry.Scheme.ord_functionFieldMap, hpull]
    have hmem : x.val ∈ X.basicOpen s := by
      rw [basicOpen_eq_of_affine]
      exact hf
    exact X.ord_eq_zero_of_mem_basicOpen ⟨x.val, trivial⟩ hmem

/-- A scalar multiple of a lattice character has the same boundary order as the character itself. -/
theorem ord_rayBoundaryPoint_mul_character (hΦ : Φ.IsRegular) (ρ : Φ.Ray)
    (c : ℂˣ) (m : N →+ ℤ) :
    Φ.algebraicRealization.ord (C (c : ℂ) * Φ.character (ofAdd m))
        (Φ.rayBoundaryPoint hΦ ρ).val = m ρ.primitiveGenerator := by
  rw [Scheme.ord_mul ((map_ne_zero C).mpr c.ne_zero)
      ((Group.isUnit (ofAdd m)).map Φ.character).ne_zero,
    Scheme.ord_algebraMap_base_unit, zero_add, Φ.ord_rayBoundaryPoint_character]

/-- A nontrivial character cannot cancel the constant term of a binomial at a boundary ray.
The binomial is nonzero, and its order is the minimum of zero and the character's order. -/
theorem ord_rayBoundaryPoint_one_add_mul_character (hΦ : Φ.IsRegular) (ρ : Φ.Ray)
    (c : ℂˣ) {m : N →+ ℤ} (hm : m ≠ 0) :
    1 + C (c : ℂ) * Φ.character (ofAdd m) ≠ 0 ∧
      Φ.algebraicRealization.ord (1 + C (c : ℂ) * Φ.character (ofAdd m))
        (Φ.rayBoundaryPoint hΦ ρ).val = min 0 (m ρ.primitiveGenerator) := by
  by_cases hpos : 0 ≤ m ρ.primitiveGenerator
  · simpa only [min_eq_left hpos] using Φ.one_add_mul_character_nonneg hΦ ρ c hm hpos
  · have hneg : m ρ.primitiveGenerator < 0 := lt_of_not_ge hpos
    obtain ⟨hne, ho⟩ := Φ.one_add_mul_character_nonneg hΦ ρ (↑c⁻¹) (neg_ne_zero.mpr hm)
      (by simpa using hneg.le)
    have hc : C (c : ℂ) * Φ.character (ofAdd m) ≠ 0 :=
      mul_ne_zero ((map_ne_zero C).mpr c.ne_zero) ((Group.isUnit (ofAdd m)).map Φ.character).ne_zero
    have heq : 1 + C (c : ℂ) * Φ.character (ofAdd m) =
        (C (c : ℂ) * Φ.character (ofAdd m)) * (1 + C (↑c⁻¹ : ℂ) * Φ.character (ofAdd (-m))) := by
      rw [ofAdd_neg, map_inv, Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv_rev,
        mul_comm (Φ.character (ofAdd m)) (C (c : ℂ)), mul_add,
        mul_one, mul_inv_cancel₀ hc, add_comm]
    rw [heq, Scheme.ord_mul hc hne, ho, add_zero, Φ.ord_rayBoundaryPoint_mul_character,
      min_eq_right hneg.le]
    exact ⟨mul_ne_zero hc hne, rfl⟩

end Fan

end Complex

end TauCeti.Toric
