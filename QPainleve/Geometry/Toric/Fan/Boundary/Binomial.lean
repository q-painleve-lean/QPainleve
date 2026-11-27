/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Character

import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Orders of character binomials at toric boundary points

A nontrivial character of order zero cannot cancel a nonzero constant at the generic
point of a toric boundary divisor. This gives the minimum formula for the binomial
in the boundary tropicalization of a cluster mutation, as in Gross, Hacking and Keel,
*Birational geometry of cluster algebras*, (1.4).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra Multiplicative

namespace TauCeti.Toric

universe u

variable (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
  {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- A binomial with nonzero constant coefficient and nontrivial exponent is a unit
at the generic point of any ray of its regular cone chart. -/
theorem IsRegularCone.rayChartPoint_mem_basicOpen_binomial {σ : PointedCone ℝ V}
    (hreg : IsRegularCone i σ) (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (ρ : ToricRay σ) {m : dualSemigroup hi σ} (hm : m ≠ 0) {a : A} (ha : a ≠ 0) (c : A) :
    (hreg.rayChartPoint hi hσ ρ A).val ∈ PrimeSpectrum.basicOpen
      (single 0 a + single m c) := by
  intro hf
  rw [hreg.rayChartPoint_asIdeal] at hf
  classical
  have hcoeff := (mem_rayChartIdeal_iff hi hσ ρ A _).mp hf 0 (by simp)
  exact ha (by simpa [hm, Finsupp.single_apply] using hcoeff)

namespace Fan

variable (Φ : Fan i) [Nonempty Φ.cones]

local notation "X₀" => Φ.finiteFanScheme A
local notation "K" => Scheme.functionField X₀
local notation "C" => algebraMap A K

private theorem one_add_mul_character_nonneg (hΦ : Φ.IsRegular) (ρ : Φ.Ray)
    (c : A) {m : N →+ ℤ} (hm : m ≠ 0) (hpos : 0 ≤ m ρ.primitiveGenerator) :
    1 + C c * Φ.functionFieldCharacter A (ofAdd m) ≠ 0 ∧
      (X₀).ord (1 + C c * Φ.functionFieldCharacter A (ofAdd m))
        (Φ.rayBoundaryChartPoint (R := A) hΦ ρ).val = 0 := by
  classical
  let σ := ρ.toCone
  let hσ := Φ.isToricCone σ.property
  let hreg := (isRegular_iff.1 hΦ) _ σ.property
  let r := Ray.toToricRay Φ ρ σ le_rfl
  let x := hreg.rayChartPoint Φ.lattice hσ r A
  let R := CommRingCat.of (affineChartRing A Φ.lattice σ.val)
  let X := Spec R
  let a : dualSemigroup Φ.lattice σ.val := ⟨m, by
    rw [Ray.toCone_eq_hull_primitiveGenerator ρ, ← Set.image_singleton,
      mem_dualSemigroup_hull_image]
    simpa using hpos⟩
  let f : R := 1 + algebraMap A R c * single a 1
  let s := (Scheme.ΓSpecIso R).inv f
  let j := Φ.affineChartι A σ
  have ha : a ≠ 0 := fun h ↦ hm (congrArg Subtype.val h)
  have heq : f = single 0 1 + single a c := by
    dsimp only [f]
    rw [← Algebra.smul_def, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rfl
  have hf : f ∉ x.val.asIdeal := by
    rw [heq]
    exact hreg.rayChartPoint_mem_basicOpen_binomial A Φ.lattice hσ r ha one_ne_zero c
  have hpull : j.functionFieldMap (1 + C c * Φ.functionFieldCharacter A (ofAdd m)) =
      X.germToFunctionField ⊤ s := by
    rw [map_add, map_one, map_mul, j.functionFieldMap_algebraMap A,
      Φ.functionFieldMap_affineChartι_character A σ a, Scheme.Spec.algebraMap_functionField_base]
    let : Algebra R X.functionField := instAlgebraCarrierFunctionFieldSpec R
    -- Identify the chart functions with the corresponding sections of `Spec R`.
    simp only [s, f, map_add, map_mul, map_one, ConcreteCategory.comp_apply]
    rfl
  constructor
  · intro hz
    have hj : j.functionFieldMap (1 + C c * Φ.functionFieldCharacter A (ofAdd m)) = 0 :=
      hz ▸ map_zero _
    have hx : s = 0 := (X.germToFunctionField_injective ⊤)
      (hpull.symm.trans (hj.trans (map_zero _).symm))
    exact hf ((map_eq_zero_iff _ (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.injective).mp
      hx ▸ x.val.asIdeal.zero_mem)
  · have := hσ.isNoetherianRing_affineChartRing A Φ.lattice
    rw [coe_rayBoundaryChartPoint, ← TauCeti.AlgebraicGeometry.Scheme.ord_functionFieldMap, hpull]
    have hmem : x.val ∈ X.basicOpen s := by
      rw [basicOpen_eq_of_affine]
      exact hf
    exact X.ord_eq_zero_of_mem_basicOpen ⟨x.val, trivial⟩ hmem

/-- A nontrivial character cannot cancel the constant term of a binomial at a boundary ray.
The binomial is nonzero, and its order is the minimum of zero and the character's order. -/
theorem ord_rayBoundaryChartPoint_one_add_mul_character (hΦ : Φ.IsRegular) (ρ : Φ.Ray)
    (c : Aˣ) {m : N →+ ℤ} (hm : m ≠ 0) :
    1 + C (c : A) * Φ.functionFieldCharacter A (ofAdd m) ≠ 0 ∧
      (X₀).ord (1 + C (c : A) * Φ.functionFieldCharacter A (ofAdd m))
        (Φ.rayBoundaryChartPoint (R := A) hΦ ρ).val = min 0 (m ρ.primitiveGenerator) := by
  by_cases hpos : 0 ≤ m ρ.primitiveGenerator
  · simpa only [min_eq_left hpos] using Φ.one_add_mul_character_nonneg A hΦ ρ c hm hpos
  · have hneg : m ρ.primitiveGenerator < 0 := lt_of_not_ge hpos
    obtain ⟨hne, ho⟩ := Φ.one_add_mul_character_nonneg A hΦ ρ (↑c⁻¹) (neg_ne_zero.mpr hm)
      (by simpa using hneg.le)
    let f := Φ.functionFieldCharacter A (ofAdd m)
    have hf : f ≠ 0 := ((Group.isUnit (ofAdd m)).map (Φ.functionFieldCharacter A)).ne_zero
    have hc : C (c : A) * f ≠ 0 := mul_ne_zero (c.isUnit.map C).ne_zero hf
    have hunit : (C (c : A) * f) * (C (↑c⁻¹ : A) * f⁻¹) = 1 := by
      calc
        _ = C ((c : A) * (↑c⁻¹ : A)) * (f * f⁻¹) := by
          rw [map_mul]
          ring
        _ = _ := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, mul_inv_cancel₀ hf, one_mul]
    have heq : 1 + C (c : A) * f =
        (C (c : A) * f) * (1 + C (↑c⁻¹ : A) * Φ.functionFieldCharacter A (ofAdd (-m))) := by
      rw [ofAdd_neg, map_inv]
      change 1 + C (c : A) * f = (C (c : A) * f) * (1 + C (↑c⁻¹ : A) * f⁻¹)
      rw [mul_add, mul_one, hunit, add_comm]
    change 1 + C (c : A) * f ≠ 0 ∧ (X₀).ord (1 + C (c : A) * f) _ = _
    rw [heq, Scheme.ord_mul hc hne, ho, add_zero, Φ.ord_rayBoundaryChartPoint_mul_character A,
      min_eq_right hneg.le]
    exact ⟨mul_ne_zero hc hne, rfl⟩

end Fan

end TauCeti.Toric
