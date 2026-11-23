/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Basic

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

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- A binomial with nonzero constant coefficient and nontrivial exponent is a unit
at the generic point of any ray of its regular cone chart. -/
theorem IsRegularCone.rayPoint_mem_basicOpen_binomial {σ : PointedCone ℝ V}
    (hreg : IsRegularCone i σ) (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (ρ : ToricRay σ) {m : dualSemigroup hi σ} (hm : m ≠ 0) {a : ℂ} (ha : a ≠ 0) (c : ℂ) :
    (hreg.rayPoint hi hσ ρ).val ∈ PrimeSpectrum.basicOpen
      (MonoidAlgebra.single 1 a + MonoidAlgebra.single (ofAdd m) c) := by
  intro hf
  rw [hreg.rayPoint_asIdeal] at hf
  have hcoeff := coeff_eq_zero_of_mem_rayIdeal hi hσ hreg ρ hf 0 (by simp)
  have hm' : ofAdd m ≠ (1 : Multiplicative (dualSemigroup hi σ)) := hm
  exact ha (by simpa [hm'] using hcoeff)

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
  have ha : a ≠ 0 := fun h ↦ hm (congrArg Subtype.val h)
  have heq : f = MonoidAlgebra.single 1 1 + MonoidAlgebra.single (ofAdd a) c := by
    dsimp only [f]
    rw [← Algebra.smul_def, MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rfl
  have hf : f ∉ x.val.asIdeal := by
    rw [heq]
    exact hreg.rayPoint_mem_basicOpen_binomial Φ.lattice hσ r ha one_ne_zero c
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

end TauCeti.Toric
