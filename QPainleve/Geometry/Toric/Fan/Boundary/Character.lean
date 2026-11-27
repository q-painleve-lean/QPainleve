/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.BaseChange.FunctionField
public import QPainleve.Geometry.Toric.Fan.Boundary.Ray.GenericPoint
public import Mathlib.AlgebraicGeometry.OrderOfVanishing.Basic

import QPainleve.Geometry.Toric.RegularChart
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Orders of toric characters along boundary divisors

The order of a lattice character along a ray divisor is the integral pairing
of the character with the primitive ray generator. In a regular cone chart,
this order is the exponent of the corresponding polynomial variable.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open TauCeti.AlgebraicGeometry (CodimensionOnePoint)

namespace TauCeti.Toric

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V} (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
  {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
  (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ)))
  (A : Type*) [CommRing A]

local notation "χ" => AddMonoidAlgebra.of A (dualSemigroup hi σ)

private theorem monomial_factor_ray (ρ : ToricRay σ) (m : dualSemigroup hi σ) :
    ∃ m₀ : dualSemigroup hi σ,
      (m₀ : N →+ ℤ) (primitiveGenerator hi hσ ρ) = 0 ∧
      χ (ofAdd m) =
        χ (ofAdd m₀) * χ (ofAdd (dualSemigroupCoord hi hσ hb (Sum.inl ρ))) ^
          (regularDualSemigroupEquiv hi hσ hb m).1 ρ := by
  let e := regularDualSemigroupEquiv hi hσ hb
  let m₀ := e.symm ((e m).1.erase ρ, (e m).2)
  let q := dualSemigroupCoord hi hσ hb (Sum.inl ρ)
  have hq : e q = (Finsupp.single ρ 1, 0) := by
    simp only [e, q, ← regularDualSemigroupEquiv_symm_apply_single_zero hi hσ hb ρ,
      AddEquiv.apply_symm_apply]
  have h₀ : e m₀ = ((e m).1.erase ρ, (e m).2) := e.apply_symm_apply _
  refine ⟨m₀, ?_, ?_⟩
  · rw [← (hb ρ).eq_primitiveGenerator hi hσ, ← coe_regularDualSemigroupEquiv_fst_apply hi hσ hb,
      h₀, Finsupp.erase_same, Nat.cast_zero]
  · have hm : m = m₀ + (e m).1 ρ • q := by
      apply e.injective
      rw [map_add, map_nsmul, h₀, hq]
      ext : 1
      · simp only [Prod.fst_add, Prod.smul_fst, Finsupp.smul_single, nsmul_eq_mul, mul_one,
          Nat.cast_id, Finsupp.erase_add_single]
      · simp
    rw [← map_pow, ← ofAdd_nsmul, ← map_mul, ← ofAdd_add, ← hm]

local notation "R" => CommRingCat.of (affineChartRing A hi σ)
local notation "X" => Spec R
local notation "toField" => (Iso.inv (Scheme.ΓSpecIso R) ≫ Scheme.germToFunctionField (X) ⊤)

/-- A monomial has order equal to the pairing of its exponent with the primitive ray. -/
theorem ord_rayChartPoint_single [IsDomain A] [IsNoetherianRing A]
    (hreg : IsRegularCone i σ) (ρ : ToricRay σ) (m : dualSemigroup hi σ) :
    letI := hσ.isNoetherianRing_affineChartRing A hi
    letI : Algebra R (X).functionField := instAlgebraCarrierFunctionFieldSpec R
    (X).ord (algebraMap R (X).functionField (AddMonoidAlgebra.single m 1))
        (hreg.rayChartPoint hi hσ ρ A).val =
      (m : N →+ ℤ) (primitiveGenerator hi hσ ρ) := by
  let := hσ.isNoetherianRing_affineChartRing A hi
  let : Algebra R (X).functionField := instAlgebraCarrierFunctionFieldSpec R
  have hmono : algebraMap R (X).functionField (AddMonoidAlgebra.single m 1) =
      (toField) (χ (ofAdd m)) := by
    rw [AddMonoidAlgebra.of_apply, toAdd_ofAdd, Scheme.ΓSpecIso_inv]
    rfl
  rw [hmono]
  let x := hreg.rayChartPoint hi hσ ρ A
  let p : PrimeSpectrum (affineChartRing A hi σ) := x.val
  let S := (X).presheaf.stalk x.val
  let := p.isPrime
  let : Algebra (affineChartRing A hi σ) S :=
    StructureSheaf.stalkAlgebra (affineChartRing A hi σ) p
  have : IsLocalization.AtPrime S p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (affineChartRing A hi σ) p
  have hmap (a : R) :
      algebraMap S (X).functionField (algebraMap (affineChartRing A hi σ) S a) = (toField) a :=
    (X).algebraMap_germ_eq_germToFunctionField (x := x.val) trivial ((Scheme.ΓSpecIso R).inv a)
  obtain ⟨l, b, hb⟩ := hreg.exists_basis_sum
  let q := χ (ofAdd (dualSemigroupCoord hi hσ hb (Sum.inl ρ)))
  have hmmax : IsLocalRing.maximalIdeal S =
      Ideal.span {algebraMap (affineChartRing A hi σ) S q} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal,
      hreg.rayChartPoint_asIdeal, rayChartIdeal_eq_span_rayCoordinate hi hσ ρ A hb,
      Ideal.map_span, Set.image_singleton]
    rfl
  have hq : (X).ord (toField q) x.val = 1 := by
    rw [← hmap]
    apply TauCeti.AlgebraicGeometry.Scheme.ord_algebraMap_stalk_eq_one x.property specializes_rfl
    simpa only [TopCat.Presheaf.stalkSpecializes_refl, CommRingCat.hom_id, Ideal.comap_id]
      using hmmax
  obtain ⟨m₀, h₀, hm⟩ := monomial_factor_ray hi hσ hb A ρ m
  have hu : IsUnit (algebraMap (affineChartRing A hi σ) S (χ (ofAdd m₀))) := by
    apply (IsLocalization.AtPrime.isUnit_to_map_iff S p.asIdeal _).2
    rw [Ideal.mem_primeCompl_iff, hreg.rayChartPoint_asIdeal, AddMonoidAlgebra.of_apply,
      toAdd_ofAdd, single_mem_rayChartIdeal_iff, h₀]
    simp
  have h₀ord : (X).ord ((toField) (χ (ofAdd m₀))) x.val = 0 := by
    rw [← hmap]
    exact Scheme.ord_algebraMap_eq_zero_of_isUnit hu
  have hinj : Function.Injective (toField) := by
    intro a b hab
    exact (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.injective
      ((X).germToFunctionField_injective ⊤ hab)
  have hne (m : dualSemigroup hi σ) : toField (χ (ofAdd m)) ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 (AddMonoidAlgebra.single_ne_zero.mpr one_ne_zero)
  rw [hm, map_mul, map_pow, Scheme.ord_mul (hne m₀) (pow_ne_zero _ (hne _)),
    h₀ord, Scheme.ord_pow, hq, zero_add, mul_one, coe_regularDualSemigroupEquiv_fst_apply,
    (hb ρ).eq_primitiveGenerator hi hσ]

end TauCeti.Toric

namespace TauCeti.Toric.Fan

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i) [Nonempty Φ.cones]

local notation "X" => (Φ.finiteFanScheme R)
local notation "A[" σ "]" => CommRingCat.of (affineChartRing R Φ.lattice (Subtype.val σ))

/-- A rational character has order given by its pairing with the primitive boundary ray. -/
theorem ord_rayBoundaryChartPoint_character (hΦ : Φ.IsRegular) (ρ : Φ.Ray) (m : N →+ ℤ) :
    (X).ord (Φ.functionFieldCharacter R (ofAdd m))
      (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val = m ρ.primitiveGenerator := by
  let σ := ρ.toCone
  let r := Ray.toToricRay Φ ρ σ le_rfl
  let hσ := Φ.isToricCone σ.property
  let hreg := (isRegular_iff.mp hΦ _ σ.property)
  have hnonneg (a : N →+ ℤ) (ha : 0 ≤ a ρ.primitiveGenerator) :
      a ∈ dualSemigroup Φ.lattice σ.val := by
    rw [ρ.toCone_eq_hull_primitiveGenerator, ← Set.image_singleton, mem_dualSemigroup_hull_image]
    simpa using ha
  have hregular (a : N →+ ℤ) (ha : 0 ≤ a ρ.primitiveGenerator) :
      (X).ord (Φ.functionFieldCharacter R (ofAdd a))
        (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val = a ρ.primitiveGenerator := by
    let : IsLocallyNoetherian (Spec A[σ]) :=
      isLocallyNoetherian_Spec.mpr (hσ.isNoetherianRing_affineChartRing R Φ.lattice)
    let : IsDominant (Φ.affineChartι R σ) :=
      isDominant_of_isOpenImmersion (Φ.affineChartι R σ)
    rw [coe_rayBoundaryChartPoint,
      ← TauCeti.AlgebraicGeometry.Scheme.ord_functionFieldMap (Φ.affineChartι R σ),
      functionFieldMap_affineChartι_character R Φ σ ⟨a, hnonneg a ha⟩]
    simpa only [Ray.primitiveGenerator_def] using
      ord_rayChartPoint_single Φ.lattice hσ R hreg r ⟨a, hnonneg a ha⟩
  by_cases hm : 0 ≤ m ρ.primitiveGenerator
  · exact hregular m hm
  · have hn := hregular (-m) (by simp [le_of_not_ge hm])
    rw [ofAdd_neg, map_inv, Scheme.ord_inv, AddMonoidHom.neg_apply] at hn
    exact neg_injective hn

/-- Multiplying a character by a coefficient unit preserves its order along a boundary ray. -/
theorem ord_rayBoundaryChartPoint_mul_character (hΦ : Φ.IsRegular) (ρ : Φ.Ray)
    (c : Rˣ) (m : N →+ ℤ) :
    (X).ord (algebraMap R (X).functionField (c : R) * Φ.functionFieldCharacter R (ofAdd m))
        (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val = m ρ.primitiveGenerator := by
  rw [Scheme.ord_mul (c.isUnit.map (algebraMap R (X).functionField)).ne_zero
      ((Group.isUnit (ofAdd m)).map (Φ.functionFieldCharacter R)).ne_zero,
    Scheme.ord_algebraMap_base_unit (X) c, zero_add,
    ord_rayBoundaryChartPoint_character R Φ hΦ]

end TauCeti.Toric.Fan
