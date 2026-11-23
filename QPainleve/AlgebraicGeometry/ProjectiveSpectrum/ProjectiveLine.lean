/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Nonvanishing loci on the projective line

Homogeneous linear forms define basic opens on the projective line. In the
standard polynomial charts they are computed by dehomogenization.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.AlgebraicGeometry.projectiveLine

open HomogeneousLocalization Polynomial

variable {R : Type*} [CommRing R]

local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)

/-- The inverse image of a linear form's nonvanishing locus in a polynomial chart
is the basic open of its dehomogenization. -/
theorem polynomialChartι_preimage_basicOpen_of_mem {p : SymmetricAlgebra R (Fin 2 → R)}
    (hp : p ∈ 𝒜 1) (j : Fin 2) :
    polynomialChartι R j ⁻¹ᵁ Proj.basicOpen 𝒜 p =
      PrimeSpectrum.basicOpen (dehomogenize R j p) := by
  rw [polynomialChartι_def, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen 𝒜 (coord_mem R j) one_pos hp one_pos,
    SpecMap_preimage_basicOpen]
  congr 1
  simpa only [RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_ofHom,
    RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv, Away.isLocalizationElem, pow_one]
    using awayEquivPolynomial_mk R j (n := 1) (a := p) (by simpa only [one_nsmul] using hp)

/-- On the first affine chart the form `X₀ + c X₁` becomes `1 + cX`. -/
theorem dehomogenize_coord_zero_add_smul (c : R) :
    dehomogenize R 0 (coord R 0 + c • coord R 1) = 1 + C c * X := by
  have h₁ : dehomogenize R 0 (coord R 1) = X := dehomogenize_coord_rev R 0
  simp [h₁, Algebra.smul_def]

/-- On the second affine chart the form `X₀ + c X₁` becomes `X + c`. -/
theorem dehomogenize_coord_one_add_smul (c : R) :
    dehomogenize R 1 (coord R 0 + c • coord R 1) = X + C c := by
  have h₀ : dehomogenize R 1 (coord R 0) = X := dehomogenize_coord_rev R 1
  simp [h₀, Algebra.smul_def]

section Field

variable {K : Type*} [Field K]

local notation "𝒜K" => TauCeti.SymmetricAlgebra.homogeneousSubmodule K (Fin 2 → K)

private theorem dehomogenize_coord_zero_add_smul_unit (c : Kˣ) :
    dehomogenize K 0 (coord K 0 + (c : K) • coord K 1) =
      C (c : K) * (X - C (-(↑c⁻¹ : K))) := by
  rw [dehomogenize_coord_zero_add_smul, mul_sub, ← map_mul]
  simp [add_comm]

private theorem mem_basicOpen_coord_add_smul_of_notMem_chart_zero (c : Kˣ)
    {x : projectiveLine K} (hx : x ∉ Set.range (polynomialChartι K 0)) :
    x ∈ Proj.basicOpen 𝒜K (coord K 0 + (c : K) • coord K 1) := by
  have hx₁ : x ∈ Set.range (polynomialChartι K 1) := by
    apply Or.resolve_left _ hx
    rw [← Set.mem_union, range_polynomialChartι_union_range_polynomialChartι]
    trivial
  obtain ⟨y, rfl⟩ := hx₁
  have hy : (X : K[X]) ∈ y.asIdeal := by
    by_contra hy
    exact hx ((polynomialChartι_mem_range_iff K 1 y).2 hy)
  have hs := (𝒜K 1).add_mem (coord_mem K 0)
    ((𝒜K 1).smul_mem (c : K) (coord_mem K 1))
  rw [← Scheme.Hom.mem_preimage, polynomialChartι_preimage_basicOpen_of_mem hs,
    dehomogenize_coord_one_add_smul]
  exact (PrimeSpectrum.mem_basicOpen _ _).2 fun he ↦ y.isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ ((y.asIdeal.add_mem_iff_right hy).mp he) (c.isUnit.map C))

/-- The complement of the point with affine coordinate `-c⁻¹` is the
nonvanishing locus of the homogeneous form `X₀ + c X₁`. -/
theorem basicOpen_coord_add_smul_eq_compl_support (c : Kˣ) :
    Proj.basicOpen 𝒜K (coord K 0 + (c : K) • coord K 1) =
      (polynomialPoint K (RingHom.id K) 0 (-(↑c⁻¹ : K))).ker.support.compl := by
  let a : K := -(↑c⁻¹ : K)
  let p := polynomialPoint K (RingHom.id K) 0 a
  let f := Spec.map (CommRingCat.ofHom (evalRingHom a))
  let s := coord K 0 + (c : K) • coord K 1
  have hs : s ∈ 𝒜K 1 :=
    (𝒜K 1).add_mem (coord_mem K 0) ((𝒜K 1).smul_mem _ (coord_mem K 1))
  have hp : p = f ≫ polynomialChartι K 0 := polynomialPoint_def K (RingHom.id K) 0 a
  have : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id
    (projectiveLine K ↘ Spec (.of K)) p (by simp [p, polynomialPoint_over])
  have hpr : (p.ker.support : Set (projectiveLine K)) = Set.range p :=
    p.support_ker.trans p.isClosedEmbedding.isClosed_range.closure_eq
  have hfr : Set.range f = PrimeSpectrum.zeroLocus {X - C a} := by
    -- The affine evaluation map on spectra is prime ideal contraction.
    change Set.range (PrimeSpectrum.comap (evalRingHom a)) = _
    rw [range_comap_of_surjective _ (evalRingHom a) (fun k ↦ ⟨C k, eval_C⟩),
      ker_evalRingHom, PrimeSpectrum.zeroLocus_span]
  have hpRange : Set.range p = polynomialChartι K 0 '' Set.range f := by
    rw [hp, ← Set.range_comp]
    exact congrArg Set.range (funext (Scheme.Hom.comp_apply _ _))
  ext x
  -- Express membership in the open complement by nonmembership in the support.
  change x ∈ Proj.basicOpen 𝒜K s ↔ x ∉ (p.ker.support : Set (projectiveLine K))
  rw [hpr]
  by_cases hx : x ∈ Set.range (polynomialChartι K 0)
  · obtain ⟨y, rfl⟩ := hx
    have hm : polynomialChartι K 0 y ∈ Set.range p ↔ y ∈ Set.range f := by
      rw [hpRange, Set.mem_image]
      exact ⟨fun ⟨z, hz, he⟩ ↦ (polynomialChartι K 0).isOpenEmbedding.injective he ▸ hz,
        fun hy ↦ ⟨y, hy, rfl⟩⟩
    rw [hm, hfr, ← Scheme.Hom.mem_preimage, polynomialChartι_preimage_basicOpen_of_mem hs,
      dehomogenize_coord_zero_add_smul_unit, PrimeSpectrum.basicOpen_mul]
    have hu : C (c : K) ∉ y.asIdeal := fun h ↦
      y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (c.isUnit.map C))
    -- Read the intersection in the prime spectrum of the polynomial chart.
    change ((y : PrimeSpectrum K[X]) ∈ PrimeSpectrum.basicOpen (C (c : K)) ∧
      (y : PrimeSpectrum K[X]) ∈ PrimeSpectrum.basicOpen (X - C a)) ↔ _
    refine (and_iff_right ((PrimeSpectrum.mem_basicOpen _ _).mpr hu)).trans ?_
    exact Set.ext_iff.mp (PrimeSpectrum.basicOpen_eq_zeroLocus_compl (X - C a)) y
  · have hp' : x ∉ Set.range p := fun hx' ↦ by
      rw [hpRange] at hx'
      exact hx (Set.image_subset_range _ _ hx')
    exact iff_of_true (mem_basicOpen_coord_add_smul_of_notMem_chart_zero c hx) hp'

end Field

end TauCeti.AlgebraicGeometry.projectiveLine
