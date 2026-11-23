/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ChartEquality
import TauCeti.AlgebraicGeometry.Restrict

/-!
# Polynomial charts on the projective line

Homogeneous linear forms define basic opens on the projective line. In the
standard polynomial charts they are computed by dehomogenization. A point
with a unit coordinate can be read in the opposite chart with the inverse coordinate.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.AlgebraicGeometry.projectiveLine

open HomogeneousLocalization Polynomial

universe u

variable {R : Type u} [CommRing R]

local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)

section PolynomialChart

variable (R)

local notation "P" => projectiveLine R
local notation "U[" i "]" => Proj.basicOpen 𝒜 (coord R i)
local notation "j[" i "]" => polynomialChartι R i

/-- The defining coordinate of a standard chart is nonvanishing throughout the chart. -/
@[simp]
theorem preimage_polynomialChartι_basicOpen_self (i : Fin 2) :
    j[i] ⁻¹ᵁ U[i] = ⊤ := by
  rw [← opensRange_polynomialChartι, Scheme.Hom.preimage_opensRange]

/-- The polynomial chart pulls a function represented by a homogeneous fraction back
to its dehomogenization. -/
theorem appLE_polynomialChartι_awayToSection (i : Fin 2)
    (a : Away 𝒜 (coord R i)) :
    (Scheme.ΓSpecIso (.of R[X])).hom
        (j[i].appLE U[i] ⊤ (preimage_polynomialChartι_basicOpen_self R i).ge
          (Proj.awayToSection 𝒜 (coord R i) a)) =
      awayEquivPolynomial R i a := by
  let q := Spec.map (awayEquivPolynomial R i).toRingEquiv.toCommRingCatIso.hom
  let g := awayι R i
  have hg : ⊤ ≤ g ⁻¹ᵁ U[i] := by
    rw [← image_awayι_top, Scheme.Hom.preimage_image_eq]
  have hq := (Scheme.Hom.preimage_top q).ge
  have hj := j[i].congr_appLE (polynomialChartι_def R i) U[i] ⊤
    (preimage_polynomialChartι_basicOpen_self R i).ge
    (hq.trans ((TopologicalSpace.Opens.map q.base).map (homOfLE hg)).le)
  have hΓ : q.appLE ⊤ ⊤ hq ≫ (Scheme.ΓSpecIso (.of R[X])).hom =
      (Scheme.ΓSpecIso (.of (Away 𝒜 (coord R i)))).hom ≫
        (awayEquivPolynomial R i).toRingEquiv.toCommRingCatIso.hom :=
    (congrArg (· ≫ (Scheme.ΓSpecIso (.of R[X])).hom)
      (Scheme.Hom.appLE_eq_app q (U := ⊤))).trans (Scheme.ΓSpecIso_naturality _)
  rw [hj, ← Scheme.Hom.appLE_comp_appLE q g U[i] ⊤ ⊤ hg hq, ← CommRingCat.comp_apply,
    Category.assoc, hΓ]
  have h := chartSectionsEquiv_awayToSection R i a
  rw [chartSectionsEquiv_apply, Scheme.Hom.appIso_hom', ← CommRingCat.comp_apply,
    ← CommRingCat.comp_apply, ← Category.assoc, Scheme.Hom.map_appLE'] at h
  exact h

variable {A : Type u} [CommRing A] (f : R →+* A) (i : Fin 2) (a : A)

local notation "p" => polynomialPoint R f i a

/-- A point given in a standard chart factors through that chart. -/
@[simp]
theorem preimage_polynomialPoint_basicOpen_self :
    p ⁻¹ᵁ U[i] = ⊤ := by
  rw [polynomialPoint_def, Scheme.Hom.comp_preimage, preimage_polynomialChartι_basicOpen_self,
    Scheme.Hom.preimage_top]

/-- Pullback of a function along a polynomial chart point evaluates the chart polynomial. -/
theorem appLE_polynomialPoint (b : Γ(P, U[i])) :
    (Scheme.ΓSpecIso (.of A)).hom
      ((p).appLE U[i] ⊤ (preimage_polynomialPoint_basicOpen_self R f i a).ge b) =
    eval₂ f a ((Scheme.ΓSpecIso (.of R[X])).hom
      (j[i].appLE U[i] ⊤ (preimage_polynomialChartι_basicOpen_self R i).ge b)) := by
  let q := Spec.map (CommRingCat.ofHom (eval₂RingHom f a))
  have hp : p = q ≫ j[i] := polynomialPoint_def R f i a
  have h := (p).congr_appLE hp U[i] ⊤ (preimage_polynomialPoint_basicOpen_self R f i a).ge
    ((Scheme.Hom.preimage_top q).ge.trans ((TopologicalSpace.Opens.map q.base).map
      (homOfLE (preimage_polynomialChartι_basicOpen_self R i).ge)).le)
  have hq : q.appLE ⊤ ⊤ (Scheme.Hom.preimage_top q).ge ≫
      (Scheme.ΓSpecIso (.of A)).hom =
        (Scheme.ΓSpecIso (.of R[X])).hom ≫ CommRingCat.ofHom (eval₂RingHom f a) :=
    (congrArg (· ≫ (Scheme.ΓSpecIso (.of A)).hom)
      (Scheme.Hom.appLE_eq_app q (U := ⊤))).trans (Scheme.ΓSpecIso_naturality _)
  rw [h, ← Scheme.Hom.appLE_comp_appLE q j[i] U[i] ⊤ ⊤
      (preimage_polynomialChartι_basicOpen_self R i).ge (Scheme.Hom.preimage_top q).ge,
    ← CommRingCat.comp_apply, Category.assoc, hq]
  rfl

end PolynomialChart

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

/-- A polynomial chart point with a unit coordinate can be read on the opposite
chart with the inverse unit as coordinate. -/
theorem polynomialPoint_rev {A : Type u} [CommRing A] (f : R →+* A) (i : Fin 2) (a : Aˣ) :
    polynomialPoint R f i (a : A) = polynomialPoint R f i.rev (↑a⁻¹ : A) := by
  let e := awayEquivPolynomial R i.rev
  let φ := pointCoordinates R f i (a : A)
  have hu : IsUnit (φ (coord R i.rev)) := by
    rw [pointCoordinates_coord_rev]
    exact a.isUnit
  let eval := Away.lift 𝒜 φ hu
  have he : eval.comp e.symm.toRingHom = eval₂RingHom f (↑a⁻¹ : A) := by
    apply Polynomial.ringHom_ext
    · intro r
      rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C, ← Polynomial.algebraMap_eq,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv, e.symm.commutes,
        HomogeneousLocalization.algebraMap_eq_comp, RingHom.comp_apply,
        ← HomogeneousLocalization.algebraMap_eq, Away.lift_algebraMap]
      exact pointCoordinates_algebraMap R f i _ r
    · simp [eval, e, φ]
  rw [polynomialPoint_eq_fromGlobalSections,
    Proj.fromOfGlobalSections_Spec_eq_awayLift φ (pointCoordinates_irrelevant R f i _)
      one_pos (coord_mem R i.rev) hu, polynomialPoint_def, polynomialChartι_def,
    ← Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  -- The chart isomorphism identifies the comparison with the polynomial evaluation above.
  change eval = (eval₂RingHom f (↑a⁻¹ : A)).comp e.toRingHom
  rw [← he]
  exact RingHom.ext fun x ↦ congrArg eval (e.symm_apply_apply x).symm

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
