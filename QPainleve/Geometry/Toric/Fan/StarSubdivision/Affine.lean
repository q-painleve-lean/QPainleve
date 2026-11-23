/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.AffineCharts
public import TauCeti.Geometry.Toric.Algebraic.Fan.Scheme
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.TwoDimensional
public import TauCeti.Geometry.Toric.Analytic.Cone.Orbit.Basic

import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.Blowup.UniversalProperty
import TauCeti.Geometry.Toric.Algebraic.FaceLocalization
import TauCeti.Algebra.MonoidAlgebra.Basic
import TauCeti.Data.Fin.Rev

/-!
# Blowup charts for star subdivisions of regular surface fans

For a full-dimensional regular cone, the two cones of the star subdivision give
the affine charts of the blowup of the distinguished point. In the chart indexed
by a boundary coordinate, the two characters are that coordinate and the ratio
of the other coordinate to it.

The chart calculation follows Cox, Little, and Schenck, *Toric Varieties*,
Proposition 3.3.15. It uses Tau Ceti's star subdivisions and universal property
of affine blowup algebras.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (hi : IsIntegralLattice i) (b : Module.Basis (Fin 2) ℤ N)

private def basisCone (i : N →+ V) : PointedCone ℝ V :=
  PointedCone.hull ℝ (i '' Set.range b)

private def blowupCone (i : N →+ V) (j : Fin 2) : PointedCone ℝ V :=
  PointedCone.hull ℝ (i '' {b 0 + b 1, b j.rev})

private theorem mem_dualSemigroup_basisCone_iff (m : N →+ ℤ) :
    m ∈ dualSemigroup hi (basisCone b i) ↔ ∀ j, 0 ≤ m (b j) := by
  rw [basisCone, mem_dualSemigroup_hull_image, Set.forall_mem_range]

private theorem mem_dualSemigroup_blowupCone_iff (j : Fin 2) (m : N →+ ℤ) :
    m ∈ dualSemigroup hi (blowupCone b i j) ↔ 0 ≤ m (b 0 + b 1) ∧ 0 ≤ m (b j.rev) := by
  rw [blowupCone, mem_dualSemigroup_hull_image]
  simp

private theorem blowupCone_le (i : N →+ V) (j : Fin 2) : blowupCone b i j ≤ basisCone b i := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · rw [map_add]
    exact add_mem (PointedCone.subset_hull ⟨_, ⟨0, rfl⟩, rfl⟩)
      (PointedCone.subset_hull ⟨_, ⟨1, rfl⟩, rfl⟩)
  · exact PointedCone.subset_hull ⟨_, ⟨_, rfl⟩, rfl⟩

private def basisChar (j : Fin 2) : dualSemigroup hi (basisCone b i) :=
  ⟨(b.coord j).toAddMonoidHom, (mem_dualSemigroup_basisCone_iff hi b _).2
    (fun k ↦ by simp [Module.Basis.coord_apply, Finsupp.single_apply]; split <;> norm_num)⟩

private theorem basisChar_apply (j k : Fin 2) :
    (basisChar hi b j : N →+ ℤ) (b k) = if k = j then 1 else 0 := by
  simp [basisChar, Module.Basis.coord_apply, Finsupp.single_apply]

private def blowupInclusion (j : Fin 2) :
    dualSemigroup hi (basisCone b i) →+ dualSemigroup hi (blowupCone b i j) :=
  AddSubmonoid.inclusion (dualSemigroup_anti hi (blowupCone_le b i j))

private def blowupRatio (j : Fin 2) : dualSemigroup hi (blowupCone b i j) :=
  ⟨(basisChar hi b j.rev : N →+ ℤ) - basisChar hi b j,
    (mem_dualSemigroup_blowupCone_iff hi b j _).2 (by
      fin_cases j <;> simp [basisChar_apply, map_add])⟩

private theorem blowupInclusion_add_blowupRatio (j : Fin 2) :
    blowupInclusion hi b j (basisChar hi b j) + blowupRatio hi b j =
      blowupInclusion hi b j (basisChar hi b j.rev) := by
  apply Subtype.ext
  exact add_sub_cancel _ _

private theorem exists_nsmul_basisChar (m : dualSemigroup hi (basisCone b i)) :
    ∃ p q : ℕ, p • basisChar hi b 0 + q • basisChar hi b 1 = m := by
  have h := (mem_dualSemigroup_basisCone_iff hi b _).mp m.property
  refine ⟨(m.val (b 0)).toNat, (m.val (b 1)).toNat, ?_⟩
  apply Subtype.ext
  apply AddMonoidHom.toIntLinearMap_injective
  apply b.ext
  intro k
  fin_cases k <;>
    simp [basisChar_apply, Int.toNat_of_nonneg (h 0), Int.toNat_of_nonneg (h 1)]

private theorem exists_nsmul_blowupRatio (j : Fin 2) (m : dualSemigroup hi (blowupCone b i j)) :
    ∃ p q : ℕ,
      p • blowupInclusion hi b j (basisChar hi b j) + q • blowupRatio hi b j = m := by
  have h := (mem_dualSemigroup_blowupCone_iff hi b j _).mp m.property
  refine ⟨(m.val (b 0 + b 1)).toNat, (m.val (b j.rev)).toNat, ?_⟩
  obtain ⟨h₀, h₁⟩ := h
  apply Subtype.ext
  apply AddMonoidHom.toIntLinearMap_injective
  apply b.ext
  intro k
  fin_cases j <;> fin_cases k <;>
    simp [blowupInclusion, AddSubmonoid.inclusion, blowupRatio, basisChar_apply, map_add] at * <;>
    omega

local notation "R" => affineCoordinateRing hi (basisCone b i)
local notation "B" j => affineCoordinateRing hi (blowupCone b i j)

private def basisMonomial (j : Fin 2) : R :=
  MonoidAlgebra.of ℂ _ (ofAdd (basisChar hi b j))

private def chartHom (j : Fin 2) : R →ₐ[ℂ] B j :=
  MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blowupInclusion hi b j).toMultiplicative

private theorem chartHom_injective (j : Fin 2) : Function.Injective (chartHom hi b j) := by
  apply MonoidAlgebra.mapDomain_injective
  exact ofAdd.injective.comp
    ((AddSubmonoid.inclusion_injective (dualSemigroup_anti hi (blowupCone_le b i j))).comp
      toAdd.injective)

private def ratioMonomial (j : Fin 2) : B j :=
  MonoidAlgebra.of ℂ _ (ofAdd (blowupRatio hi b j))

private theorem chartHom_basisMonomial (j k : Fin 2) :
    chartHom hi b j (basisMonomial hi b k) =
      MonoidAlgebra.of ℂ _ (ofAdd (blowupInclusion hi b j (basisChar hi b k))) := by
  simp [chartHom, basisMonomial, MonoidAlgebra.of_apply]

private theorem chartHom_basisMonomial_mul_ratioMonomial (j : Fin 2) :
    chartHom hi b j (basisMonomial hi b j) * ratioMonomial hi b j =
      chartHom hi b j (basisMonomial hi b j.rev) := by
  simp only [chartHom_basisMonomial, ratioMonomial, ← map_mul, ← ofAdd_add,
    blowupInclusion_add_blowupRatio]

private theorem chartHom_basisMonomial_isRegular (j : Fin 2) :
    IsRegular (chartHom hi b j (basisMonomial hi b j)) := by
  rw [chartHom_basisMonomial, MonoidAlgebra.of_apply, isRegular_iff_mem_nonZeroDivisors]
  exact TauCeti.MonoidAlgebra.single_mem_nonZeroDivisors_iff.mpr (one_mem _)

private def pointIdeal : Ideal R := RingHom.ker
  (distinguishedPoint hi (⊤ : (basisCone b i).Face)).toRingHom

private theorem basisMonomial_mem_pointIdeal (j : Fin 2) :
    basisMonomial hi b j ∈ pointIdeal hi b := by
  rw [pointIdeal, RingHom.mem_ker, basisMonomial, MonoidAlgebra.of_apply]
  -- Apply the distinguished point as an algebra morphism to evaluate the monomial.
  change distinguishedPoint hi (⊤ : (basisCone b i).Face) _ = 0
  rw [distinguishedPoint_apply_single]
  refine ite_eq_right (fun h ↦ ?_)
  have hx : i (b j) ∈ (⊤ : (basisCone b i).Face) :=
    PointedCone.subset_hull ⟨_, ⟨j, rfl⟩, rfl⟩
  simpa [hi.realCharacter_apply, basisChar_apply] using h _ hx

private theorem pointIdeal_eq_span :
    pointIdeal hi b = Ideal.span (Set.range (basisMonomial hi b)) := by
  let J := Ideal.span (Set.range (basisMonomial hi b))
  let d := distinguishedPoint hi (⊤ : (basisCone b i).Face)
  let q := Ideal.Quotient.mkₐ ℂ J
  refine le_antisymm ?_ (Ideal.span_le.mpr (Set.range_subset_iff.mpr
    (basisMonomial_mem_pointIdeal hi b)))
  have hq : q = (Algebra.ofId ℂ _).comp d := by
    apply MonoidAlgebra.algHom_ext
    · intro m
      obtain ⟨p, r, h⟩ := exists_nsmul_basisChar hi b m.toAdd
      have he : m = (ofAdd (basisChar hi b 0)) ^ p * (ofAdd (basisChar hi b 1)) ^ r := by
        apply toAdd.injective
        simpa only [toAdd_mul, toAdd_pow, toAdd_ofAdd] using h.symm
      rw [← MonoidAlgebra.of_apply, he, map_mul, map_pow, map_pow]
      have hk (j : Fin 2) : q (basisMonomial hi b j) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
      have hd (j : Fin 2) : d (basisMonomial hi b j) = 0 :=
        basisMonomial_mem_pointIdeal hi b j
      have hcoord (j : Fin 2) :
          q (basisMonomial hi b j) = ((Algebra.ofId ℂ _).comp d) (basisMonomial hi b j) := by
        simp [hk, hd]
      simpa only [basisMonomial, map_mul, map_pow] using
        congrArg₂ (· * ·) (congrArg (· ^ p) (hcoord 0)) (congrArg (· ^ r) (hcoord 1))
    · ext
  intro x hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hdx : d x = 0 := hx
  have hxq : q x = 0 := by rw [hq, AlgHom.comp_apply, hdx, map_zero]
  exact hxq

private theorem map_pointIdeal_chartHom (j : Fin 2) :
    (pointIdeal hi b).map (chartHom hi b j).toRingHom =
      Ideal.span {chartHom hi b j (basisMonomial hi b j)} := by
  rw [pointIdeal_eq_span, Ideal.map_span]
  refine le_antisymm (Ideal.span_le.mpr ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  · rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    rcases Fin.fin_two_eq_or_eq_rev j k with rfl | rfl
    · exact Ideal.mem_span_singleton_self _
    · exact Ideal.mem_span_singleton'.mpr
        ⟨ratioMonomial hi b j, by
          simpa [mul_comm] using chartHom_basisMonomial_mul_ratioMonomial hi b j⟩
  · exact Ideal.subset_span ⟨_, ⟨j, rfl⟩, rfl⟩

private abbrev chartAlgebra (j : Fin 2) : Algebra R (B j) :=
  (chartHom hi b j).toRingHom.toAlgebra

private def affineChartLift (j : Fin 2) :
    letI := chartAlgebra hi b j
    (pointIdeal hi b).affineBlowup (basisMonomial hi b j)
      (Localization.Away (basisMonomial hi b j)) →ₐ[R] B j :=
  letI := chartAlgebra hi b j
  (pointIdeal hi b).affineBlowupLift _ _ (map_pointIdeal_chartHom hi b j).le
    (chartHom_basisMonomial_isRegular hi b j).left

open TauCeti.Localization in
private theorem affineChartLift_divBy (j : Fin 2) :
    affineChartLift hi b j ⟨divBy (basisMonomial hi b j.rev) (basisMonomial hi b j),
        Ideal.divBy_mem_affineBlowup (basisMonomial_mem_pointIdeal hi b j.rev)⟩ =
      ratioMonomial hi b j := by
  let := chartAlgebra hi b j
  apply (chartHom_basisMonomial_isRegular hi b j).left
  exact (Ideal.algebraMap_mul_algHom_divBy (affineChartLift hi b j)
    (basisMonomial_mem_pointIdeal hi b j.rev)).trans
    (chartHom_basisMonomial_mul_ratioMonomial hi b j).symm

open TauCeti.Localization in
private theorem bijective_affineBlowupLift (j : Fin 2) :
    letI := chartAlgebra hi b j
    Function.Bijective (affineChartLift hi b j) := by
  let := chartAlgebra hi b j
  let a := basisMonomial hi b j
  let J := pointIdeal hi b
  let A := J.affineBlowup a (Localization.Away a)
  let e := affineChartLift hi b j
  refine ⟨(injective_iff_map_eq_zero e).mpr fun z hz ↦ ?_, ?_⟩
  · obtain ⟨n, y, _, heq⟩ :=
      (Ideal.mem_affineBlowup_iff (basisMonomial_mem_pointIdeal hi b j)).mp z.property
    have hmul : algebraMap R A a ^ n * z = algebraMap R A y := Subtype.ext heq
    have hy : algebraMap R (B j) y = 0 := by
      rw [← e.commutes, ← hmul, map_mul, hz, mul_zero]
    have hy₀ : y = 0 := (chartHom_injective hi b j)
      (hy.trans ((algebraMap R (B j)).map_zero).symm)
    have ha := Ideal.isRegular_algebraMap_affineBlowup (I := J) (a := a) (S := Localization.Away a)
    apply ha.left.pow n
    simpa only [mul_zero, hy₀, map_zero] using hmul
  · have hr := affineChartLift_divBy hi b j
    intro z
    induction z using MonoidAlgebra.induction_on with
    | of m =>
      obtain ⟨p, q, hm⟩ := exists_nsmul_blowupRatio hi b j m.toAdd
      have he : m = (ofAdd (blowupInclusion hi b j (basisChar hi b j))) ^ p *
          (ofAdd (blowupRatio hi b j)) ^ q := by
        apply toAdd.injective
        simpa only [toAdd_mul, toAdd_pow, toAdd_ofAdd] using hm.symm
      rw [he, map_mul, map_pow, map_pow, ← chartHom_basisMonomial]
      -- The second factor is the monomial of the difference character.
      change ∃ z, e z = algebraMap R (B j) a ^ p * ratioMonomial hi b j ^ q
      refine ⟨(algebraMap R A a) ^ p *
        (⟨divBy (basisMonomial hi b j.rev) a,
          Ideal.divBy_mem_affineBlowup (basisMonomial_mem_pointIdeal hi b j.rev)⟩ : A) ^ q, ?_⟩
      rw [map_mul, map_pow, map_pow, e.commutes, hr]
    | add x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, e.map_add _ _⟩
    | smul c x hx =>
      obtain ⟨x, rfl⟩ := hx
      refine ⟨algebraMap R A (algebraMap ℂ R c) * x, ?_⟩
      rw [map_mul, e.commutes]
      -- The algebra structure on the chart comes from the complex algebra map.
      change chartHom hi b j (algebraMap ℂ R c) * e x = c • e x
      rw [AlgHom.commutes, Algebra.smul_def]

private def affineBlowupChartEquiv (j : Fin 2) :
    (pointIdeal hi b).affineBlowup (basisMonomial hi b j)
      (Localization.Away (basisMonomial hi b j)) ≃+* B j :=
  letI := chartAlgebra hi b j
  (AlgEquiv.ofBijective _ (bijective_affineBlowupLift hi b j)).toRingEquiv

private theorem affineBlowupChartEquiv_algebraMap (j : Fin 2) (x : R) :
    affineBlowupChartEquiv hi b j (algebraMap R _ x) = chartHom hi b j x := by
  let := chartAlgebra hi b j
  exact (affineChartLift hi b j).commutes x

private theorem mapsTo_blowupCone (j : Fin 2) :
    Set.MapsTo (LinearMap.id : V →ₗ[ℝ] V) (blowupCone b i j : Set V) (basisCone b i : Set V) := by
  intro x hx
  rw [LinearMap.id_apply]
  exact SetLike.mem_coe.mpr (blowupCone_le b i j (SetLike.mem_coe.mp hx))

private theorem affineCoordinateRingMap_blowupCone (j : Fin 2) :
    affineCoordinateRingMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
      (mapsTo_blowupCone b (i := i) j) = chartHom hi b j := by
  apply MonoidAlgebra.algHom_ext
  · intro m
    let m₀ := m.toAdd
    have he :
        dualSemigroupMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
          (mapsTo_blowupCone b (i := i) j) m₀ = blowupInclusion hi b j m₀ :=
      Subtype.ext (coe_dualSemigroupMap_id hi _ _)
    calc
      _ = MonoidAlgebra.single
          (ofAdd (dualSemigroupMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
            (mapsTo_blowupCone b (i := i) j) m₀)) 1 :=
        affineCoordinateRingMap_single hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
          (mapsTo_blowupCone b (i := i) j) m₀ 1
      _ = _ := by simp [he, chartHom, m₀]
  · ext

private abbrev allRays {σ : PointedCone ℝ V} (hσ : IsRegularCone i σ) :=
  ToricRay.faceFinset (PointedCone.IsFaceOf.refl σ) hσ.fg

private theorem starSubdivisionCone_eq_blowupCone {σ : PointedCone ℝ V}
    (hσ : IsRegularCone i σ) (e : Fin 2 ≃ ToricRay σ)
    (hb : ∀ j, b j = primitiveGenerator hi hσ.toIsToricCone (e j)) (j : Fin 2) :
    starSubdivisionCone hi (allRays hσ) hσ.toIsToricCone {none, some (e j.rev)} =
      blowupCone b i j := by
  rw [hσ.starSubdivisionCone_pair_eq_hull hi b e hb, blowupCone,
    Set.image_insert_eq, Set.image_singleton]

@[reassoc]
private theorem affineBlowupChartEquiv_SpecMap (j : Fin 2) :
    Spec.map (affineBlowupChartEquiv hi b j).toCommRingCatIso.hom ≫
      affineBlowupι (Localization.Away (basisMonomial hi b j)) (basisMonomial_mem_pointIdeal hi b j)
      ≫ Proj.toSpecZero (reesAlgebra.grade (pointIdeal hi b))
      ≫ Spec.map (reesAlgebra.gradeZeroEquiv (pointIdeal hi b)).toCommRingCatIso.hom =
    affineToricSchemeMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
      (mapsTo_blowupCone b (i := i) j) := by
  rw [affineBlowupι_toSpecZero, affineToricSchemeMap_def,
    affineCoordinateRingMap_blowupCone, ← Spec.map_comp]
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact affineBlowupChartEquiv_algebraMap hi b j x

private theorem some_notMem_starSubdivisionChart {σ : PointedCone ℝ V}
    (e : Fin 2 ≃ ToricRay σ) (j : Fin 2) :
    some (e j) ∉ ({none, some (e j.rev)} : Set (Option (ToricRay σ))) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, reduceCtorEq, Option.some.injEq,
    e.injective.eq_iff, false_or]
  fin_cases j <;> decide

private def starSubdivisionChart {σ : PointedCone ℝ V} (hσ : IsRegularCone i σ)
    (e : Fin 2 ≃ ToricRay σ) (j : Fin 2) :
    (Fan.starSubdivision hi (allRays hσ) hσ).cones :=
  ⟨starSubdivisionCone hi (allRays hσ) hσ.toIsToricCone {none, some (e j.rev)},
    hσ.starSubdivisionCone_pair_mem hi e j.rev⟩

private theorem exists_le_starSubdivisionChart {σ : PointedCone ℝ V}
    (hσ : IsRegularCone i σ) (e : Fin 2 ≃ ToricRay σ)
    (τ : (Fan.starSubdivision hi (allRays hσ) hσ).cones) :
    ∃ j, τ ≤ starSubdivisionChart hi hσ e j := by
  obtain ⟨j, hj⟩ := hσ.exists_le_starSubdivisionCone_pair hi e τ.property
  refine ⟨j.rev, ?_⟩
  simpa only [← Subtype.coe_le_coe, starSubdivisionChart, allRays, Fin.rev_rev] using hj

private theorem starSubdivisionChart_inf_eq {σ : PointedCone ℝ V}
    (hσ : IsRegularCone i σ) (e : Fin 2 ≃ ToricRay σ)
    (hb : ∀ j, b j = primitiveGenerator hi hσ.toIsToricCone (e j)) (j : Fin 2) :
    (starSubdivisionChart hi hσ e j).val ⊓ (starSubdivisionChart hi hσ e j.rev).val =
      PointedCone.hull ℝ {i (b 0 + b 1)} := by
  classical
  let := Fintype.ofEquiv _ e
  have hsum := hσ.sum_primitiveGenerator_allRays hi b e hb
  have hS (k : Fin 2) : ∃ ρ ∈ allRays hσ,
      some ρ ∉ ({none, some (e k.rev)} : Set (Option (ToricRay σ))) :=
    ⟨e k, (ToricRay.mem_faceFinset _ _).2 (e k).val.isFaceOf.le,
      some_notMem_starSubdivisionChart e k⟩
  have hj : e j.rev ≠ e j := e.injective.ne (by fin_cases j <;> decide)
  have hinter : ({none, some (e j.rev)} : Set (Option (ToricRay σ))) ∩
      {none, some (e j.rev.rev)} = {none} := by
    ext x
    cases x with
    | none => simp
    | some x => simp only [Fin.rev_rev, Set.mem_inter_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, reduceCtorEq, Option.some.injEq, false_or]; grind
  -- Unpack the two chart cones before applying the intersection formula.
  change starSubdivisionCone hi (allRays hσ) hσ.toIsToricCone {none, some (e j.rev)} ⊓
      starSubdivisionCone hi (allRays hσ) hσ.toIsToricCone {none, some (e j.rev.rev)} = _
  rw [starSubdivisionCone_inf hi (allRays hσ) hσ.toIsToricCone
    (hσ.linearIndependent_primitiveGenerator hi) (hS j) (hS j.rev), hinter]
  simp only [starSubdivisionCone_def, Set.image_singleton, starSubdivisionGenerator_none, hsum]

private theorem blowupRatio_eval_sum (j : Fin 2) :
    hi.realCharacter (blowupRatio hi b j : N →+ ℤ) (i (b 0 + b 1)) = 0 := by
  rw [hi.realCharacter_apply]
  fin_cases j <;> simp [blowupRatio, basisChar_apply, map_add]

private theorem blowupRatio_eval_other (j : Fin 2) :
    hi.realCharacter (blowupRatio hi b j : N →+ ℤ) (i (b j.rev)) = 1 := by
  rw [hi.realCharacter_apply]
  fin_cases j <;> simp [blowupRatio, basisChar_apply]

private theorem blowupCone_inf_ker_ratio (j : Fin 2)
    (hface : (PointedCone.hull ℝ {i (b 0 + b 1)}).IsFaceOf (blowupCone b i j)) :
    blowupCone b i j ⊓ PointedCone.ofSubmodule
        (LinearMap.ker (hi.realCharacter (blowupRatio hi b j))) =
      PointedCone.hull ℝ {i (b 0 + b 1)} := by
  have hsubset : PointedCone.hull ℝ {i (b 0 + b 1)} ≤
      PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter (blowupRatio hi b j))) := by
    refine Submodule.span_le.2 ?_
    rintro _ rfl
    exact LinearMap.mem_ker.mpr (blowupRatio_eval_sum hi b j)
  refine PointedCone.inf_ker_eq_of_eq_hull (s := {i (b 0 + b 1), i (b j.rev)})
    (by simp [blowupCone, Set.image_insert_eq]) hface ?_ ?_
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [blowupRatio_eval_sum]
    · rw [blowupRatio_eval_other]
      exact zero_le_one
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact iff_of_true (blowupRatio_eval_sum hi b j) (PointedCone.subset_hull rfl)
    · have hne : hi.realCharacter (blowupRatio hi b j : N →+ ℤ) (i (b j.rev)) ≠ 0 := by
        rw [blowupRatio_eval_other]
        norm_num
      exact iff_of_false hne fun h ↦ hne (LinearMap.mem_ker.mp (hsubset h))

private def reesChartMap (j : Fin 2) :
    affineToricScheme hi (blowupCone b i j) ⟶ Proj (reesAlgebra.grade (pointIdeal hi b)) :=
  Spec.map (affineBlowupChartEquiv hi b j).toCommRingCatIso.hom ≫
    affineBlowupι (Localization.Away (basisMonomial hi b j)) (basisMonomial_mem_pointIdeal hi b j)

private instance (j : Fin 2) : IsOpenImmersion (reesChartMap hi b j) := by
  unfold reesChartMap
  infer_instance

private theorem reesChartMap_preimage_opensRange (j : Fin 2) :
    reesChartMap hi b j ⁻¹ᵁ (reesChartMap hi b j.rev).opensRange =
      (PrimeSpectrum.basicOpen (ratioMonomial hi b j) :
        (affineToricScheme hi (blowupCone b i j)).Opens) := by
  simp only [reesChartMap]
  rw [Scheme.Hom.opensRange_comp_of_isIso,
    opensRange_affineBlowupι, Scheme.Hom.comp_preimage, affineBlowupι_preimage_basicOpen,
    SpecMap_preimage_basicOpen]
  congr 1
  exact affineChartLift_divBy hi b j

private def starChartIso {σ : PointedCone ℝ V} (hσ : IsRegularCone i σ)
    (e : Fin 2 ≃ ToricRay σ)
    (hb : ∀ j, b j = primitiveGenerator hi hσ.toIsToricCone (e j)) (j : Fin 2) :
    (Fan.starSubdivision hi (allRays hσ) hσ).affineToricChart (starSubdivisionChart hi hσ e j) ≅
      affineToricScheme hi (blowupCone b i j) :=
  eqToIso (congrArg (affineToricScheme hi) (starSubdivisionCone_eq_blowupCone hi b hσ e hb j))

private theorem faceAffineToricSchemeMap_comp_eqToIso {κ σ σ' : PointedCone ℝ V}
    (h : σ = σ') (hκ : κ.IsFaceOf σ) :
    faceAffineToricSchemeMap hi hκ ≫ (eqToIso (congrArg (affineToricScheme hi) h)).hom =
      faceAffineToricSchemeMap hi (h ▸ hκ) := by
  subst σ'
  simp

private theorem mem_range_starSubdivisionChart_of_mem_basicOpen {σ : PointedCone ℝ V}
    (hσ : IsRegularCone i σ) (e : Fin 2 ≃ ToricRay σ)
    (hb : ∀ j, b j = primitiveGenerator hi hσ.toIsToricCone (e j)) (j : Fin 2)
    (x : (Fan.starSubdivision hi (allRays hσ) hσ).affineToricChart
      (starSubdivisionChart hi hσ e j))
    (hx : (starChartIso hi b hσ e hb j).hom x ∈ PrimeSpectrum.basicOpen
      (ratioMonomial hi b j)) :
    (Fan.starSubdivision hi (allRays hσ) hσ).affineToricChartι (starSubdivisionChart hi hσ e j) x ∈
      Set.range ((Fan.starSubdivision hi (allRays hσ) hσ).affineToricChartι
        (starSubdivisionChart hi hσ e j.rev)) := by
  let F := Fan.starSubdivision hi (allRays hσ) hσ
  let τ := starSubdivisionChart hi hσ e
  let κ := τ j ⊓ τ j.rev
  let hface := F.inf_isFaceOf_left (τ j).property (τ j.rev).property
  have h₁ : (τ j).val = blowupCone b i j := starSubdivisionCone_eq_blowupCone hi b hσ e hb j
  have h₂ : κ.val = PointedCone.hull ℝ {i (b 0 + b 1)} :=
    starSubdivisionChart_inf_eq hi b hσ e hb j
  have hf' : κ.val.IsFaceOf (blowupCone b i j) := h₁ ▸ hface
  have hfg : (blowupCone b i j).FG := h₁ ▸ (F.isToricCone (τ j).property).fg
  have he := blowupCone_inf_ker_ratio hi b j (h₂ ▸ hf')
  have hRange {κ' : PointedCone ℝ V} (hκ' : κ'.IsFaceOf (blowupCone b i j))
      (hκ : blowupCone b i j ⊓ PointedCone.ofSubmodule
        (LinearMap.ker (hi.realCharacter (blowupRatio hi b j))) = κ') :
      Set.range (faceAffineToricSchemeMap hi hκ') =
        (PrimeSpectrum.basicOpen (ratioMonomial hi b j) : Set (PrimeSpectrum (B j))) := by
    subst κ'
    exact range_faceAffineToricSchemeMap hi hfg (blowupRatio hi b j)
  have hr := hRange hf' (he.trans h₂.symm)
  have hmap : faceAffineToricSchemeMap hi hface ≫ (starChartIso hi b hσ e hb j).hom =
      faceAffineToricSchemeMap hi hf' :=
    faceAffineToricSchemeMap_comp_eqToIso hi h₁ hface
  have hm : (starChartIso hi b hσ e hb j).hom x ∈
      Set.range (faceAffineToricSchemeMap hi hf') := by
    rw [hr]
    exact SetLike.mem_coe.mpr hx
  obtain ⟨y, hy⟩ := hm
  have hyx : faceAffineToricSchemeMap hi hface y = x :=
    (starChartIso hi b hσ e hb j).hom.isOpenEmbedding.injective (by
      rwa [← Scheme.Hom.comp_apply, hmap])
  have hcomp := F.affineToricOverlap_comp_affineToricChartι (τ j) (τ j.rev)
  refine ⟨F.affineToricOverlapRight (τ j) (τ j.rev) y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hcomp, Scheme.Hom.comp_apply, F.affineToricOverlapLeft_def, hyx]

private theorem eqToIso_hom_comp_affineToricSchemeMap {κ κ' σ : PointedCone ℝ V}
    (h : κ = κ') (hκ : κ' ≤ σ) :
    (eqToIso (congrArg (affineToricScheme hi) h)).hom ≫
        affineToricSchemeMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
          ((Set.mapsTo_id (σ : Set V)).mono_left (SetLike.coe_subset_coe.mpr hκ)) =
      affineToricSchemeMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
        ((Set.mapsTo_id (σ : Set V)).mono_left (SetLike.coe_subset_coe.mpr (h.symm ▸ hκ))) := by
  subst κ'
  simp

/-- The two full-dimensional charts of the star subdivision of a regular rank-two cone
are the standard affine charts of the Rees blowup of its distinguished point.
The chart isomorphisms respect the projections to the original affine toric scheme. -/
theorem exists_affineBlowupCharts_starSubdivision {σ : PointedCone ℝ V}
    (hσ : IsRegularCone i σ) (hN : Module.finrank ℤ N = 2)
    (hc : Nat.card (ToricRay σ) = 2) :
    let Φ := Fan.starSubdivision hi
      (ToricRay.faceFinset (PointedCone.IsFaceOf.refl σ) hσ.fg) hσ
    let J := RingHom.ker (distinguishedPoint hi (⊤ : σ.Face)).toRingHom
    ∃ (a : Fin 2 → affineCoordinateRing hi σ) (τ : Fin 2 → Φ.cones)
      (ha : ∀ j, a j ∈ J) (hle : ∀ j, (τ j).val ≤ σ),
      Ideal.span (Set.range a) = J ∧ (∀ κ : Φ.cones, ∃ j, κ ≤ τ j) ∧
      ∀ j, ∃ e : Φ.affineToricChart (τ j) ≅
          Spec (.of (J.affineBlowup (a j) (Localization.Away (a j)))),
        e.hom ≫ affineBlowupι (Localization.Away (a j)) (ha j) ≫
            Proj.toSpecZero (reesAlgebra.grade J) ≫
            Spec.map (reesAlgebra.gradeZeroEquiv J).toCommRingCatIso.hom =
          affineToricSchemeMap Φ.lattice hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
            ((Set.mapsTo_id (σ : Set V)).mono_left (SetLike.coe_subset_coe.mpr (hle j))) := by
  obtain ⟨e, b, hb⟩ := hσ.exists_basis_primitiveGenerators hi hN hc
  have hcone : σ = basisCone b i := (hσ.hull_eq_of_basis_primitiveGenerators hi b e hb).symm
  subst σ
  let τ := starSubdivisionChart hi hσ e
  have hτ (j : Fin 2) : (τ j).val = blowupCone b i j :=
    starSubdivisionCone_eq_blowupCone hi b hσ e hb j
  refine ⟨basisMonomial hi b, τ, basisMonomial_mem_pointIdeal hi b,
    fun j ↦ (hτ j).symm ▸ blowupCone_le b i j, (pointIdeal_eq_span hi b).symm,
    exists_le_starSubdivisionChart hi hσ e, fun j ↦ ?_⟩
  -- The cone equality transports the native scheme chart and its morphism.
  let φ (κ : PointedCone ℝ V) := affineToricScheme hi κ
  let iso := eqToIso (congrArg φ (hτ j))
  let a := basisMonomial hi b j
  let J := pointIdeal hi b
  let E := affineBlowupChartEquiv hi b j
  refine ⟨iso ≪≫ Scheme.Spec.mapIso E.toCommRingCatIso.op, ?_⟩
  -- Identify the point ideal with its kernel description in the statement.
  change (iso ≪≫ Scheme.Spec.mapIso E.toCommRingCatIso.op).hom ≫
      affineBlowupι (Localization.Away a) (basisMonomial_mem_pointIdeal hi b j) ≫
      Proj.toSpecZero (reesAlgebra.grade J) ≫
      Spec.map (reesAlgebra.gradeZeroEquiv J).toCommRingCatIso.hom = _
  rw [Iso.trans_hom, Category.assoc, Scheme.Spec.mapIso_hom, Scheme.Spec_map,
    Iso.op_hom, Quiver.Hom.unop_op]
  rw [affineBlowupChartEquiv_SpecMap]
  exact eqToIso_hom_comp_affineToricSchemeMap hi (hτ j) (blowupCone_le b i j)

private theorem exists_range_starSubdivisionChart {σ : PointedCone ℝ V}
    (hσ : IsRegularCone i σ) (e : Fin 2 ≃ ToricRay σ)
    (x : (Fan.starSubdivision hi (allRays hσ) hσ).algebraicRealization) :
    ∃ j, x ∈ Set.range ((Fan.starSubdivision hi (allRays hσ) hσ).affineToricChartι
      (starSubdivisionChart hi hσ e j)) := by
  let F := Fan.starSubdivision hi (allRays hσ) hσ
  obtain ⟨κ, y, rfl⟩ := F.exists_affineToricChartι_apply_eq x
  obtain ⟨j, hj⟩ := exists_le_starSubdivisionChart hi hσ e κ
  let h := F.isFaceOf_of_le (starSubdivisionChart hi hσ e j).property κ.property hj
  refine ⟨j, faceAffineToricSchemeMap hi h y, ?_⟩
  rw [← Scheme.Hom.comp_apply, Fan.faceAffineToricSchemeMap_comp_affineToricChartι]

private theorem iSup_opensRange_reesChartMap :
    (⨆ j, (reesChartMap hi b j).opensRange) = ⊤ := by
  simp only [reesChartMap, Scheme.Hom.opensRange_comp_of_isIso]
  exact iSup_opensRange_affineBlowupι (pointIdeal_eq_span hi b).symm

section AffineGluing

variable {σ : PointedCone ℝ V} (hσ : IsRegularCone i σ) (e : Fin 2 ≃ ToricRay σ)
  (hb : ∀ j, b j = primitiveGenerator hi hσ.toIsToricCone (e j))

local notation "F" => Fan.starSubdivision hi (allRays hσ) hσ
local notation "J" => pointIdeal hi b
local notation "π" => (Proj.toSpecZero (reesAlgebra.grade J) ≫
  Spec.map (Iso.hom (RingEquiv.toCommRingCatIso (reesAlgebra.gradeZeroEquiv J))))
local notation "ιₛ" => fun j : Fin 2 ↦ Fan.affineToricChartι F (starSubdivisionChart hi hσ e j)
local notation "ψ" => fun j : Fin 2 ↦ (Iso.hom (starChartIso hi b hσ e hb j) ≫ reesChartMap hi b j)
local notation "𝓘" => ofIdealTop
  (Ideal.map (CommRingCat.Hom.hom (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of R)))) J)

private theorem isEffectiveCartier_comap_affineSubdivision
    (p : Fan.algebraicRealization F ⟶ affineToricScheme hi (basisCone b i))
    (hp : ∀ j : Fin 2, ιₛ j ≫ p = ψ j ≫ π) : (comap 𝓘 p).IsEffectiveCartier := by
  apply isEffectiveCartier_of_forall_exists_isOpenImmersion
  intro x
  obtain ⟨j, hj⟩ := exists_range_starSubdivisionChart hi hσ e x
  refine ⟨_, ιₛ j, inferInstance, hj, ?_⟩
  rw [← comap_comp, hp, comap_comp]
  exact (isEffectiveCartier_comap_toSpecZero_reesAlgebra J).comap (ψ j)

private theorem injective_affineSubdivision_lift
    (f : Fan.algebraicRealization F ⟶ Proj (reesAlgebra.grade J))
    (hf : ∀ j : Fin 2, ιₛ j ≫ f = ψ j) : Function.Injective f := by
  intro x y hxy
  obtain ⟨j, u, rfl⟩ := exists_range_starSubdivisionChart hi hσ e x
  obtain ⟨k, v, rfl⟩ := exists_range_starSubdivisionChart hi hσ e y
  have hinj (j : Fin 2) : Function.Injective (ιₛ j ≫ f) := by
    rw [hf j]
    exact (ψ j).isOpenEmbedding.injective
  rcases Fin.fin_two_eq_or_eq_rev j k with hk | hk
  · subst k
    exact congrArg (ιₛ j) (hinj j hxy)
  · subst k
    have hm : (reesChartMap hi b j) ((starChartIso hi b hσ e hb j).hom u) ∈
        (reesChartMap hi b j.rev).opensRange := by
      rw [Scheme.Hom.mem_opensRange]
      refine ⟨(starChartIso hi b hσ e hb j.rev).hom v, ?_⟩
      simpa only [← Scheme.Hom.comp_apply, ← hf] using hxy.symm
    have hu : (starChartIso hi b hσ e hb j).hom u ∈
        (reesChartMap hi b j) ⁻¹ᵁ (reesChartMap hi b j.rev).opensRange := hm
    rw [reesChartMap_preimage_opensRange] at hu
    obtain ⟨w, hw⟩ := mem_range_starSubdivisionChart_of_mem_basicOpen hi b hσ e hb j u hu
    calc
      ιₛ j u = ιₛ j.rev w := hw.symm
      _ = ιₛ j.rev v := congrArg (ιₛ j.rev) (hinj j.rev (by simpa only [Scheme.Hom.comp_apply, hw]))

private theorem isIso_affineSubdivision_lift
    (f : Fan.algebraicRealization F ⟶ Proj (reesAlgebra.grade J))
    (hf : ∀ j : Fin 2, ιₛ j ≫ f = ψ j) : IsIso f := by
  have hopen (j : Fin 2) : IsOpenImmersion (ιₛ j ≫ f) := by
    rw [hf j]
    infer_instance
  have : IsOpenImmersion f :=
    IsOpenImmersion.of_forall_source_exists f (injective_affineSubdivision_lift hi b hσ e hb f hf)
      fun x ↦ by
        obtain ⟨j, hj⟩ := exists_range_starSubdivisionChart hi hσ e x
        exact ⟨_, ιₛ j, inferInstance, hj, hopen j⟩
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top f (top_unique fun x _ ↦ ?_)
  have hx : x ∈ ⨆ j, (reesChartMap hi b j).opensRange := by
    rw [iSup_opensRange_reesChartMap hi b]
    trivial
  obtain ⟨j, hx⟩ := Opens.mem_iSup.mp hx
  have hopenRange : (ιₛ j ≫ f).opensRange = (reesChartMap hi b j).opensRange := by
    apply SetLike.ext
    intro y
    simp only [Scheme.Hom.mem_opensRange]
    rw [hf j]
    refine ⟨fun ⟨z, hz⟩ ↦ ⟨(starChartIso hi b hσ e hb j).hom z, hz⟩, ?_⟩
    rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := (starChartIso hi b hσ e hb j).hom.surjective z
    exact ⟨w, hz⟩
  rw [← hopenRange, Scheme.Hom.mem_opensRange] at hx
  obtain ⟨z, rfl⟩ := hx
  exact ⟨ιₛ j z, rfl⟩

private theorem exists_iso_reesBlowup_of_chartMaps
    (p : Fan.algebraicRealization F ⟶ affineToricScheme hi (basisCone b i))
    (hp : ∀ j : Fin 2, ιₛ j ≫ p = ψ j ≫ π) :
    ∃ g : Fan.algebraicRealization F ≅ Proj (reesAlgebra.grade J), g.hom ≫ π = p := by
  have hI := isEffectiveCartier_comap_affineSubdivision hi b hσ e hb p hp
  let f := projReesAlgebraLift J p hI
  have hf : f ≫ π = p := projReesAlgebraLift_toSpecZero p hI
  have hCharts (j : Fin 2) : ιₛ j ≫ f = ψ j := by
    have hc : (ιₛ j ≫ f) ≫ π = ψ j ≫ π := by rw [Category.assoc, hf, hp]
    have hCartier : (comap 𝓘 ((ιₛ j ≫ f) ≫ π)).IsEffectiveCartier := by
      rw [Category.assoc, hf, comap_comp]
      exact hI.comap (ιₛ j)
    exact projReesAlgebra_hom_ext (by simpa only [Category.assoc] using hc)
      (by simpa only [Category.assoc] using hCartier)
  have := isIso_affineSubdivision_lift hi b hσ e hb f hCharts
  exact ⟨asIso f, hf⟩

end AffineGluing

private theorem affineToricSchemeMap_eq_of_maps_eq_id {κ σ : PointedCone ℝ V}
    {f : N →+ N} {g : V →ₗ[ℝ] V} (hfg : ∀ n, g (i n) = i (f n))
    (hm : Set.MapsTo g (κ : Set V) (σ : Set V)) (hle : κ ≤ σ)
    (hf : f = AddMonoidHom.id N) (hg : g = LinearMap.id) :
    affineToricSchemeMap hi hi f g hfg hm =
      affineToricSchemeMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
        ((Set.mapsTo_id (σ : Set V)).mono_left (SetLike.coe_subset_coe.mpr hle)) := by
  subst f g
  rfl

/-- The star subdivision along the rays of a full-dimensional regular cone in rank two
is the blowup of the affine toric scheme at its distinguished point. The identification
commutes with the native toric map to the fan of faces of the original cone. -/
theorem exists_iso_reesBlowup_starSubdivision {σ : PointedCone ℝ V}
    (hσ : IsRegularCone i σ) (hN : Module.finrank ℤ N = 2) (hc : Nat.card (ToricRay σ) = 2) :
    let A := ToricRay.faceFinset (PointedCone.IsFaceOf.refl σ) hσ.fg
    let Φ := Fan.starSubdivision hi A hσ
    let Ψ := Fan.ofCone hi hσ.toIsToricCone
    let τ : Ψ.cones := ⟨σ, (Fan.mem_ofCone_cones hi _).2 (.refl σ)⟩
    let I := RingHom.ker (distinguishedPoint hi (⊤ : σ.Face)).toRingHom
    ∃ (hA : A.Nonempty) (e : Φ.algebraicRealization ≅ Proj (reesAlgebra.grade I)),
      e.hom ≫ Proj.toSpecZero (reesAlgebra.grade I) ≫
          Spec.map (reesAlgebra.gradeZeroEquiv I).toCommRingCatIso.hom ≫ Ψ.affineToricChartι τ =
        (Fan.starSubdivision_isSubdivision hi A hσ hA).toFanHom.algebraicMap := by
  obtain ⟨e, b, hb⟩ := hσ.exists_basis_primitiveGenerators hi hN hc
  have hcone : σ = basisCone b i := (hσ.hull_eq_of_basis_primitiveGenerators hi b e hb).symm
  subst σ
  let A := allRays hσ
  let F := Fan.starSubdivision hi A hσ
  let Ψ := Fan.ofCone hi hσ.toIsToricCone
  let τ : Ψ.cones := ⟨basisCone b i, (Fan.mem_ofCone_cones hi _).2 (.refl _)⟩
  let f₀ := Ψ.affineToricChartι τ
  have : IsIso f₀ := Fan.isIso_affineToricChartι_ofCone hi hσ.toIsToricCone
  have hA : A.Nonempty :=
    ⟨e 0, (ToricRay.mem_faceFinset _ _).2 (e 0).val.isFaceOf.le⟩
  let f := (Fan.starSubdivision_isSubdivision hi A hσ hA).toFanHom
  let π := Proj.toSpecZero (reesAlgebra.grade (pointIdeal hi b)) ≫
    Spec.map (reesAlgebra.gradeZeroEquiv (pointIdeal hi b)).toCommRingCatIso.hom
  let p := f.algebraicMap ≫ inv f₀
  have hp (j : Fin 2) : F.affineToricChartι (starSubdivisionChart hi hσ e j) ≫ p =
      ((starChartIso hi b hσ e hb j).hom ≫ reesChartMap hi b j) ≫ π := by
    let κ := starSubdivisionChart hi hσ e j
    have hκ : κ.val = blowupCone b i j := starSubdivisionCone_eq_blowupCone hi b hσ e hb j
    have hle : κ.val ≤ τ.val := by
      exact hκ.symm ▸ blowupCone_le b i j
    have hm : Set.MapsTo f.realMap (κ.val : Set V) (τ.val : Set V) := by
      rw [Fan.IsSubdivision.toFanHom_realMap]
      exact (Set.mapsTo_id (τ.val : Set V)).mono_left (SetLike.coe_subset_coe.mpr hle)
    apply (cancel_mono f₀).mp
    simp only [p, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [f.affineToricChartι_comp_algebraicMap_of_mapsTo κ τ hm]
    unfold π reesChartMap
    simp only [Category.assoc]
    rw [affineBlowupChartEquiv_SpecMap_assoc, ← Category.assoc,
      affineToricSchemeMap_eq_of_maps_eq_id hi f.map_lattice hm hle
        (Fan.IsSubdivision.toFanHom_latticeMap _) (Fan.IsSubdivision.toFanHom_realMap _)]
    exact congrArg (· ≫ f₀)
      (eqToIso_hom_comp_affineToricSchemeMap hi hκ (blowupCone_le b i j)).symm
  obtain ⟨g, hg⟩ := exists_iso_reesBlowup_of_chartMaps hi b hσ e hb p hp
  refine ⟨hA, g, ?_⟩
  -- Fold the kernel ideal and the maximal affine chart used in the comparison.
  change g.hom ≫ Proj.toSpecZero (reesAlgebra.grade (pointIdeal hi b)) ≫
    Spec.map (reesAlgebra.gradeZeroEquiv (pointIdeal hi b)).toCommRingCatIso.hom ≫ f₀ =
      f.algebraicMap
  simpa only [p, π, Category.assoc, IsIso.inv_hom_id, Category.comp_id] using
    congrArg (· ≫ f₀) hg

end TauCeti.Toric
