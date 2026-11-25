/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Basic
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Degenerate binary quadratics on the projective line

Over a field of characteristic different from two, the projective vanishing
locus of a nonzero binary quadratic of discriminant zero has at most one point.
-/

public section

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

open _root_.AlgebraicGeometry Polynomial TopologicalSpace

variable {K : Type u} [Field K]

local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule K (Fin 2 → K)
local notation "A" => _root_.SymmetricAlgebra K (Fin 2 → K)

private theorem subsingleton_compl_basicOpen_coord (i : Fin 2) :
    ((Proj.basicOpen 𝒜 (coord K i) : Set (projectiveLine K))ᶜ).Subsingleton := by
  have hchart (p : projectiveLine K) (hp : p ∉ Proj.basicOpen 𝒜 (coord K i)) :
      ∃ q : Spec (.of K[X]), polynomialChartι K i.rev q = p ∧ X ∈ q.asIdeal := by
    have hr (j : Fin 2) :
        Set.range (polynomialChartι K j) = (Proj.basicOpen 𝒜 (coord K j) : Set _) := by
      rw [← Scheme.Hom.coe_opensRange, opensRange_polynomialChartι]
    have h : p ∈ Set.range (polynomialChartι K i) ∪ Set.range (polynomialChartι K i.rev) := by
      have hu := Set.mem_univ p
      rw [← range_polynomialChartι_union_range_polynomialChartι K] at hu
      fin_cases i
      · exact hu
      · exact Or.symm hu
    obtain ⟨q, rfl⟩ := h.resolve_left (hr i ▸ hp)
    refine ⟨q, rfl, ?_⟩
    apply not_not.mp ((polynomialChartι_mem_range_iff K i.rev q).not.mp ?_)
    simpa only [Fin.rev_rev, hr i, SetLike.mem_coe] using hp
  have hmax : (Ideal.span {(X : K[X])}).IsMaximal := by
    simpa only [ker_evalRingHom, C_0, sub_zero] using
      RingHom.ker_isMaximal_of_surjective (evalRingHom (0 : K))
        (fun a ↦ ⟨C a, eval_C⟩)
  intro p hp p' hp'
  obtain ⟨q, rfl, hq⟩ := hchart p hp
  obtain ⟨q', rfl, hq'⟩ := hchart p' hp'
  congr 1
  exact PrimeSpectrum.ext ((hmax.eq_of_le q.isPrime.ne_top
    (Ideal.span_singleton_le_iff_mem _ |>.mpr hq)).symm.trans
    (hmax.eq_of_le q'.isPrime.ne_top (Ideal.span_singleton_le_iff_mem _ |>.mpr hq')))

/-- A nonzero binary quadratic with zero discriminant has at most one projective zero
over a field of characteristic different from two. -/
theorem subsingleton_compl_basicOpen_of_discrim_eq_zero [NeZero (2 : K)] {a b c : K}
    (h : discrim a b c = 0)
    (hne : algebraMap K A a * coord K 0 ^ 2 + algebraMap K A b * coord K 0 * coord K 1 +
      algebraMap K A c * coord K 1 ^ 2 ≠ 0) :
    ((Proj.basicOpen 𝒜 (algebraMap K A a * coord K 0 ^ 2 +
      algebraMap K A b * coord K 0 * coord K 1 + algebraMap K A c * coord K 1 ^ 2) :
        Set (projectiveLine K))ᶜ).Subsingleton := by
  classical
  have hopen (u : K) (hu : u ≠ 0) (l : A) :
      Proj.basicOpen 𝒜 (algebraMap K A u * l ^ 2) = Proj.basicOpen 𝒜 l := by
    have htop : Proj.basicOpen 𝒜 (algebraMap K A u) = ⊤ :=
      top_unique (Proj.basicOpen_one 𝒜 ▸ Proj.basicOpen_mono 𝒜 _ _
        (isUnit_iff_dvd_one.mp (hu.isUnit.map (algebraMap K A))))
    rw [Proj.basicOpen_mul, Proj.basicOpen_pow 𝒜 _ 2 (by decide), htop, top_inf_eq]
  by_cases ha : a = 0
  · have hb : b = 0 := by simpa [discrim, ha] using h
    have hc : c ≠ 0 := by rintro rfl; simp [ha, hb] at hne
    simpa only [ha, hb, map_zero, zero_mul, add_zero, zero_add, hopen c hc] using
      subsingleton_compl_basicOpen_coord (K := K) 1
  let t := b / (2 * a)
  have heq : a * t ^ 2 = c := by
    unfold discrim at h
    dsimp only [t]
    field_simp
    linear_combination h
  have ht : a * (2 * t) = b := by dsimp only [t]; field_simp
  have hq : algebraMap K A a * coord K 0 ^ 2 +
      algebraMap K A b * coord K 0 * coord K 1 + algebraMap K A c * coord K 1 ^ 2 =
      algebraMap K A a * (coord K 0 + t • coord K 1) ^ 2 := by
    rw [← heq, ← ht, Algebra.smul_def]
    simp only [map_mul, map_pow, map_ofNat]
    ring
  rw [hq, hopen a ha]
  by_cases ht₀ : t = 0
  · simpa only [ht₀, zero_smul, add_zero] using subsingleton_compl_basicOpen_coord (K := K) 0
  let u := Units.mk0 t ht₀
  have hu : (u : K) = t := rfl
  rw [← hu, basicOpen_coord_add_smul_eq_compl_support]
  simp only [Closeds.coe_compl, compl_compl]
  let p := polynomialPoint K (RingHom.id K) 0 (-(↑u⁻¹ : K))
  have hi : IsClosedImmersion p :=
    isClosedImmersion_of_comp_eq_id (projectiveLine K ↘ Spec (.of K)) p
      (by simp [p, polynomialPoint_over])
  rw [p.support_ker, p.isClosedEmbedding.isClosed_range.closure_eq]
  exact Set.subsingleton_range p

end TauCeti.AlgebraicGeometry.projectiveLine
