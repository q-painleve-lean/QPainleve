/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.SelfIntersection
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Boundary

import Mathlib.LinearAlgebra.Transvection.Basic
import QPainleve.Geometry.Toric.Cone.Coordinates
import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision
import QPainleve.Geometry.Toric.Fan.StarSubdivision.TwoDimensional
import QPainleve.Geometry.Toric.Fan.TwoDimensional

/-!
# Inverse star subdivisions of toric surfaces

A boundary curve of square `-1` on a regular complete toric surface arises from
subdividing the cone spanned by its two neighboring rays. The new fan replaces
the two incident cones by that single regular cone. The identified ray is the
exceptional ray of the subdivision.

This is the fan calculation for the contraction of a torus-invariant exceptional
curve, as in Cox, Little and Schenck, *Toric Varieties*, §10.4.
-/

public noncomputable section

open PointedCone Module
open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

section Combinatorial

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

private lemma mem_starSubdivision_basisCone_iff (hi : IsIntegralLattice i)
    (b : Basis (Fin 2) ℤ N) {σ : PointedCone ℝ V}
    (hσ : IsRegularCone i σ) (he : σ = hull ℝ (Set.range (i ∘ b))) (C : PointedCone ℝ V) :
    C ∈ (starSubdivision hi (ToricRay.faceFinset (IsFaceOf.refl σ) hσ.fg) hσ).cones ↔
      ∃ j : Fin 2, C.IsFaceOf (hull ℝ {i (b 0 + b 1), i (b j)}) := by
  let A := ToricRay.faceFinset (IsFaceOf.refl σ) hσ.fg
  obtain ⟨e, hb⟩ := hσ.exists_rayEquiv_of_basis hi b he
  have hchart (j : Fin 2) := hσ.starSubdivisionCone_pair_mem hi e j
  constructor
  · intro hC
    obtain ⟨j, hj⟩ := hσ.exists_le_starSubdivisionCone_pair hi e hC
    have hface := (starSubdivision hi A hσ).isFaceOf_of_le (hchart j) hC hj
    exact ⟨j, by simpa only [hσ.starSubdivisionCone_pair_eq_hull hi b e hb] using hface⟩
  · rintro ⟨j, h⟩
    rw [← hσ.starSubdivisionCone_pair_eq_hull hi b e hb j] at h
    exact (starSubdivision hi A hσ).mem_of_isFaceOf (hchart j) h

private lemma exists_regular_fan_replace_basis_sum (hΦ : Φ.IsRegular)
    (b : Basis (Fin 2) ℤ N)
    (hr : hull ℝ {i (b 0 + b 1)} ∈ Φ.cones)
    (hcharts : ∀ j : Fin 2, hull ℝ {i (b 0 + b 1), i (b j)} ∈ Φ.cones) :
    ∃ Ψ : Fan i, Ψ.IsRegular ∧ ∀ C : PointedCone ℝ V, C ∈ Ψ.cones ↔
      C.IsFaceOf (hull ℝ (Set.range (i ∘ b))) ∨
        (C ∈ Φ.cones ∧ ¬ hull ℝ {i (b 0 + b 1)} ≤ C) := by
  let σ₀ := hull ℝ (Set.range (i ∘ b))
  let R := hull ℝ {i (b 0 + b 1)}
  let A := {C | C ∈ Φ.cones ∧ ¬ R ≤ C}
  let S := insert σ₀ A
  have hσreg : IsRegularCone i σ₀ := by
    simpa only [σ₀, Set.image_univ, Set.range_comp] using
      isRegularCone_hull_image_basis Φ.lattice b Set.univ
  have hreg (C) (hC : C ∈ S) : IsRegularCone i C := by
    rcases Set.mem_insert_iff.mp hC with rfl | hC
    · exact hσreg
    · exact (isRegular_iff.mp hΦ) _ hC.1
  let B := Φ.lattice.isBaseChange.basis b
  have hB (j : Fin 2) : B j = i (b j) := IsBaseChange.basis_apply _ _ _
  have hB' : (B : Fin 2 → V) = i ∘ b := funext hB
  have hR : hull ℝ {B 0 + B 1} = R := by simp only [hB, R, map_add]
  have hchart (j : Fin 2) : hull ℝ {B 0 + B 1, B j} = hull ℝ {i (b 0 + b 1), i (b j)} := by
    simp only [hB, map_add]
  have hface {C} (hC : C ∈ A) : (C ⊓ σ₀).IsFaceOf C ∧ (C ⊓ σ₀).IsFaceOf σ₀ := by
    simp only [σ₀, ← hB']
    exact B.face_inter_basisHull_of_not_le
      (hR ▸ Φ.inf_isFaceOf_left hC.1 hr)
      (fun j ↦ hchart j ▸ ⟨Φ.inf_isFaceOf_left hC.1 (hcharts j),
        Φ.inf_isFaceOf_right hC.1 (hcharts j)⟩) (hR ▸ hC.2)
  have hinter ⦃C D : PointedCone ℝ V⦄ (hC : C ∈ S) (hD : D ∈ S) : (C ⊓ D).IsFaceOf C := by
    rcases Set.mem_insert_iff.mp hC with rfl | hC <;>
      rcases Set.mem_insert_iff.mp hD with rfl | hD
    · rw [inf_idem]
    · exact inf_comm D σ₀ ▸ (hface hD).2
    · exact (hface hC).1
    · exact Φ.inf_isFaceOf_left hC.1 hD.1
  let Ψ := ofCones Φ.lattice S ((Φ.finite_cones.subset (t := A) (fun _ h ↦ h.1)).insert σ₀)
    (fun _ h ↦ (hreg _ h).toIsToricCone) hinter
  have hΨ : Ψ.IsRegular :=
    isRegular_iff.mpr fun C hC ↦
      let ⟨D, hD, hCD⟩ := (mem_ofCones_cones ..).mp hC
      (hreg D hD).of_isFaceOf hCD
  refine ⟨Ψ, hΨ, fun C ↦ (mem_ofCones_cones ..).trans ?_⟩
  constructor
  · rintro ⟨E, hE, hCE⟩
    rcases Set.mem_insert_iff.mp hE with rfl | hE
    · exact Or.inl hCE
    · exact Or.inr ⟨Φ.mem_of_isFaceOf hE.1 hCE, fun h ↦ hE.2 (h.trans hCE.le)⟩
  · rintro (hC | ⟨hC, hn⟩)
    · exact ⟨σ₀, Set.mem_insert _ _, hC⟩
    · exact ⟨C, Set.mem_insert_of_mem _ ⟨hC, hn⟩, .rfl⟩

private lemma starSubdivisionAlong_eq_of_replace_basis_sum
    {Ψ : Fan i} (hΨ : Ψ.IsRegular) (b : Basis (Fin 2) ℤ N) (σ : Ψ.cones)
    (hσ : σ.val = hull ℝ (Set.range (i ∘ b))) (hcard : Nat.card (ToricRay σ.val) = 2)
    (hcones : ∀ C : PointedCone ℝ V, C ∈ Ψ.cones ↔
      C.IsFaceOf σ.val ∨ (C ∈ Φ.cones ∧ ¬ hull ℝ {i (b 0 + b 1)} ≤ C))
    (hcharts : ∀ j : Fin 2, hull ℝ {i (b 0 + b 1), i (b j)} ∈ Φ.cones)
    (hcover : ∀ C ∈ Φ.cones, hull ℝ {i (b 0 + b 1)} ≤ C →
      ∃ j : Fin 2, C ≤ hull ℝ {i (b 0 + b 1), i (b j)}) :
    Ψ.starSubdivisionAlong hΨ σ.property = Φ := by
  let R := hull ℝ {i (b 0 + b 1)}
  have hmid : R ≤ σ.val := by
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    rw [hσ, map_add]
    exact Submodule.add_mem _ (subset_hull (Set.mem_range_self 0))
      (subset_hull (Set.mem_range_self 1))
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  have hreg := isRegular_iff.mp hΨ _ σ.property
  apply Fan.ext
  ext C
  have hlocal := mem_starSubdivision_basisCone_iff Ψ.lattice b hreg hσ C
  rw [Ψ.mem_starSubdivisionAlong_cones hΨ σ.property]
  constructor
  · rintro (⟨hC, hn⟩ | ⟨D, hD, hσD, hC⟩)
    · rcases (hcones C).mp hC with hCD | ⟨hC, -⟩
      · obtain ⟨j, hj⟩ := hlocal.mp (mem_starSubdivision_cones_of_isFaceOf _ _ _ hCD
          (ToricRay.exists_mem_faceFinset_not_le_of_not_le _ _ hreg.toIsToricCone.salient hn))
        exact Φ.mem_of_isFaceOf (hcharts j) hj
      · exact hC
    · have heq : σ.val = D :=
        congrArg Subtype.val (eq_of_le_fullCone hΨ hN hcard (τ := ⟨D, hD⟩) hσD)
      subst D
      obtain ⟨j, hj⟩ := hlocal.mp hC
      exact Φ.mem_of_isFaceOf (hcharts j) hj
  · intro hC
    by_cases h : R ≤ C
    · obtain ⟨j, hj⟩ := hcover C hC h
      exact Or.inr ⟨σ.val, σ.property, le_rfl, hlocal.mpr
        ⟨j, Φ.isFaceOf_of_le (hcharts j) hC hj⟩⟩
    · exact Or.inl ⟨(hcones C).mpr (Or.inr ⟨hC, h⟩), fun hn ↦ h (hmid.trans hn)⟩

private lemma exists_coarsening_at_basis_sum (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (b : Basis (Fin 2) ℤ N)
    (hr : hull ℝ {i (b 0 + b 1)} ∈ Φ.cones)
    (hcharts : ∀ j : Fin 2, hull ℝ {i (b 0 + b 1), i (b j)} ∈ Φ.cones)
    (hcover : ∀ C ∈ Φ.cones, hull ℝ {i (b 0 + b 1)} ≤ C →
      ∃ j : Fin 2, C ≤ hull ℝ {i (b 0 + b 1), i (b j)}) :
    ∃ (Ψ : Fan i) (hΨ : Ψ.IsRegular) (σ : Ψ.cones)
      (hσ : Nat.card (ToricRay σ.val) = 2),
      Ψ.IsComplete ∧ Ψ.starSubdivisionAlong hΨ σ.property = Φ ∧
        (Ψ.starSubdivisionAlongRay hΨ σ.property (ne_bot_of_card_toricRay_eq_two hσ)).toCone.val =
          hull ℝ {i (b 0 + b 1)} ∧ hull ℝ {i (b 0 + b 1)} ∉ Ψ.cones ∧
        σ.val = hull ℝ (Set.range (i ∘ b)) := by
  obtain ⟨Ψ, hΨ, hcones⟩ := exists_regular_fan_replace_basis_sum hΦ b hr hcharts
  let σ₀ := hull ℝ (Set.range (i ∘ b))
  let σ : Ψ.cones := ⟨σ₀, (hcones σ₀).mpr (Or.inl .rfl)⟩
  have hreg := isRegular_iff.mp hΨ _ σ.property
  obtain ⟨e, he⟩ := hreg.exists_rayEquiv_of_basis Ψ.lattice b (by rfl)
  have hcard : Nat.card (ToricRay σ.val) = 2 := by rw [← Nat.card_congr e, Nat.card_fin]
  have hstar := starSubdivisionAlong_eq_of_replace_basis_sum hΨ b σ (by rfl) hcard
    hcones hcharts hcover
  have hΨc : Ψ.IsComplete :=
    (Ψ.starSubdivisionAlong_isSubdivision hΨ σ.property
      (ne_bot_of_card_toricRay_eq_two hcard)).isComplete_iff.mp (hstar.symm ▸ hc)
  refine ⟨Ψ, hΨ, σ, hcard, hΨc, hstar, ?_, ?_, rfl⟩
  · rw [coe_toCone_starSubdivisionAlongRay,
      hreg.sum_primitiveGenerator_allRays Ψ.lattice b e he]
  · intro h
    rcases (hcones _).mp h with hf | ⟨_, hn⟩
    · let B := Φ.lattice.isBaseChange.basis b
      have hb (j : Fin 2) : B j = i (b j) := IsBaseChange.basis_apply _ _ _
      have hbasis : (B : Fin 2 → V) = i ∘ b := funext hb
      rw [← hbasis, map_add, ← hb 0, ← hb 1] at hf
      have hb₀ : B 0 ∈ hull ℝ (Set.range B) := subset_hull (Set.mem_range_self _)
      have hb₁ : B 1 ∈ hull ℝ (Set.range B) := subset_hull (Set.mem_range_self _)
      have hsum : B 0 + B 1 ∈ hull ℝ {B 0 + B 1} := subset_hull (Set.mem_singleton _)
      have hm := (B.mem_hull_sum_iff hb₀).mp (hf.mem_of_add_mem_left hb₀ hb₁ hsum)
      simp [LinearMap.sub_apply, Basis.coord_apply] at hm
    · exact hn le_rfl

private lemma exists_basis_of_sum_eq (a : Basis (Fin 2) ℤ N) :
    ∃ b : Basis (Fin 2) ℤ N, b 0 = a 0 ∧ b 0 + b 1 = a 1 := by
  have hzero : (-(a.coord 1)) (a 0) = 0 := by simp
  let b := a.map (LinearEquiv.transvection hzero)
  have h₀ : b 0 = a 0 := by simp [b, LinearMap.transvection.apply, hzero]
  have h₁ : b 1 = a 1 - a 0 := by
    simp [b, LinearMap.transvection.apply, sub_eq_add_neg]
  exact ⟨b, h₀, by rw [h₀, h₁]; abel⟩

private lemma le_or_le_of_ray_neighbors (hΦ : Φ.IsRegular)
    (hN : Module.finrank ℤ N = 2) {p r q : Φ.Ray}
    (hn : ∀ t : Φ.Ray, (r ≠ t ∧ ∃ C : Φ.cones, r.toCone ≤ C ∧ t.toCone ≤ C) ↔
      t = p ∨ t = q)
    {C : Φ.cones} (hr : r.toCone ≤ C) :
    C.val ≤ p.toCone.val ⊔ r.toCone.val ∨ C.val ≤ q.toCone.val ⊔ r.toCone.val := by
  by_cases ht : ∃ t : Φ.Ray, r ≠ t ∧ t.toCone ≤ C
  · obtain ⟨t, hne, ht⟩ := ht
    have he := cone_eq_sup_of_ray_ne_of_le hΦ hN hne hr ht
    rcases (hn t).mp ⟨hne, C, hr, ht⟩ with rfl | rfl
    · exact Or.inl (by rw [he, sup_comm])
    · exact Or.inr (by rw [he, sup_comm])
  · have hC : C ≤ r.toCone := by
      apply Φ.le_iff_forall_ray_le.mpr
      intro t htC
      by_cases h : r = t
      · rw [← h]
      · exact (ht ⟨t, h, htC⟩).elim
    exact Or.inl (le_trans (show C.val ≤ r.toCone.val from hC) le_sup_right)

/-- A ray whose two adjacent primitive generators sum to its generator can be
removed by an inverse star subdivision. The coarser fan is complete and regular,
and the removed ray is absent from it. The center cone is spanned by the neighbors. -/
theorem exists_star_subdivision_of_ray_eq_sum
    (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    {p r q : Φ.Ray}
    (hp : b.detDualEquiv p.primitiveGenerator r.primitiveGenerator = 1 ∧
      ∃ C : Φ.cones, p.toCone ≤ C ∧ r.toCone ≤ C)
    (hq : b.detDualEquiv r.primitiveGenerator q.primitiveGenerator = 1 ∧
      ∃ C : Φ.cones, r.toCone ≤ C ∧ q.toCone ≤ C)
    (hsum' : p.primitiveGenerator + q.primitiveGenerator = r.primitiveGenerator) :
    ∃ (Ψ : Fan i) (hΨ : Ψ.IsRegular) (σ : Ψ.cones)
      (hσ : Nat.card (ToricRay σ.val) = 2),
      Ψ.IsComplete ∧ Ψ.starSubdivisionAlong hΨ σ.property = Φ ∧
        (Ψ.starSubdivisionAlongRay hΨ σ.property (ne_bot_of_card_toricRay_eq_two hσ)).toCone.val =
          r.toCone.val ∧ r.toCone.val ∉ Ψ.cones ∧
        σ.val = p.toCone.val ⊔ q.toCone.val := by
  have hn := ray_neighbors_iff_of_det b hΦ hc hp hq
  obtain ⟨hp, C, hrC, hpC⟩ := (hn p).mpr (Or.inl rfl)
  obtain ⟨hq, D, hrD, hqD⟩ := (hn q).mpr (Or.inr rfl)
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  obtain ⟨a, ha₀, ha₁⟩ := exists_basis_of_ray_ne_of_le
    ((isRegular_iff.mp hΦ) _ C.property) hN hp.symm hpC hrC
  obtain ⟨c, hc₀, hcr⟩ := exists_basis_of_sum_eq a
  rw [ha₀] at hc₀
  rw [ha₁] at hcr
  have hc₁ : c 1 = q.primitiveGenerator := add_left_cancel (hc₀ ▸ hcr.trans hsum'.symm)
  have hr : hull ℝ {i (c 0 + c 1)} = r.toCone.val := by
    rw [hcr, Ray.toCone_eq_hull_primitiveGenerator]
  have hcharts : ∀ j : Fin 2, hull ℝ {i (c 0 + c 1), i (c j)} =
      (if j = 0 then p.toCone.val else q.toCone.val) ⊔ r.toCone.val := by
    have hjoin (x y : V) : hull ℝ {x, y} = hull ℝ {y} ⊔ hull ℝ {x} := by
      rw [← Set.singleton_union, hull, Submodule.span_union, sup_comm]
    intro j
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    · rw [hjoin, hr, hc₀, ite_eq_left rfl, Ray.toCone_eq_hull_primitiveGenerator p]
    · rw [hjoin, hr, hc₁, ite_eq_right (by decide : (1 : Fin 2) ≠ 0),
        Ray.toCone_eq_hull_primitiveGenerator q]
  have hcharts' (j : Fin 2) : hull ℝ {i (c 0 + c 1), i (c j)} ∈ Φ.cones := by
    rw [hcharts]
    fin_cases j
    · simpa [cone_eq_sup_of_ray_ne_of_le hΦ hN hp.symm hpC hrC] using C.property
    · simpa [cone_eq_sup_of_ray_ne_of_le hΦ hN hq.symm hqD hrD] using D.property
  have hcover (E : PointedCone ℝ V) (hE : E ∈ Φ.cones)
      (hRE : hull ℝ {i (c 0 + c 1)} ≤ E) :
      ∃ j : Fin 2, E ≤ hull ℝ {i (c 0 + c 1), i (c j)} := by
    have hrE : r.toCone.val ≤ E := hr ▸ hRE
    rcases le_or_le_of_ray_neighbors hΦ hN hn (C := ⟨E, hE⟩) hrE with h | h
    · exact ⟨0, by rw [hcharts 0, ite_eq_left rfl]; exact h⟩
    · exact ⟨1, by rw [hcharts 1, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]; exact h⟩
  obtain ⟨Ψ, hΨ, σ, hσ, hc', hstar, hnew, hremoved, hcone⟩ :=
    exists_coarsening_at_basis_sum hΦ hc c (hr ▸ r.toCone.property) hcharts' hcover
  refine ⟨Ψ, hΨ, σ, hσ, hc', hstar, hnew.trans hr, hr ▸ hremoved, ?_⟩
  rw [hcone, p.toCone_eq_hull_primitiveGenerator, q.toCone_eq_hull_primitiveGenerator,
    ← Submodule.span_union, ← hc₀, ← hc₁]
  congr 1
  ext x
  simp [Fin.exists_fin_succ, eq_comm, or_comm]

end Combinatorial

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

/-- A ray of boundary self-intersection `-1` in a complete regular toric surface
is the inserted ray of a star subdivision of a complete regular fan. The
subdivision is along a two-ray cone, and recovers the given fan on its lattice. -/
theorem exists_star_subdivision_of_ray_self_intersection_neg_one
    [Φ.algebraicRealization.IsProjectiveOver ℂ]
    (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (r : Φ.Ray)
    (hself : Φ.rayBoundarySelfIntersection hΦ r = -1) :
    ∃ (Ψ : Fan i) (hΨ : Ψ.IsRegular) (σ : Ψ.cones)
      (hσ : Nat.card (ToricRay σ.val) = 2),
      Ψ.IsComplete ∧ Ψ.starSubdivisionAlong hΨ σ.property = Φ ∧
        (Ψ.starSubdivisionAlongRay hΨ σ.property (ne_bot_of_card_toricRay_eq_two hσ)).toCone.val =
          r.toCone.val := by
  obtain ⟨p, q, hpDet, hqDet, hn, hsum⟩ :=
    exists_rayBoundaryPoint_selfIntersection_relation b hΦ hc r
  rw [← rayBoundarySelfIntersection_def, hself, neg_one_zsmul] at hsum
  have hsum' : p.primitiveGenerator + q.primitiveGenerator = r.primitiveGenerator := by
    calc
      _ = (p.primitiveGenerator + -r.primitiveGenerator + q.primitiveGenerator) +
          r.primitiveGenerator := by abel
      _ = _ := by rw [hsum, zero_add]
  have hp : b.detDualEquiv p.primitiveGenerator r.primitiveGenerator = 1 := by
    rw [b.detDualEquiv_swap]
    omega
  obtain ⟨_, C, hrC, hpC⟩ := (hn p).mpr (Or.inl rfl)
  obtain ⟨_, D, hrD, hqD⟩ := (hn q).mpr (Or.inr rfl)
  obtain ⟨Ψ, hΨ, σ, hσ, hc', hstar, hr, -⟩ :=
    exists_star_subdivision_of_ray_eq_sum b hΦ hc ⟨hp, C, hpC, hrC⟩
      ⟨hqDet, D, hrD, hqD⟩ hsum'
  exact ⟨Ψ, hΨ, σ, hσ, hc', hstar, hr⟩

/-- A toric boundary divisor of square `-1` is the exceptional divisor of the
blowup of a distinguished point of another smooth complete toric surface. The
blowup identification matches the reduced total transform of the toric boundary. -/
theorem exists_iso_blowup_of_ray_self_intersection_neg_one
    [Φ.algebraicRealization.IsProjectiveOver ℂ]
    (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (r : Φ.Ray)
    (hself : Φ.rayBoundarySelfIntersection hΦ r = -1) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (hΨc : Ψ.IsComplete) (σ : Ψ.cones)
      (_ : Nat.card (ToricRay σ.val) = 2) (h : Φ.IsSubdivision Ψ)
      (e : Φ.algebraicRealization ≅ (Ψ.distinguishedPointHom σ).ker.blowup),
      e.hom ≫ (Ψ.distinguishedPointHom σ).ker.blowupToBase = h.toFanHom.algebraicMap ∧
      (((Ψ.distinguishedPointHom σ).ker).comap
        (Ψ.distinguishedPointHom σ).ker.blowupToBase).comap e.hom = Φ.rayBoundaryIdeal hΦ r ∧
      (((Ψ.boundaryIdeal hΨc.nonempty_cones).comap
        (Ψ.distinguishedPointHom σ).ker.blowupToBase).radical).comap e.hom =
          Φ.boundaryIdeal hc.nonempty_cones := by
  obtain ⟨Ψ, hΨ, σ, hσ, hΨc, h, hr⟩ :=
    exists_star_subdivision_of_ray_self_intersection_neg_one b hΦ hc r hself
  subst Φ
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  obtain ⟨h₀, e, -, he, -⟩ := exists_iso_blowup_starSubdivisionAlong hΨ σ hN hσ
  let hsub := Ψ.starSubdivisionAlong_isSubdivision hΨ σ.property h₀
  have hr' : Ψ.starSubdivisionAlongRay hΨ σ.property h₀ = r := Subtype.ext (Subtype.ext hr)
  refine ⟨Ψ, hΨ, hΨc, σ, hσ, hsub, e, he, ?_,
    hsub.radical_comap_boundaryIdeal_of_iso hc.nonempty_cones hΨc.nonempty_cones _ e he⟩
  rw [← Scheme.IdealSheafData.comap_comp, he, ← hr']
  exact comap_ker_distinguishedPointHom_eq_rayBoundaryIdeal hΨ σ h₀ hN hσ

end TauCeti.Toric.Fan
