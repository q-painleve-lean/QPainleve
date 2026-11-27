/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.StarSubdivision.TwoDimensional

import Mathlib.Data.Set.Card
import QPainleve.Geometry.Toric.Cone.Coordinates
import QPainleve.Geometry.Toric.Fan.Adjacency
import QPainleve.Geometry.Toric.Fan.TwoDimensional
import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Factorization of subdivisions of regular surface fans

If a regular two-dimensional cone has been subdivided nontrivially into regular
cones, the subdividing fan contains the ray through the sum of its primitive
generators. Inserting that ray gives an intermediate regular fan and decreases
the number of cones of the final fan that are still missing. This gives a
factorization by star subdivisions at two-dimensional cones. See Cox, Little,
and Schenck, *Toric Varieties*, §10.4 for the surface blowup description in
terms of inserting the sum of two neighbouring primitive generators.
-/

public section

open Module PointedCone

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

namespace Fan

variable {Φ Ψ : Fan i}

private theorem eq_bot_of_no_toricRays {σ : PointedCone ℝ V} (hσ : IsToricCone i σ)
    (hi : IsIntegralLattice i) [IsEmpty (ToricRay σ)] : σ = ⊥ := by
  rw [← hσ.hull_primitiveGenerator hi]
  simp

private theorem IsSubdivision.mem_of_card_toricRay_le_one (h : Ψ.IsSubdivision Φ)
    (σ : Φ.cones) (hc : Nat.card (ToricRay σ.val) ≤ 1) : σ.val ∈ Ψ.cones := by
  let hσ := Φ.isToricCone σ.property
  have := ToricRay.finite_of_fg hσ.fg
  rcases isEmpty_or_nonempty (ToricRay σ.val) with hempty | hne
  · have he := eq_bot_of_no_toricRays hσ Φ.lattice
    obtain ⟨τ, hτ, -, -⟩ := h.exists_mem_cone σ.property (zero_mem σ.val)
    exact he ▸ Ψ.mem_of_isFaceOf hτ ((Ψ.isToricCone hτ).salient.bot_isFaceOf)
  · let := hne
    obtain ⟨ρ⟩ := hne
    have : Subsingleton (ToricRay σ.val) := Finite.card_le_one_iff_subsingleton.mp hc
    let v := primitiveGenerator Φ.lattice hσ ρ
    have hgen : σ.val = hull ℝ {i v} := by
      rw [← hσ.hull_primitiveGenerator Φ.lattice]
      congr 1
      rw [← Set.range_comp]
      exact Set.range_eq_singleton (fun r ↦ congrArg _ (Subsingleton.elim r ρ))
    have hv : i v ∈ σ.val := ρ.val.isFaceOf.le (primitiveGenerator_mem Φ.lattice hσ ρ)
    obtain ⟨τ, hτ, hle, hmem⟩ := h.exists_mem_cone σ.property hv
    exact (hle.antisymm (hgen ▸ (Submodule.span_singleton_le_iff_mem _ _).mpr hmem)) ▸ hτ

private theorem sum_basis_ne_zero (b : Basis (Fin 2) ℤ N) : b 0 + b 1 ≠ 0 := by
  intro h
  have h' := congrArg (b.coord 0) h
  simp [Basis.coord_apply] at h'

private theorem basis_repr_nonneg_of_mem {b : Basis (Fin 2) ℤ N}
    (hi : IsIntegralLattice i) {x : N} (hx : i x ∈ hull ℝ (i '' Set.range b)) (j : Fin 2) :
    0 ≤ b.repr x j := by
  have hchar : (b.coord j).toAddMonoidHom ∈ dualSemigroup hi (hull ℝ (i '' Set.range b)) := by
    rw [mem_dualSemigroup_hull_image, Set.forall_mem_range]
    intro k
    simp only [LinearMap.toAddMonoidHom_coe, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_apply]
    split <;> omega
  have h := (mem_dualSemigroup hi _).mp hchar hx
  rw [IsIntegralLattice.realCharacter_apply] at h
  exact_mod_cast h

private theorem eq_basis_of_repr_sum_eq_one (b : Basis (Fin 2) ℤ N) {x : N}
    (h : ∀ j, 0 ≤ b.repr x j) (hsum : b.repr x 0 + b.repr x 1 = 1) :
    x = b 0 ∨ x = b 1 := by
  have he : b.repr x 0 = 1 ∧ b.repr x 1 = 0 ∨ b.repr x 0 = 0 ∧ b.repr x 1 = 1 := by
    have := h 0
    have := h 1
    omega
  rcases he with h | h
  · left
    apply b.repr.injective
    ext j
    fin_cases j <;> simp [h]
  · right
    apply b.repr.injective
    ext j
    fin_cases j <;> simp [h]

private theorem eq_hull_sum_of_single_coord
    {σ : PointedCone ℝ V} (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    {c : Basis (Fin 2) ℤ N} {r : ToricRay σ ↪ Fin 2} (hc : IsExtendingBasis i c r)
    {x : N} (hx : x ≠ 0) {j : Fin 2} (hpos : 0 < c.repr x j)
    (hr : j ∈ Set.range r) (he : x = c.repr x j • c j) :
    ∃ ρ : ToricRay σ, ρ.toPointedCone = hull ℝ {i x} := by
  obtain ⟨ρ, rfl⟩ := hr
  refine ⟨ρ, ρ.eq_hull_singleton (hσ.salient.anti ρ.val.isFaceOf.le) ?_
    (by simpa using hi.injective.ne hx)⟩
  rw [he, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ]
  exact ρ.toPointedCone.smul_mem (by exact_mod_cast hpos.le)
    (hc.isPrimitiveGenerator_apply ρ).mem

private theorem eq_cone_of_two_pos_coords
    {σ : PointedCone ℝ V} (hi : IsIntegralLattice i)
    (b c : Basis (Fin 2) ℤ N)
    (hm : ∀ j, i (c j) ∈ σ) (hle : σ ≤ hull ℝ (i '' Set.range b))
    (a d : ℤ) (ha : 0 < a) (hd : 0 < d) (he : a • c 0 + d • c 1 = b 0 + b 1) :
    σ = hull ℝ (i '' Set.range b) := by
  let w := b.coord 0 + b.coord 1
  have hw (y : N) : w y = b.repr y 0 + b.repr y 1 := rfl
  have hnonneg (j k : Fin 2) := basis_repr_nonneg_of_mem hi (hle (hm j)) k
  have hp (j : Fin 2) : 1 ≤ w (c j) := by
    have h0 := hnonneg j 0
    have h1 := hnonneg j 1
    by_contra! h
    rw [hw] at h
    have hz : c j = 0 := by
      apply b.repr.injective
      ext k
      have hz₀ : b.repr (c j) 0 = 0 := by omega
      have hz₁ : b.repr (c j) 1 = 0 := by omega
      fin_cases k <;> simpa using ‹_›
    exact c.linearIndependent.ne_zero j hz
  have hweight : a * w (c 0) + d * w (c 1) = 2 := by
    have h := congrArg w he
    simp only [map_add, map_smul, smul_eq_mul] at h
    have htwo : w (b 0) + w (b 1) = 2 := by simp [hw]
    exact h.trans htwo
  have hnonnegWeight (j : Fin 2) : 0 ≤ w (c j) := zero_le_one.trans (hp j)
  have h0 := mul_le_mul_of_nonneg_right (show 1 ≤ a by omega) (hnonnegWeight 0)
  have h1 := mul_le_mul_of_nonneg_right (show 1 ≤ d by omega) (hnonnegWeight 1)
  have hsum (j : Fin 2) : b.repr (c j) 0 + b.repr (c j) 1 = 1 := by
    have h0p := hp 0
    have h1p := hp 1
    have hw0 : w (c 0) = 1 := by omega
    have hw1 : w (c 1) = 1 := by omega
    fin_cases j
    · exact (hw _).symm.trans hw0
    · exact (hw _).symm.trans hw1
  have hmem (k : Fin 2) : i (b k) ∈ σ := by
    obtain h | h := eq_basis_of_repr_sum_eq_one b (hnonneg 0) (hsum 0)
    · have hh : c 1 = b 1 := (eq_basis_of_repr_sum_eq_one b (hnonneg 1) (hsum 1)).resolve_left
        (fun h' ↦ (by decide : (0 : Fin 2) ≠ 1) (c.injective (h.trans h'.symm)))
      fin_cases k
      · exact h ▸ hm 0
      · exact hh ▸ hm 1
    · have hh : c 1 = b 0 := (eq_basis_of_repr_sum_eq_one b (hnonneg 1) (hsum 1)).resolve_right
        (fun h' ↦ (by decide : (0 : Fin 2) ≠ 1) (c.injective (h.trans h'.symm)))
      fin_cases k
      · exact hh ▸ hm 1
      · exact h ▸ hm 0
  exact hle.antisymm (Submodule.span_le.mpr (by rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩; exact hmem j))

private theorem exists_ray_or_eq_of_basis_sum_mem
    {σ : PointedCone ℝ V} (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ)
    (b : Basis (Fin 2) ℤ N) (hle : σ ≤ hull ℝ (i '' Set.range b))
    (hx : i (b 0 + b 1) ∈ σ) :
    (∃ ρ : ToricRay σ, ρ.toPointedCone = hull ℝ {i (b 0 + b 1)}) ∨
      σ = hull ℝ (i '' Set.range b) := by
  let x := b 0 + b 1
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  obtain ⟨c, r, hc⟩ := hN ▸ hσ.exists_basis_finrank
  have hcoef := (hc.mem_iff_lattice_basis_repr hi hσ.toIsToricCone x).mp hx
  have he : c.repr x 0 • c 0 + c.repr x 1 • c 1 = x := by
    simpa only [Fin.sum_univ_two] using c.sum_repr x
  have hr (j : Fin 2) (hj : 0 < c.repr x j) : j ∈ Set.range r :=
    not_not.mp (fun hn ↦ (ne_of_gt hj) ((hcoef j).2 hn))
  have hmem (j : Fin 2) (hj : 0 < c.repr x j) : i (c j) ∈ σ := by
    obtain ⟨ρ, rfl⟩ := hr j hj
    exact ρ.val.isFaceOf.le (hc.isPrimitiveGenerator_apply ρ).mem
  by_cases h0 : c.repr x 0 = 0
  · have he' : x = c.repr x 1 • c 1 := by simpa [h0] using he.symm
    have h1 : 0 < c.repr x 1 := lt_of_le_of_ne (hcoef 1).1 (by
      intro hz
      exact sum_basis_ne_zero b (by simpa [hz.symm] using he'))
    exact Or.inl (eq_hull_sum_of_single_coord hi hσ.toIsToricCone hc (sum_basis_ne_zero b)
      h1 (hr 1 h1) he')
  · have hp0 := lt_of_le_of_ne (hcoef 0).1 (Ne.symm h0)
    by_cases h1 : c.repr x 1 = 0
    · have he' : x = c.repr x 0 • c 0 := by simpa [h1] using he.symm
      exact Or.inl (eq_hull_sum_of_single_coord hi hσ.toIsToricCone hc (sum_basis_ne_zero b)
        hp0 (hr 0 hp0) he')
    · have hp1 := lt_of_le_of_ne (hcoef 1).1 (Ne.symm h1)
      refine Or.inr (eq_cone_of_two_pos_coords hi b c ?_ hle _ _ hp0 hp1 he)
      intro j
      fin_cases j
      · exact hmem 0 hp0
      · exact hmem 1 hp1

-- Only the chosen maximal cone can be removed. It was already absent from the
-- final fan, and the inserted ray is a new common cone.
private theorem sdiff_starSubdivisionAlong_ssubset (hΦ : Φ.IsRegular)
    (hN : Module.finrank ℤ N = 2) (σ : Φ.cones) (hmissing : σ.val ∉ Ψ.cones)
    (hc : Nat.card (ToricRay σ.val) = 2) (ray : PointedCone ℝ V)
    (hrayΨ : ray ∈ Ψ.cones) (hrayΦ : ray ∉ Φ.cones)
    (hrayS : ray ∈ (Φ.starSubdivisionAlong hΦ σ.property).cones) :
    (Ψ.cones \ (Φ.starSubdivisionAlong hΦ σ.property).cones) ⊂ (Ψ.cones \ Φ.cones) := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · rintro κ ⟨hκ, hκS⟩
    refine ⟨hκ, fun hκΦ ↦ hκS (Φ.mem_starSubdivisionAlong_cones_of_not_le hΦ σ.property
      hκΦ ?_)⟩
    intro hs
    have he : σ.val = κ := congrArg Subtype.val
      (eq_of_le_fullCone hΦ hN hc (τ := ⟨κ, hκΦ⟩) hs)
    exact hmissing (he.symm ▸ hκ)
  · intro he
    have hm : ray ∈ Ψ.cones \ Φ.cones := ⟨hrayΨ, hrayΦ⟩
    rw [← he] at hm
    exact hm.2 hrayS

private theorem IsSubdivision.hull_sum_mem_of_notMem (h : Ψ.IsSubdivision Φ)
    (hΨ : Ψ.IsRegular) (σ : Φ.cones) (hmissing : σ.val ∉ Ψ.cones)
    (b : Basis (Fin 2) ℤ N) (hcone : hull ℝ (i '' Set.range b) = σ.val)
    (hx : i (b 0 + b 1) ∈ σ.val) :
    hull ℝ {i (b 0 + b 1)} ∈ Ψ.cones := by
  obtain ⟨τ, hτ, hle, hmem⟩ := h.exists_mem_cone σ.property hx
  rcases exists_ray_or_eq_of_basis_sum_mem Φ.lattice ((isRegular_iff.1 hΨ) _ hτ) b
      (hcone.symm ▸ hle) hmem with ⟨ρ, hρ⟩ | he
  · have hr : ρ.toPointedCone ∈ Ψ.cones := Ψ.mem_of_isFaceOf hτ ρ.val.isFaceOf
    rwa [hρ] at hr
  · exact (hmissing ((he.trans hcone) ▸ hτ)).elim

private theorem IsSubdivision.exists_starSubdivisionAlong (h : Ψ.IsSubdivision Φ)
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hN : Module.finrank ℤ N = 2)
    (σ : Φ.cones) (hmissing : σ.val ∉ Ψ.cones) (hc : Nat.card (ToricRay σ.val) = 2) :
    Ψ.IsSubdivision (Φ.starSubdivisionAlong hΦ σ.property) ∧
      (Ψ.cones \ (Φ.starSubdivisionAlong hΦ σ.property).cones) ⊂ (Ψ.cones \ Φ.cones) := by
  let hσ := (isRegular_iff.1 hΦ) _ σ.property
  obtain ⟨e, b, hb⟩ := hσ.exists_basis_primitiveGenerators Φ.lattice hN hc
  let u := b 0 + b 1
  let ray := hull ℝ {i u}
  let c := Φ.lattice.isBaseChange.basis b
  have hcv (j : Fin 2) : c j = i (b j) := Φ.lattice.isBaseChange.basis_apply b j
  have hcone' := hσ.hull_eq_of_basis_primitiveGenerators Φ.lattice b e hb
  have hcone : hull ℝ (Set.range c) = σ.val := by
    rw [show (c : Fin 2 → V) = i ∘ b by funext j; exact hcv j, Set.range_comp, hcone']
  have hray : ray = hull ℝ {c 0 + c 1} := by simp [ray, u, hcv]
  have hx : i u ∈ σ.val := by
    have hu : i u = c 0 + c 1 := by simp [u, hcv]
    rw [hu, ← hcone]
    exact add_mem (subset_hull (Set.mem_range_self 0)) (subset_hull (Set.mem_range_self 1))
  have hrayΨ : ray ∈ Ψ.cones := h.hull_sum_mem_of_notMem hΨ σ hmissing b hcone' hx
  have hσ₀ := ne_bot_of_card_toricRay_eq_two hc
  let S := Φ.starSubdivisionAlong hΦ σ.property
  have hstar := Φ.starSubdivisionAlong_isSubdivision hΦ σ.property hσ₀
  have hsum := hσ.sum_primitiveGenerator_allRays Φ.lattice b e hb
  have hstarRay : (Φ.starSubdivisionAlongRay hΦ σ.property hσ₀).toCone.val = ray := by
    rw [coe_toCone_starSubdivisionAlongRay, hsum]
  have hrayS : ray ∈ S.cones := hstarRay ▸
    (Φ.starSubdivisionAlongRay hΦ σ.property hσ₀).toCone.property
  have hrayΦ : ray ∉ Φ.cones := by
    intro hr
    have hf := Φ.inf_isFaceOf_left σ.property hr
    have hx' : i u ∈ σ.val ⊓ ray := ⟨hx, subset_hull (Set.mem_singleton _)⟩
    have hl := (Φ.isToricCone σ.property).le_of_isFaceOf_of_sum_primitiveGenerator_mem
      Φ.lattice hf (hsum.symm ▸ hx')
    have he := (c.mem_hull_sum_iff (subset_hull (Set.mem_range_self 0))).mp
      (hray ▸ (hl (hcone ▸ subset_hull (Set.mem_range_self 0))).2)
    simp [Basis.coord_apply] at he
  refine ⟨⟨?_, h.support_eq.trans hstar.support_eq.symm⟩,
    sdiff_starSubdivisionAlong_ssubset hΦ hN σ hmissing hc ray hrayΨ hrayΦ hrayS⟩
  intro κ hκ
  obtain ⟨η, hη, hκη⟩ := h.exists_cone_le hκ
  by_cases he : η = σ.val
  · subst η
    have hf := Ψ.inf_isFaceOf_left hκ hrayΨ
    rw [hray] at hf
    obtain ⟨j, hj⟩ := c.exists_le_hull_sum_pair_of_isFaceOf (hcone ▸ hκη) hf
    refine ⟨hull ℝ {i u, i (b j)}, mem_starSubdivisionAlong_hull_sum_pair hΦ σ b e hb j, ?_⟩
    simpa only [hcv, ← map_add] using hj
  · have hnot : ¬ σ.val ≤ η := fun hle' ↦ he
      (congrArg Subtype.val (eq_of_le_fullCone hΦ hN hc (τ := ⟨η, hη⟩) hle')).symm
    exact ⟨η, Φ.mem_starSubdivisionAlong_cones_of_not_le hΦ σ.property hη hnot, hκη⟩

/-- A single star subdivision at a two-ray cone of a regular fan.
The first fan is the input and the second fan is the subdivision. -/
inductive IsTwoRayStarSubdivision : Fan i → Fan i → Prop
  /-- Subdivide a regular fan along the sum of the two primitive ray generators of a cone. -/
  | along {Φ : Fan i} (hΦ : Φ.IsRegular) (σ : Φ.cones) (hc : Nat.card (ToricRay σ.val) = 2) :
      IsTwoRayStarSubdivision Φ (Φ.starSubdivisionAlong hΦ σ.property)

/-- Each two-ray star subdivision is an instance of the native subdivision relation. -/
theorem IsTwoRayStarSubdivision.isSubdivision (h : Φ.IsTwoRayStarSubdivision Ψ) :
    Ψ.IsSubdivision Φ := by
  obtain ⟨hΦ, σ, hc⟩ := h
  exact Φ.starSubdivisionAlong_isSubdivision hΦ σ.property (ne_bot_of_card_toricRay_eq_two hc)

/-- A chain of two-ray star subdivisions gives a subdivision of the initial fan. -/
theorem isSubdivision_of_starSubdivision_chain
    (h : Relation.ReflTransGen IsTwoRayStarSubdivision Φ Ψ) : Ψ.IsSubdivision Φ := by
  induction h with
  | refl => exact IsSubdivision.refl _
  | tail _ hstep ih => exact hstep.isSubdivision.trans ih

/-- A subdivision between regular fans in a rank-two lattice factors by star subdivisions at
two-dimensional cones. This holds for noncomplete fans with any common support. -/
theorem IsSubdivision.exists_starSubdivision_factorization (h : Ψ.IsSubdivision Φ)
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hN : Module.finrank ℤ N = 2) :
    Relation.ReflTransGen IsTwoRayStarSubdivision Φ Ψ := by
  classical
  induction hn : (Ψ.cones \ Φ.cones).ncard using Nat.strong_induction_on generalizing Φ with
  | ind n ih =>
    by_cases hle : Φ.cones ⊆ Ψ.cones
    · have he : Φ = Ψ := Fan.ext (Set.Subset.antisymm hle fun τ hτ ↦ by
        obtain ⟨σ, hσ, hτσ⟩ := h.exists_cone_le hτ
        exact Φ.mem_of_isFaceOf hσ (Ψ.isFaceOf_of_le (hle hσ) hτ hτσ))
      exact he ▸ .refl
    · obtain ⟨σ, hσ, hmissing⟩ := Set.not_subset.mp hle
      have hc : Nat.card (ToricRay σ) = 2 := by
        have hmax := ((isRegular_iff.1 hΦ) σ hσ).card_toricRay_le_finrank
        have hmin : ¬ Nat.card (ToricRay σ) ≤ 1 := fun hc ↦
          hmissing (h.mem_of_card_toricRay_le_one ⟨σ, hσ⟩ hc)
        omega
      obtain ⟨hs, hlt⟩ := h.exists_starSubdivisionAlong hΦ hΨ hN ⟨σ, hσ⟩ hmissing hc
      have hsm := Φ.isRegular_starSubdivisionAlong hΦ hσ
      have hcard := Set.ncard_lt_ncard hlt (Ψ.finite_cones.sdiff)
      exact (ih _ (hcard.trans_le hn.le) hs hsm rfl).head (.along hΦ ⟨σ, hσ⟩ hc)

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

end Fan

end TauCeti.Toric
