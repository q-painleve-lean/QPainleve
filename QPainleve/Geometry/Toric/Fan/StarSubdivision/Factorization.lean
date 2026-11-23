/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.StarSubdivision.TwoDimensional

import Mathlib.Data.Set.Card
import QPainleve.Geometry.Toric.Cone.Coordinates

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

private theorem mem_basisHull_iff (b : Basis (Fin 2) ℝ V) {x : V} :
    x ∈ hull ℝ (Set.range b) ↔ 0 ≤ b.coord 0 x ∧ 0 ≤ b.coord 1 x := by
  have hset : Set.range b = {b 0, b 1} := by
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff,
      Fin.exists_fin_two, eq_comm]
  rw [hset, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, d, rfl⟩
    simpa [← Nonneg.coe_smul, Basis.coord_apply] using And.intro a.property d.property
  · rintro ⟨h0, h1⟩
    refine ⟨⟨_, h0⟩, ⟨_, h1⟩, ?_⟩
    simpa only [Nonneg.mk_smul, Fin.sum_univ_two, Basis.coord_apply] using b.sum_repr x

private theorem mem_hull_sum_iff (b : Basis (Fin 2) ℝ V) {x : V}
    (hx : x ∈ hull ℝ (Set.range b)) :
    x ∈ hull ℝ {b 0 + b 1} ↔ (b.coord 0 - b.coord 1) x = 0 := by
  rw [mem_hull_singleton]
  constructor
  · rintro ⟨t, -, rfl⟩
    simp [Basis.coord_apply]
  · intro he
    refine ⟨b.coord 0 x, ((mem_basisHull_iff b).mp hx).1, ?_⟩
    have he' : b.coord 0 x = b.coord 1 x := sub_eq_zero.mp he
    rw [smul_add]
    nth_rw 2 [he']
    simpa only [Fin.sum_univ_two, Basis.coord_apply] using b.sum_repr x

private theorem mem_hull_sum_pair_of_coord_le (b : Basis (Fin 2) ℝ V) {x : V}
    (hx : x ∈ hull ℝ (Set.range b)) {j k : Fin 2} (hjk : j ≠ k)
    (h : b.coord k x ≤ b.coord j x) :
    x ∈ hull ℝ {b 0 + b 1, b j} := by
  have hpos (l : Fin 2) : 0 ≤ b.coord l x := by
    have hp := (mem_basisHull_iff b).mp hx
    fin_cases l
    · exact hp.1
    · exact hp.2
  rw [Submodule.mem_span_pair]
  refine ⟨⟨_, hpos k⟩, ⟨_, sub_nonneg.mpr h⟩, ?_⟩
  have he := b.sum_repr x
  simp only [Fin.sum_univ_two, ← Basis.coord_apply] at he
  simp only [Nonneg.mk_smul, smul_add, sub_smul]
  have hsum : (b.coord k x) • b 0 + (b.coord k x) • b 1 +
      ((b.coord j x) • b j - (b.coord k x) • b j) =
      (b.coord 0 x) • b 0 + (b.coord 1 x) • b 1 := by
    have hcases : j = 0 ∧ k = 1 ∨ j = 1 ∧ k = 0 := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> module
  exact hsum.trans he

private theorem exists_le_hull_sum_pair_of_isFaceOf (b : Basis (Fin 2) ℝ V)
    {τ : PointedCone ℝ V} (hτ : τ ≤ hull ℝ (Set.range b))
    (hface : (τ ⊓ hull ℝ {b 0 + b 1}).IsFaceOf τ) :
    ∃ j : Fin 2, τ ≤ hull ℝ {b 0 + b 1, b j} := by
  let f := b.coord 0 - b.coord 1
  by_cases hp : ∃ x ∈ τ, 0 < f x
  · obtain ⟨x, hx, hpos⟩ := hp
    refine ⟨0, fun y hy ↦ mem_hull_sum_pair_of_coord_le b (hτ hy)
      (by decide : (0 : Fin 2) ≠ 1) (sub_nonneg.mp ?_)⟩
    by_contra! hneg
    have hneg' : f y < 0 := hneg
    have h1 := τ.smul_mem (neg_nonneg.mpr hneg'.le) hx
    have h2 := τ.smul_mem hpos.le hy
    have hz : f ((-f y) • x + f x • y) = 0 := by
      simp only [map_add, map_smul, smul_eq_mul]
      ring
    have hm := (mem_hull_sum_iff b (hτ (τ.add_mem h1 h2))).mpr hz
    have hxf := hface.mem_of_add_mem_left h1 h2 ⟨τ.add_mem h1 h2, hm⟩
    have he := (mem_hull_sum_iff b (hτ h1)).mp hxf.2
    have hz' : 0 < f ((-f y) • x) := by
      rw [map_smul, smul_eq_mul]
      exact mul_pos (neg_pos.mpr hneg') hpos
    exact hz'.ne' he
  · push Not at hp
    refine ⟨1, fun y hy ↦ mem_hull_sum_pair_of_coord_le b (hτ hy)
      (by decide : (1 : Fin 2) ≠ 0) (sub_nonpos.mp (hp y hy))⟩

private theorem mem_starSubdivisionAlong_hull_sum_pair (hΦ : Φ.IsRegular)
    (σ : Φ.cones) (b : Basis (Fin 2) ℤ N) (e : Fin 2 ≃ ToricRay σ.val)
    (hb : ∀ j, b j = primitiveGenerator Φ.lattice (Φ.isToricCone σ.property) (e j))
    (j : Fin 2) :
    hull ℝ {i (b 0 + b 1), i (b j)} ∈ (Φ.starSubdivisionAlong hΦ σ.property).cones := by
  let hσ := (isRegular_iff.1 hΦ) _ σ.property
  have hmem := hσ.starSubdivisionCone_pair_mem Φ.lattice e j
  dsimp only at hmem
  rw [hσ.starSubdivisionCone_pair_eq_hull Φ.lattice b e hb] at hmem
  exact (Φ.mem_starSubdivisionAlong_cones hΦ σ.property).mpr
    (.inr ⟨σ.val, σ.property, le_rfl, hmem⟩)

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
    have he := (mem_hull_sum_iff c (subset_hull (Set.mem_range_self 0))).mp
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
    obtain ⟨j, hj⟩ := exists_le_hull_sum_pair_of_isFaceOf c (hcone ▸ hκη) hf
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

end Fan

end TauCeti.Toric
