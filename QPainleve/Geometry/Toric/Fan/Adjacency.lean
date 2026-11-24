/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.DeterminantCharacters
public import QPainleve.Geometry.Toric.Fan.Ray
public import TauCeti.Geometry.Toric.Algebraic.Regular

import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.Real.Lemmas
import QPainleve.Geometry.Toric.Cone.Coordinates

/-!
# Neighbouring rays in a complete regular fan

In rank two, each ray of a complete regular fan has one neighbouring ray on each
side of its line. The primitive generators of a pair of neighbours form an integral
basis. Here neighbours are distinct fan rays sharing a cone, as in Fulton's
*Introduction to Toric Varieties*, §2.5.
-/

public section

open PointedCone

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

/-- Two distinct rays sharing a cone of a regular rank-two fan have primitive generators
which, in the given order, form an integral basis. -/
theorem exists_basis_of_ray_ne_of_le {ρ τ : Φ.Ray} {σ : Φ.cones}
    (hσ : IsRegularCone i σ.val) (hN : Module.finrank ℤ N = 2)
    (hne : ρ ≠ τ) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ) :
    ∃ c : Module.Basis (Fin 2) ℤ N, c 0 = ρ.primitiveGenerator ∧ c 1 = τ.primitiveGenerator := by
  obtain ⟨c, r, hc⟩ := hN ▸ hσ.exists_basis_finrank
  let u : Fin 2 → Fin 2 := ![r (ρ.toToricRay Φ σ hρ), r (τ.toToricRay Φ σ hτ)]
  have hne' : u 0 ≠ u 1 := by
    intro h
    have he : Φ.rayEquiv σ ⟨ρ, hρ⟩ = Φ.rayEquiv σ ⟨τ, hτ⟩ := by
      simpa only [rayEquiv_apply] using r.injective h
    exact hne (congrArg Subtype.val ((Φ.rayEquiv σ).injective he))
  have hu : Function.Injective u := Matrix.injective_pair_iff_ne.mpr hne'
  let e := Equiv.ofBijective u (Finite.injective_iff_bijective.mp hu)
  refine ⟨c.reindex e.symm, ?_, ?_⟩
  · simpa [e, u] using
      (hc.isPrimitiveGenerator_apply (ρ.toToricRay Φ σ hρ)).eq_primitiveGenerator
        Φ.lattice (Φ.isToricCone σ.property)
  · simpa [e, u] using
      (hc.isPrimitiveGenerator_apply (τ.toToricRay Φ σ hτ)).eq_primitiveGenerator
        Φ.lattice (Φ.isToricCone σ.property)

/-- Adjacent primitive generators have determinant a unit in any integral basis. -/
theorem isUnit_det_of_ray_ne_of_le (b : Module.Basis (Fin 2) ℤ N)
    {ρ τ : Φ.Ray} {σ : Φ.cones} (hσ : IsRegularCone i σ.val)
    (hne : ρ ≠ τ) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ) :
    IsUnit (b.detDualEquiv ρ.primitiveGenerator τ.primitiveGenerator) := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_basis_of_ray_ne_of_le hσ
    (by simpa using Module.finrank_eq_card_basis b) hne hρ hτ
  have hc : (c : Fin 2 → N) = ![ρ.primitiveGenerator, τ.primitiveGenerator] := by
    funext j
    fin_cases j <;> assumption
  rw [Module.Basis.detDualEquiv_apply, ← hc]
  exact b.isUnit_det c

/-- A two-ray cone of a regular rank-two fan contains an ordered pair of rays whose
primitive generators have determinant one in the chosen lattice basis. -/
theorem exists_ray_pair_le_det_eq_one (b : Module.Basis (Fin 2) ℤ N)
    {σ : Φ.cones} (hσ : IsRegularCone i σ.val) (hcard : Nat.card (ToricRay σ.val) = 2) :
    ∃ ρ τ : Φ.Ray, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ ∧
      b.detDualEquiv ρ.primitiveGenerator τ.primitiveGenerator = 1 := by
  have : Finite (ToricRay σ.val) := ToricRay.finite_of_fg (Φ.isToricCone σ.property).fg
  let := Fintype.ofFinite (ToricRay σ.val)
  let e := (Fintype.equivFinOfCardEq ((Nat.card_eq_fintype_card).symm.trans hcard)).symm.trans
    (Φ.rayEquiv σ).symm
  let ρ : Φ.Ray := (e 0).val
  let τ : Φ.Ray := (e 1).val
  have hρθ : ρ ≠ τ := fun h ↦ zero_ne_one (e.injective (Subtype.ext h))
  rcases Int.isUnit_iff.mp
    (isUnit_det_of_ray_ne_of_le b hσ hρθ (e 0).property (e 1).property) with hd | hd
  · exact ⟨ρ, τ, (e 0).property, (e 1).property, hd⟩
  · exact ⟨τ, ρ, (e 1).property, (e 0).property, by rw [b.detDualEquiv_swap, hd, neg_neg]⟩

/-- Two distinct fan rays in a regular cone of a rank-two lattice exhaust its toric rays. -/
theorem toricRays_eq_pair (Φ : Fan i) {ρ τ : Φ.Ray} {σ : Φ.cones}
    (hσ : IsRegularCone i σ.val) (hN : Module.finrank ℤ N = 2)
    (hne : ρ ≠ τ) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ) :
    ({ρ.toToricRay Φ σ hρ, τ.toToricRay Φ σ hτ} : Set (ToricRay σ.val)) = Set.univ := by
  have hr : ρ.toToricRay Φ σ hρ ≠ τ.toToricRay Φ σ hτ := by
    intro h
    have he : Φ.rayEquiv σ ⟨ρ, hρ⟩ = Φ.rayEquiv σ ⟨τ, hτ⟩ := by
      simpa only [rayEquiv_apply] using h
    exact hne (congrArg Subtype.val ((Φ.rayEquiv σ).injective he))
  have hcard := hσ.card_toricRay_le_finrank.trans_eq hN
  have : Finite (ToricRay σ.val) := ToricRay.finite_of_fg (Φ.isToricCone σ.property).fg
  apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
  rwa [Set.ncard_univ, Set.ncard_pair hr]

/-- In rank two, a ray lying in a regular cone with two known distinct rays is
one of those two rays. -/
theorem ray_eq_or_eq_of_le {σ : Φ.cones} (hσ : IsRegularCone i σ.val)
    (hN : Module.finrank ℤ N = 2) {p q r : Φ.Ray} (hne : p ≠ q)
    (hp : p.toCone ≤ σ) (hq : q.toCone ≤ σ) (hr : r.toCone ≤ σ) :
    r = p ∨ r = q := by
  let e := Φ.rayEquiv σ
  have h := Φ.toricRays_eq_pair hσ hN hne hp hq
  have hm : e ⟨r, hr⟩ ∈ ({e ⟨p, hp⟩, e ⟨q, hq⟩} : Set _) := by
    simp only [e, rayEquiv_apply, h, Set.mem_univ]
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, e.injective.eq_iff,
    Subtype.mk.injEq] using hm

/-- A cone of a regular rank-two fan containing two distinct rays has exactly two rays. -/
theorem card_toricRay_eq_two_of_ray_ne_of_le (Φ : Fan i)
    (hΦ : Φ.IsRegular) (hdim : Module.finrank ℤ N = 2)
    {ρ τ : Φ.Ray} {σ : Φ.cones} (hne : ρ ≠ τ)
    (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ) : Nat.card (ToricRay σ.val) = 2 := by
  have hpair := Φ.toricRays_eq_pair ((isRegular_iff.mp hΦ) _ σ.property) hdim hne hρ hτ
  have hne' : ρ.toToricRay Φ σ hρ ≠ τ.toToricRay Φ σ hτ := by
    intro h
    have he : Φ.rayEquiv σ ⟨ρ, hρ⟩ = Φ.rayEquiv σ ⟨τ, hτ⟩ := by
      simpa only [rayEquiv_apply] using h
    exact hne (congrArg Subtype.val ((Φ.rayEquiv σ).injective he))
  rw [← Set.ncard_univ, ← hpair, Set.ncard_pair hne']

/-- A cone of a regular rank-two fan containing two distinct rays is their join. -/
theorem cone_eq_sup_of_ray_ne_of_le (hΦ : Φ.IsRegular) (hN : Module.finrank ℤ N = 2)
    {ρ τ : Φ.Ray} {σ : Φ.cones} (hne : ρ ≠ τ) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ) :
    σ.val = ρ.toCone.val ⊔ τ.toCone.val := by
  refine le_antisymm ?_ (sup_le hρ hτ)
  rw [← ToricRay.iSup_toPointedCone (Φ.isToricCone σ.property).fg
    (Φ.isToricCone σ.property).salient]
  refine iSup_le fun r ↦ ?_
  have hr : r ∈ ({ρ.toToricRay Φ σ hρ, τ.toToricRay Φ σ hτ} : Set (ToricRay σ.val)) :=
    Φ.toricRays_eq_pair ((isRegular_iff.1 hΦ) _ σ.property) hN hne hρ hτ ▸ Set.mem_univ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl
  · rw [Ray.toPointedCone_toToricRay]
    exact le_sup_left
  · rw [Ray.toPointedCone_toToricRay]
    exact le_sup_right

/-- The preimage of a regular fan cone is closed if every real linear coordinate is
continuous along the map. The ambient real vector space needs no topology. -/
theorem isClosed_preimage_cone_of_isRegular {T : Type*} [TopologicalSpace T]
    (hΦ : Φ.IsRegular) (σ : Φ.cones) (f : T → V)
    (hf : ∀ l : V →ₗ[ℝ] ℝ, Continuous (l ∘ f)) :
    IsClosed (f ⁻¹' (σ.val : Set V)) := by
  classical
  have hreg := (isRegular_iff.1 hΦ) σ.val σ.property
  obtain ⟨n, b, r, hb⟩ := hreg.exists_basis
  let c := Φ.lattice.isBaseChange.basis b
  let A := Set.range r
  have hmem (z : V) : z ∈ σ.val ↔ ∀ j, c.repr z j ∈
      if j ∈ A then Set.Ici (0 : ℝ) else {0} := by
    rw [hb.mem_iff_real_basis_repr Φ.lattice hreg.toIsToricCone]
    apply forall_congr'
    intro j
    by_cases hj : j ∈ A
    · simp [A, hj, c]
    · simp only [A, hj, not_false_eq_true, forall_const, ite_false, Set.mem_singleton_iff, c]
      exact ⟨And.right, fun h ↦ ⟨h.ge, h⟩⟩
  rw [show f ⁻¹' (σ.val : Set V) = {t | ∀ j, c.repr (f t) j ∈
      if j ∈ A then Set.Ici (0 : ℝ) else {0}} from Set.ext fun t ↦ hmem (f t)]
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun j ↦ ?_
  have hclosed : IsClosed (if j ∈ A then Set.Ici (0 : ℝ) else {0}) := by
    split_ifs
    · exact isClosed_Ici
    · exact isClosed_singleton
  exact hclosed.preimage (hf (c.coord j))

private theorem exists_cone_mem_pos (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    {f : V →ₗ[ℝ] ℝ} {x y : V} (hx : f x = 0) (hy : 0 < f y) :
    ∃ σ : Φ.cones, x ∈ σ.val ∧ ∃ z ∈ σ.val, 0 < f z := by
  let S := {σ : Φ.cones | ∃ z ∈ σ.val, 0 < f z}
  let U := ⋃ σ ∈ S, {t : ℝ | x + t • y ∈ σ.val}
  have hU : IsClosed U := S.toFinite.isClosed_biUnion fun σ _ ↦
    isClosed_preimage_cone_of_isRegular hΦ σ (fun t : ℝ ↦ x + t • y) fun l ↦ by
      rw [show (l ∘ fun t : ℝ ↦ x + t • y) = fun t ↦ l x + t * l y from
        funext fun t ↦ by simp [smul_eq_mul]]
      exact continuous_const.add (continuous_id.mul continuous_const)
  have hcover : Set.Ioi (0 : ℝ) ⊆ U := by
    intro t ht
    obtain ⟨σ, hσ, hz⟩ := Φ.isComplete_iff.1 hc (x + t • y)
    have hp : 0 < f (x + t • y) := by
      simpa [hx] using mul_pos (Set.mem_Ioi.mp ht) hy
    simp only [U, Set.mem_iUnion]
    exact ⟨⟨σ, hσ⟩, ⟨_, hz, hp⟩, hz⟩
  have hzero : (0 : ℝ) ∈ U := closure_minimal hcover hU
    (by rw [closure_Ioi]; exact le_rfl)
  simp only [U, Set.mem_iUnion] at hzero
  obtain ⟨σ, hσ, hz⟩ := hzero
  exact ⟨σ, by simpa using hz, hσ⟩

private theorem exists_pos_neighbor (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (ρ : Φ.Ray) {f : V →ₗ[ℝ] ℝ} (hf : f ≠ 0) (hρ : f (i ρ.primitiveGenerator) = 0) :
    ∃ τ : Φ.Ray, 0 < f (i τ.primitiveGenerator) ∧
      ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ := by
  obtain ⟨y, hy⟩ := LinearMap.surjective hf 1
  have hy₀ : 0 < f y := hy.symm ▸ zero_lt_one
  obtain ⟨σ, hx, z, hz, hzpos⟩ := exists_cone_mem_pos hΦ hc hρ hy₀
  have hpos : ∃ τ : ToricRay σ.val,
      0 < f (i (Toric.primitiveGenerator Φ.lattice (Φ.isToricCone σ.property) τ)) := by
    by_contra! h
    have hle : σ.val ≤ (hull ℝ {(-1 : ℝ)}).comap f := by
      refine (Φ.isToricCone σ.property).hull_primitiveGenerator Φ.lattice ▸
        Submodule.span_le.mpr ?_
      rintro _ ⟨_, ⟨τ, rfl⟩, rfl⟩
      exact mem_hull_singleton.mpr ⟨_, neg_nonneg.mpr (h τ), by simp⟩
    obtain ⟨a, ha, he⟩ := mem_hull_singleton.mp (mem_comap.mp (hle hz))
    rw [← he, smul_eq_mul] at hzpos
    linarith
  obtain ⟨τ, hτ⟩ := hpos
  exact ⟨Ray.ofToricRay Φ σ τ, by simpa using hτ, σ, (ρ.toCone_le_iff σ).mpr hx,
    Ray.toCone_ofToricRay_le Φ σ τ⟩

private theorem eq_of_positive_neighbors (hΦ : Φ.IsRegular) (hN : Module.finrank ℤ N = 2)
    {ρ τ υ : Φ.Ray} {σ σ' : Φ.cones} {f : V →ₗ[ℝ] ℝ}
    (hker : f.ker = ℝ ∙ i ρ.primitiveGenerator) (hρ₀ : f (i ρ.primitiveGenerator) = 0)
    (hτ : 0 < f (i τ.primitiveGenerator)) (hυ : 0 < f (i υ.primitiveGenerator))
    (hρσ : ρ.toCone ≤ σ) (hτσ : τ.toCone ≤ σ) (hρσ' : ρ.toCone ≤ σ') (hυσ' : υ.toCone ≤ σ') :
    υ = τ := by
  let x := i ρ.primitiveGenerator
  let y := i τ.primitiveGenerator
  let z := i υ.primitiveGenerator
  have hline : f y • z - f z • y ∈ ℝ ∙ x := by
    rw [← hker, LinearMap.mem_ker]
    simp [mul_comm]
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hline
  have hab : f y • z = t • x + f z • y := eq_add_of_sub_eq ht.symm
  have hne : ρ ≠ τ := by rintro rfl; linarith
  have hne' : ρ ≠ υ := by rintro rfl; linarith
  rcases le_total 0 t with hp | hn
  · have hz : f y • z ∈ σ.val := by
      rw [hab]
      exact σ.val.add_mem (σ.val.smul_mem hp ((ρ.toCone_le_iff σ).mp hρσ))
        (σ.val.smul_mem hυ.le ((τ.toCone_le_iff σ).mp hτσ))
    exact (ray_eq_or_eq_of_le ((isRegular_iff.mp hΦ) _ σ.property) hN hne hρσ hτσ
      ((υ.toCone_le_iff σ).mpr ((σ.val.smul_mem_iff hτ).mp hz))).resolve_left (Ne.symm hne')
  · have hba : f z • y = -t • x + f y • z := by
      rw [hab, neg_smul, ← add_assoc, neg_add_cancel, zero_add]
    have hy : f z • y ∈ σ'.val := by
      rw [hba]
      exact σ'.val.add_mem (σ'.val.smul_mem (neg_nonneg.mpr hn) ((ρ.toCone_le_iff σ').mp hρσ'))
        (σ'.val.smul_mem hτ.le ((υ.toCone_le_iff σ').mp hυσ'))
    exact ((ray_eq_or_eq_of_le ((isRegular_iff.mp hΦ) _ σ'.property) hN hne' hρσ' hυσ'
      ((τ.toCone_le_iff σ').mpr ((σ'.val.smul_mem_iff hυ).mp hy))).resolve_left (Ne.symm hne)).symm

private theorem existsUnique_pos_neighbor (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hN : Module.finrank ℤ N = 2) (ρ : Φ.Ray) {f : V →ₗ[ℝ] ℝ} (hf : f ≠ 0)
    (hker : f.ker = ℝ ∙ i ρ.primitiveGenerator) :
    ∃! τ : Φ.Ray, 0 < f (i τ.primitiveGenerator) ∧
      ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ := by
  have hρ : f (i ρ.primitiveGenerator) = 0 :=
    LinearMap.mem_ker.mp (hker.symm ▸ Submodule.mem_span_singleton_self _)
  obtain ⟨τ, hτ, σ, hρσ, hτσ⟩ := exists_pos_neighbor hΦ hc ρ hf hρ
  refine ⟨τ, ⟨hτ, σ, hρσ, hτσ⟩, ?_⟩
  rintro υ ⟨hυ, σ', hρσ', hυσ'⟩
  exact eq_of_positive_neighbors hΦ hN hker hρ hτ hυ hρσ hτσ hρσ' hυσ'

/-- In a complete regular rank-two fan there is exactly one neighbouring ray on either
oriented side of a given ray. The positive side uses determinant one from the given
ray to its neighbour, and the negative side uses determinant minus one. -/
theorem exists_unique_ray_neighbor_on_each_side (b : Module.Basis (Fin 2) ℤ N)
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (ρ : Φ.Ray) :
    (∃! τ : Φ.Ray, b.detDualEquiv ρ.primitiveGenerator τ.primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ) ∧
    (∃! τ : Φ.Ray, b.detDualEquiv ρ.primitiveGenerator τ.primitiveGenerator = -1 ∧
      ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ) := by
  let m := (b.detDualEquiv ρ.primitiveGenerator).toAddMonoidHom
  let f := Φ.lattice.realCharacter m
  have hf : f ≠ 0 := by
    intro h
    have hm : m = 0 := Φ.lattice.realCharacter_injective (h.trans (map_zero _).symm)
    exact ρ.primitiveGenerator_ne_zero
      (b.detDualEquiv.map_eq_zero_iff.mp (LinearMap.toAddMonoidHom_injective hm))
  have hker := Φ.lattice.ker_realCharacter_detDualEquiv b ρ.primitiveGenerator_ne_zero
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  have hev (τ : Φ.Ray) :
      f (i τ.primitiveGenerator) =
        (b.detDualEquiv ρ.primitiveGenerator τ.primitiveGenerator : ℝ) := by
    rw [IsIntegralLattice.realCharacter_apply]
    rfl
  have hdet (τ : Φ.Ray) (h : ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ)
      (hne : f (i τ.primitiveGenerator) ≠ 0) :
      b.detDualEquiv ρ.primitiveGenerator τ.primitiveGenerator = 1 ∨
        b.detDualEquiv ρ.primitiveGenerator τ.primitiveGenerator = -1 := by
    obtain ⟨σ, hρσ, hτσ⟩ := h
    have hn : ρ ≠ τ := by
      rintro rfl
      apply hne
      rw [hev, b.detDualEquiv_self, Int.cast_zero]
    have hu := isUnit_det_of_ray_ne_of_le b ((isRegular_iff.1 hΦ) _ σ.property) hn hρσ hτσ
    exact Int.isUnit_iff.mp hu
  constructor
  · refine (existsUnique_congr fun τ ↦ ?_).mp (existsUnique_pos_neighbor hΦ hc hN ρ hf hker)
    constructor
    · rintro ⟨hp, h⟩
      rcases hdet τ h hp.ne' with hd | hd
      · exact ⟨hd, h⟩
      · norm_num [hev, hd] at hp
    · rintro ⟨hd, h⟩
      exact ⟨by simp [hev, hd], h⟩
  · refine (existsUnique_congr fun τ ↦ ?_).mp
      (existsUnique_pos_neighbor hΦ hc hN ρ (neg_ne_zero.mpr hf) (LinearMap.ker_neg f ▸ hker))
    constructor
    · rintro ⟨hp, h⟩
      have hn : f (i τ.primitiveGenerator) < 0 := neg_pos.mp hp
      rcases hdet τ h hn.ne with hd | hd
      · norm_num [hev, hd] at hn
      · exact ⟨hd, h⟩
    · rintro ⟨hd, h⟩
      exact ⟨by simp [hev, hd], h⟩

/-- The two oriented neighbours account for every distinct ray sharing a cone with the
given ray. -/
theorem exists_ray_neighbors (b : Module.Basis (Fin 2) ℤ N)
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (ρ : Φ.Ray) :
    ∃ prev next : Φ.Ray,
      b.detDualEquiv ρ.primitiveGenerator prev.primitiveGenerator = -1 ∧
      b.detDualEquiv ρ.primitiveGenerator next.primitiveGenerator = 1 ∧
      ∀ τ : Φ.Ray, (ρ ≠ τ ∧ ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ) ↔
        τ = prev ∨ τ = next := by
  obtain ⟨⟨next, ⟨hn, hncone⟩, hnuniq⟩, ⟨prev, ⟨hp, hpcone⟩, hpuniq⟩⟩ :=
    exists_unique_ray_neighbor_on_each_side b hΦ hc ρ
  refine ⟨prev, next, hp, hn, fun τ ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨hne, σ, hρ, hτ⟩
    have hu := isUnit_det_of_ray_ne_of_le b ((isRegular_iff.1 hΦ) _ σ.property) hne hρ hτ
    rcases Int.isUnit_iff.mp hu with h | h
    · exact Or.inr (hnuniq τ ⟨h, σ, hρ, hτ⟩)
    · exact Or.inl (hpuniq τ ⟨h, σ, hρ, hτ⟩)
  · rintro (he | he)
    · subst τ
      refine ⟨?_, hpcone⟩
      intro he
      subst prev
      rw [b.detDualEquiv_self] at hp
      omega
    · subst τ
      refine ⟨?_, hncone⟩
      intro he
      subst next
      rw [b.detDualEquiv_self] at hn
      omega

/-- A specified preceding and succeeding ray account for all distinct rays sharing a cone
with the middle ray. -/
theorem ray_neighbors_iff_of_det (b : Module.Basis (Fin 2) ℤ N)
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) {prev ρ next : Φ.Ray}
    (hprev : b.detDualEquiv prev.primitiveGenerator ρ.primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, prev.toCone ≤ σ ∧ ρ.toCone ≤ σ)
    (hnext : b.detDualEquiv ρ.primitiveGenerator next.primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ next.toCone ≤ σ) (τ : Φ.Ray) :
    (ρ ≠ τ ∧ ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ) ↔ τ = prev ∨ τ = next := by
  obtain ⟨p, q, hp, hq, hneighbors⟩ := exists_ray_neighbors b hΦ hc ρ
  obtain ⟨⟨_, _, hpos⟩, ⟨_, _, hneg⟩⟩ := exists_unique_ray_neighbor_on_each_side b hΦ hc ρ
  have hprev' : b.detDualEquiv ρ.primitiveGenerator prev.primitiveGenerator = -1 := by
    rw [b.detDualEquiv_swap, hprev.1]
  have hp' : p = prev :=
    (hneg p ⟨hp, ((hneighbors p).2 (Or.inl rfl)).2⟩).trans
      (hneg prev ⟨hprev', hprev.2.imp (fun _ h ↦ h.symm)⟩).symm
  have hq' : q = next :=
    (hpos q ⟨hq, ((hneighbors q).2 (Or.inr rfl)).2⟩).trans (hpos next hnext).symm
  simpa only [hp', hq'] using hneighbors τ

end TauCeti.Toric.Fan
