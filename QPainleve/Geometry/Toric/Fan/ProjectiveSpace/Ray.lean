/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ray
public import TauCeti.Geometry.Toric.Algebraic.Fan.ProjectiveSpace.Basic
import QPainleve.Geometry.Toric.Fan.TwoDimensional

/-!
# Primitive rays of the projective-space fan

The primitive ray generators of the fan of projective space are the vectors of
the chosen basis and the negative of their sum. This identifies the rays in the
native `Fan.projectiveSpace` with its defining family of lattice vectors.
-/

public section

open Module PointedCone

namespace TauCeti.Toric.Fan

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- For a positive-dimensional projective-space fan the prescribed lattice vectors are
exactly the primitive generators of the actual rays of the fan. -/
theorem range_primitiveGenerator_projectiveSpace [Fintype ι] [Nonempty ι]
    (b : Basis ι ℤ N) (hi : IsIntegralLattice i) :
    Set.range (Ray.primitiveGenerator (Phi := projectiveSpace b hi)) =
      Set.range (projectiveSpaceGenerator b) := by
  classical
  have hprim (k : Option ι) : IsPrimitive (projectiveSpaceGenerator b k) := by
    cases k with
    | some j => simpa only [projectiveSpaceGenerator_some] using b.isPrimitive j
    | none =>
      obtain ⟨j⟩ := ‹Nonempty ι›
      exact isPrimitive_def.mpr ⟨-b.coord j, by simp⟩
  ext v
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨S, -, hS⟩ := (mem_projectiveSpace_cones b hi).mp r.toCone.property
    have hnonempty : S.Nonempty := Set.ne_empty_iff_nonempty.mp fun h ↦
      r.toCone_ne_bot _ (by rw [← hS, h, projectiveSpaceCone_empty])
    obtain ⟨k, hk⟩ := hnonempty
    have hm : i (projectiveSpaceGenerator b k) ∈ r.toCone.val := by
      rw [← hS, projectiveSpaceCone_def]
      exact subset_hull (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hk))
    exact ⟨k, (r.primitiveGenerator_eq_of_mem_of_isPrimitive hm (hprim k)).symm⟩
  · rintro ⟨k, rfl⟩
    let C := hull ℝ {i (projectiveSpaceGenerator b k)}
    have hC : C ∈ (projectiveSpace b hi).cones := (mem_projectiveSpace_cones b hi).mpr
      ⟨{k}, Set.singleton_ne_univ k,
        by rw [projectiveSpaceCone_def, Set.image_singleton, Set.image_singleton]⟩
    have hne : i (projectiveSpaceGenerator b k) ≠ 0 := by
      exact (map_ne_zero_iff i hi.injective).mpr (hprim k).ne_zero
    let r : (projectiveSpace b hi).Ray := ⟨⟨C, hC⟩, finrank_span_coe_hull_singleton hne⟩
    exact ⟨r, r.primitiveGenerator_eq_of_mem_of_isPrimitive
      (subset_hull (Set.mem_singleton _)) (hprim k)⟩

variable (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)

private theorem injective_projectivePlaneGenerator :
    Function.Injective (projectiveSpaceGenerator b) := by
  intro j k h
  rcases j with _ | j <;> rcases k with _ | k
  · rfl
  · have hh := congrArg (b.coord k) h
    fin_cases k <;> norm_num [Fin.sum_univ_two, Basis.coord_apply] at hh
  · have hh := congrArg (b.coord j) h
    fin_cases j <;> norm_num [Fin.sum_univ_two, Basis.coord_apply] at hh
  · exact congrArg some (b.injective (by simpa only [projectiveSpaceGenerator_some] using h))

/-- The two basis rays of the plane fan are indexed by `some` and their negative
sum is indexed by `none`. -/
noncomputable def projectivePlaneRayEquiv : Option (Fin 2) ≃ (projectiveSpace b hi).Ray :=
  ((Equiv.ofInjective _ (injective_projectivePlaneGenerator b)).trans
    (Set.equivOfEq (range_primitiveGenerator_projectiveSpace b hi).symm)).trans
      (Equiv.ofInjective _ Ray.primitiveGenerator_injective).symm

/-- A labelled ray has the corresponding primitive generator of the plane fan. -/
@[simp]
theorem primitiveGenerator_projectivePlaneRayEquiv (j : Option (Fin 2)) :
    (projectivePlaneRayEquiv b hi j).primitiveGenerator = projectiveSpaceGenerator b j := by
  exact congrArg Subtype.val
    ((Equiv.ofInjective _ Ray.primitiveGenerator_injective).apply_symm_apply _)

section Plane

variable {Φ : Fan i}

/-- In rank two, the projective-space fan has the three primitive rays of the
coordinate triangle. -/
theorem range_primitiveGenerator_projectivePlane (b : Basis (Fin 2) ℤ N)
    (hi : IsIntegralLattice i) :
    Set.range (Fan.Ray.primitiveGenerator (Phi := projectiveSpace b hi)) =
      {b 0, b 1, -b 0 - b 1} := by
  rw [range_primitiveGenerator_projectiveSpace]
  ext v
  simp [Option.exists, Fin.exists_fin_two, Fin.sum_univ_two, neg_add_rev, sub_eq_add_neg, add_comm]
  grind

/-- Any two distinct rays of the plane fan belong to a common cone. -/
theorem exists_cone_projectivePlane_of_ray_ne (b : Basis (Fin 2) ℤ N)
    (hi : IsIntegralLattice i) {ρ τ : (projectiveSpace b hi).Ray} (hne : ρ ≠ τ) :
    ∃ σ : (projectiveSpace b hi).cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ := by
  classical
  let e := projectivePlaneRayEquiv b hi
  obtain ⟨a, rfl⟩ := e.surjective ρ
  obtain ⟨c, rfl⟩ := e.surjective τ
  have hn : a ≠ c := fun h ↦ hne (congrArg e h)
  have hs : ({a, c} : Set (Option (Fin 2))) ≠ Set.univ := by
    intro h
    have he := Set.ncard_pair hn
    rw [h, Set.ncard_univ] at he
    simp at he
  have hcone : projectiveSpaceCone b i {a, c} ∈ (projectiveSpace b hi).cones :=
    (mem_projectiveSpace_cones b hi).mpr ⟨_, hs, rfl⟩
  have hle (j : Option (Fin 2)) (hj : j ∈ ({a, c} : Set (Option (Fin 2)))) :
      (e j).toCone.val ≤ projectiveSpaceCone b i {a, c} := by
    rw [Ray.toCone_eq_hull_primitiveGenerator, primitiveGenerator_projectivePlaneRayEquiv,
      projectiveSpaceCone_def]
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr
      (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hj)))
  exact ⟨⟨_, hcone⟩, hle a (by simp), hle c (by simp)⟩

/-- The two ray generators of a maximal cone of the plane fan form an integral basis. -/
theorem exists_projectivePlane_vertex_basis (d : Basis (Fin 2) ℤ N)
    (hi : IsIntegralLattice i) (k : Option (Fin 2)) :
    ∃ (c : Basis (Fin 2) ℤ N) (a : {j : Option (Fin 2) // j ≠ k} ≃ Fin 2),
      ∀ j, c (a j) = projectiveSpaceGenerator d j := by
  classical
  let σ := projectiveSpaceMaximalCone d hi k
  let J := {j : Option (Fin 2) // j ≠ k}
  let v : J → V := fun j ↦ i (projectiveSpaceGenerator d j)
  have hσ := isRegular_iff.mp (isRegular_projectiveSpace d hi) σ.val σ.property
  have hv : σ.val = hull ℝ (Set.range v) := by
    -- The maximal cone uses the complement of the omitted ray index.
    change projectiveSpaceCone d i {k}ᶜ = _
    rw [projectiveSpaceCone_def, Set.image_image, Set.image_eq_range]
    rfl
  have hvli : LinearIndependent ℝ v :=
    linearIndepOn_projectiveSpaceGenerator d (hi.linearIndependent_basis d)
      (Set.compl_ne_univ.mpr (Set.singleton_nonempty k))
  let e := toricRayEquivOfLinearIndependent v hvli hv
  have hJ : Fintype.card J = 2 := by simp [J]
  obtain ⟨c, r, hr⟩ := hσ.exists_basis_finrank
  have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis d
  let a := e.symm.toEmbedding.trans (r.trans (finCongr hdim).toEmbedding)
  have ha : Function.Surjective a :=
    (Finite.injective_iff_surjective_of_equiv (Fintype.equivFinOfCardEq hJ)).mp a.injective
  refine ⟨c.reindex (finCongr hdim), Equiv.ofBijective a ⟨a.injective, ha⟩, fun j ↦ ?_⟩
  have hgen := hr.isPrimitiveGenerator_apply (e.symm j)
  obtain ⟨q, hq⟩ := (range_primitiveGenerator_projectiveSpace d hi ▸
      Set.mem_range_self (f := projectiveSpaceGenerator d) j.val)
  have hj := (apply_mem_iff_toricRayEquivOfLinearIndependent _ _ hv (e.symm j) j).mpr
    (e.apply_symm_apply j).symm
  have hp := isPrimitiveGenerator_iff.mpr ⟨hj, hq ▸ q.isPrimitiveGenerator.isPrimitive⟩
  simpa [a, Equiv.ofBijective_apply] using (hgen.eq_primitiveGenerator hi hσ.toIsToricCone).trans
    (hp.eq_primitiveGenerator hi hσ.toIsToricCone).symm

/-- In a basis for the maximal cone at a plane vertex, the third ray generator is
the negative sum of the two basis vectors, and is the generator omitted at that vertex. -/
theorem projectivePlane_vertex_rays (d : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    (k : Option (Fin 2)) :
    let σ := projectiveSpaceMaximalCone d hi k
    ∃ c : Basis (Fin 2) ℤ N, σ.val = hull ℝ (Set.range (i ∘ c)) ∧
      Set.range (projectiveSpaceGenerator d) = {c 0, c 1, -c 0 - c 1} ∧
      projectiveSpaceGenerator d k = -c 0 - c 1 := by
  classical
  obtain ⟨c, a, ha⟩ := exists_projectivePlane_vertex_basis d hi k
  have hrange : projectiveSpaceGenerator d '' {k}ᶜ = Set.range c := by
    rw [Set.image_eq_range, ← a.surjective.range_comp c]
    exact congrArg Set.range (funext fun j ↦ (ha j).symm)
  have hrem := Equiv.sum_comp a c
  simp only [ha, Fin.sum_univ_two] at hrem
  have hsum := sum_projectiveSpaceGenerator d
  have hsplit : (∑ j ∈ Finset.univ.erase k, projectiveSpaceGenerator d j) =
      ∑ j : {j // j ≠ k}, projectiveSpaceGenerator d j := Finset.sum_subtype (Finset.univ.erase k)
    (p := fun j ↦ j ≠ k) (by simp) (projectiveSpaceGenerator d)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), hsplit, hrem] at hsum
  have hk : projectiveSpaceGenerator d k = -c 0 - c 1 := by
    calc
      _ = -(c 0 + c 1) := eq_neg_of_add_eq_zero_right hsum
      _ = _ := by abel
  refine ⟨c, ?_, ?_, hk⟩
  · -- Unfold the maximal cone to apply its hull formula.
    change projectiveSpaceCone d i {k}ᶜ = _
    rw [projectiveSpaceCone_def, hrange, Set.range_comp]
  · have huniv : insert k ({k}ᶜ : Set (Option (Fin 2))) = Set.univ := by
      ext j
      simp [em]
    rw [← Set.image_univ, ← huniv, Set.image_insert_eq,
      hrange, hk]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range,
      Fin.exists_fin_two]
    tauto

/-- A vertex cone of the projective plane fan has exactly two rays. -/
@[simp]
theorem card_toricRay_projectiveSpaceMaximalCone
    (d : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i) (k : Option (Fin 2)) :
    Nat.card (ToricRay (projectiveSpaceMaximalCone d hi k).val) = 2 := by
  obtain ⟨c, hc, -, -⟩ := projectivePlane_vertex_rays d hi k
  let e := toricRayEquivOfLinearIndependent (i ∘ c) (hi.linearIndependent_basis c) hc
  exact (Nat.card_congr e).trans (Nat.card_fin 2)

/-- A two-ray cone of the plane fan is one of its three maximal cones. -/
theorem exists_eq_projectiveSpaceMaximalCone_of_card_toricRay_eq_two
    (d : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i) (σ : (projectiveSpace d hi).cones)
    (hσ : Nat.card (ToricRay σ.val) = 2) :
    ∃ k : Option (Fin 2), σ = projectiveSpaceMaximalCone d hi k := by
  have hdim : finrank ℤ N = 2 := (finrank_eq_card_basis d).trans (Fintype.card_fin 2)
  obtain ⟨k, hk⟩ := exists_le_projectiveSpaceCone_compl d hi σ.property
  exact ⟨k, (projectiveSpace d hi).eq_of_le_fullCone (isRegular_projectiveSpace d hi) hdim hσ hk⟩

/-- A complete regular rank-two fan with the plane ray generators is the
projective-space fan in that lattice frame. -/
theorem eq_projectiveSpace_of_plane_ray_generators
    (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hrays : Set.range (Fan.Ray.primitiveGenerator (Phi := Φ)) = {b 0, b 1, -b 0 - b 1}) :
    Φ = projectiveSpace b Φ.lattice :=
  eq_of_range_primitiveGenerator_eq b hΦ (isRegular_projectiveSpace b Φ.lattice) hc
    (isComplete_projectiveSpace b Φ.lattice)
    (hrays.trans (range_primitiveGenerator_projectivePlane b Φ.lattice).symm)

end Plane

end TauCeti.Toric.Fan
