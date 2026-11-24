/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
public import QPainleve.Geometry.Toric.Fan.Point
public import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Ray
public import TauCeti.Geometry.Toric.Algebraic.Fan.ProjectiveSpace.Proj

import QPainleve.Geometry.Toric.Fan.TwoDimensional

/-!
# The toric projective plane

The three primitive rays of a complete regular surface fan in plane normal
form identify it with the native projective-space fan. The comparison
`Fan.projectiveSpaceToProj` then identifies its maximal cone charts with the
standard coordinate opens in polynomial projective space.
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Proj CategoryTheory Module PointedCone

namespace TauCeti.Toric.Fan

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

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
the negative sum of the two basis vectors. -/
theorem projectivePlane_vertex_rays (d : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    (k : Option (Fin 2)) :
    let σ := projectiveSpaceMaximalCone d hi k
    ∃ c : Basis (Fin 2) ℤ N, σ.val = hull ℝ (Set.range (i ∘ c)) ∧
      Set.range (projectiveSpaceGenerator d) = {c 0, c 1, -c 0 - c 1} := by
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
  refine ⟨c, ?_, ?_⟩
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

/-- A complete regular rank-two fan with the plane ray generators is the
projective-space fan in that lattice frame. -/
theorem eq_projectiveSpace_of_plane_ray_generators
    (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hrays : Set.range (Fan.Ray.primitiveGenerator (Phi := Φ)) = {b 0, b 1, -b 0 - b 1}) :
    Φ = projectiveSpace b Φ.lattice :=
  eq_of_range_primitiveGenerator_eq b hΦ (isRegular_projectiveSpace b Φ.lattice) hc
    (isComplete_projectiveSpace b Φ.lattice)
    (hrays.trans (range_primitiveGenerator_projectivePlane b Φ.lattice).symm)

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "𝒫" => MvPolynomial.homogeneousSubmodule (Fin 3) ℂ
local notation "P" => Proj 𝒫
local notation "𝒮" => SymmetricAlgebra.homogeneousSubmodule ℂ (Option (Fin 2) → ℂ)
local notation "coords" =>
  Basis.reindex (Pi.basisFun ℂ (Option (Fin 2))) (Equiv.symm (finSuccEquiv 2))

variable (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)

/-- The projective-space fan of an integral plane realizes the polynomial projective plane.
The coordinate indexed by `none` in the fan is indexed by zero in the polynomial ring. -/
def projectivePlaneIso : (projectiveSpace b hi).algebraicRealization ≅ P :=
  asIso (projectiveSpaceToProj b hi) ≪≫ (coords).polynomialProjIso.symm

/-- The toric comparison with the polynomial projective plane is over the coefficient field. -/
@[reassoc (attr := simp)]
theorem projectivePlaneIso_hom_toSpecCoeff :
    (projectivePlaneIso b hi).hom ≫ toSpecCoeff 𝒫 =
      (projectiveSpace b hi).algebraicRealizationStructureMap := by
  rw [projectivePlaneIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    ← (coords).polynomialProjIso_hom_over, Category.assoc, Iso.inv_hom_id_assoc,
    ← SymmetricAlgebra.over_eq_projToSpec, CategoryTheory.comp_over, algebraicRealization_over]

/-- The standard chart of the polynomial projective plane pulls back to the corresponding
maximal cone chart. -/
@[simp]
theorem projectivePlaneIso_hom_preimage_basicOpen (j : Fin 3) :
    (projectivePlaneIso b hi).hom ⁻¹ᵁ basicOpen 𝒫 (MvPolynomial.X j) =
      ((projectiveSpace b hi).affineToricChartι
        (projectiveSpaceMaximalCone b hi (finSuccEquiv 2 j))).opensRange := by
  let k := finSuccEquiv 2 j
  let σ := projectiveSpaceMaximalCone b hi k
  have h : projectiveSpaceToProj b hi ''ᵁ ((projectiveSpace b hi).affineToricChartι σ).opensRange =
      basicOpen 𝒮 (SymmetricAlgebra.ι ℂ (Option (Fin 2) → ℂ) (Pi.single k 1)) := by
    rw [← Scheme.Hom.opensRange_comp, ← opensRange_projectiveSpaceChartToProj (b := b) (hi := hi) k]
    apply TopologicalSpace.Opens.ext
    simp only [Scheme.Hom.coe_opensRange, affineToricChartι_comp_projectiveSpaceToProj σ le_rfl]
  rw [← (coords).polynomialProjIso_hom_preimage_basicOpen_ι j, ← Scheme.Hom.comp_preimage]
  simp only [projectivePlaneIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Basis.reindex_apply, Equiv.symm_symm, Pi.basisFun_apply]
  rw [← h, Scheme.Hom.preimage_image_eq]

variable {W : Type} [AddCommGroup W] [Module ℝ W] {a : N →+ W} in
/-- The distinguished point of a maximal cone of the plane fan is the coordinate vertex
corresponding to the omitted ray. -/
theorem projectivePlaneIso_distinguishedPointHom_mem_basicOpen_iff (ha : IsIntegralLattice a)
    (j l : Fin 3)
    (x : Spec (.of ℂ)) :
    (projectivePlaneIso b ha).hom
        ((projectiveSpace b ha).distinguishedPointHom
          (projectiveSpaceMaximalCone b ha (finSuccEquiv 2 j)) x) ∈
        basicOpen 𝒫 (MvPolynomial.X l) ↔ j = l := by
  let σ := projectiveSpaceMaximalCone b ha (finSuccEquiv 2 j)
  let τ := projectiveSpaceMaximalCone b ha (finSuccEquiv 2 l)
  have h : σ ≤ τ ↔ j = l := by
    rw [← Subtype.coe_le_coe, projectiveSpaceCone_le_iff b (ha.linearIndependent_basis b) (by simp)]
    simp only [Set.compl_subset_compl, Set.singleton_subset_iff, Set.mem_singleton_iff,
      (finSuccEquiv 2).injective.eq_iff, eq_comm]
  rw [← Scheme.Hom.mem_preimage, projectivePlaneIso_hom_preimage_basicOpen]
  simpa only [Scheme.Hom.mem_opensRange, Set.mem_range] using
    ((projectiveSpace b ha).distinguishedPointHom_mem_range_affineToricChartι_iff σ τ x).trans h

end TauCeti.Toric.Fan
