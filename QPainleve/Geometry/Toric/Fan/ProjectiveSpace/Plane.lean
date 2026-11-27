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

/-- A basis comparison from the toric plane to the projective spectrum of
a symmetric algebra respects the structure morphisms over the coefficient field. -/
theorem projectivePlaneIso_trans_polynomialProjIso_hom_isOver
    {M : Type} [AddCommGroup M] [Module ℂ M] (c : Basis (Fin 3) ℂ M) :
    ((projectivePlaneIso b hi) ≪≫ c.polynomialProjIso).hom.IsOver (Spec (.of ℂ)) := by
  refine ⟨?_⟩
  simp only [Iso.trans_hom, Category.assoc, SymmetricAlgebra.over_eq_projToSpec,
    Basis.polynomialProjIso_hom_over, projectivePlaneIso_hom_toSpecCoeff,
    algebraicRealization_over]

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
