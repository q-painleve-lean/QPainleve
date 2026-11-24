/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Picard
public import QPainleve.Geometry.Toric.Fan.Boundary.Basic
public import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Plane

import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction

/-!
# The coordinate triangle of the toric projective plane

The intersection of the three standard charts is the dense torus. Its reduced
complement is therefore the union of the three coordinate hyperplanes.
-/

public section

open AlgebraicGeometry AlgebraicGeometry.Proj CategoryTheory Module TopologicalSpace
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "𝒫" => MvPolynomial.homogeneousSubmodule (Fin 3) ℂ
local notation "Φ" => projectiveSpace b hi
local notation "g" => Iso.hom (projectivePlaneIso b hi)
local notation "H[" j "]" => coordinateHyperplaneIdeal (k := ℂ) (n := 2) j

/-- The dense torus of the projective plane consists of the points for which
every homogeneous coordinate is nonzero. -/
theorem mem_range_denseTorusι_projectivePlane_iff (h₀ : Nonempty (Φ).cones)
    (x : (Φ).algebraicRealization) :
    x ∈ Set.range ((Φ).denseTorusι h₀) ↔ ∀ j : Fin 3, g x ∈ basicOpen 𝒫 (MvPolynomial.X j) := by
  let σ (j : Fin 3) := projectiveSpaceMaximalCone b hi (finSuccEquiv 2 j)
  have hbot := bot_mem_projectiveSpace_cones b hi
  have hmeet : σ 0 ⊓ σ 1 ⊓ σ 2 = ⟨⊥, hbot⟩ := by
    apply Subtype.ext
    simp only [coe_inf]
    -- The maximal cones meet in the cone indexed by the intersection of the three complements.
    change ((projectiveSpaceCone b i {finSuccEquiv 2 0}ᶜ ⊓
      projectiveSpaceCone b i {finSuccEquiv 2 1}ᶜ) ⊓
      projectiveSpaceCone b i {finSuccEquiv 2 2}ᶜ) = ⊥
    rw [projectiveSpaceCone_inf b (hi.linearIndependent_basis b),
      projectiveSpaceCone_inf b (hi.linearIndependent_basis b)]
    have hempty : (({finSuccEquiv 2 0}ᶜ ∩ {finSuccEquiv 2 1}ᶜ) ∩
        {finSuccEquiv 2 2}ᶜ : Set (Option (Fin 2))) = ∅ := by
      ext k
      obtain ⟨j, rfl⟩ := (finSuccEquiv 2).surjective k
      fin_cases j <;> simp
    rw [hempty, projectiveSpaceCone_empty]
  have hchart (j : Fin 3) :
      g x ∈ basicOpen 𝒫 (MvPolynomial.X j) ↔
        x ∈ Set.range ((Φ).affineToricChartι (σ j)) := by
    rw [← Scheme.Hom.mem_preimage, projectivePlaneIso_hom_preimage_basicOpen,
      Scheme.Hom.mem_opensRange]
    rfl
  simp only [hchart, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
  have h := congrArg (fun τ : (Φ).cones ↦ Set.range ((Φ).affineToricChartι τ)) hmeet
  rw [← range_affineToricChartι_inter_range_affineToricChartι,
    ← range_affineToricChartι_inter_range_affineToricChartι] at h
  rw [denseTorusι_eq_affineToricChartι _ h₀ hbot, ← h]
  exact and_assoc

/-- The plane comparison pulls back the reduced union of the coordinate
hyperplanes to the toric boundary ideal. -/
theorem projectivePlaneIso_comap_coordinateTriangle (h₀ : Nonempty (Φ).cones) :
    ((∏ j : Fin 3, H[j]).radical).comap g = (Φ).boundaryIdeal h₀ := by
  rw [← radical_comap_of_isOpenImmersion, ← vanishingIdeal_support, boundaryIdeal_def]
  congr 1
  apply SetLike.coe_injective
  ext x
  rw [support_comap, Closeds.coe_preimage, Set.mem_preimage]
  -- Compare the underlying sets of the two bundled closed loci.
  change g x ∈ ((∏ j : Fin 3, H[j]).support : Set _) ↔ x ∉ Set.range ((Φ).denseTorusι h₀)
  rw [mem_range_denseTorusι_projectivePlane_iff]
  simp only [Fin.prod_univ_three, support_mul, Closeds.coe_sup,
    coe_support_coordinateHyperplaneIdeal, Set.mem_union, Set.mem_compl_iff,
    Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
  tauto

end TauCeti.Toric.Fan
