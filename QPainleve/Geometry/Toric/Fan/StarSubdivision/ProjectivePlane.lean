/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Generators
public import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Boundary
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Boundary
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Factorization
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Blowup.Isomorphism
import QPainleve.AlgebraicGeometry.Blowup.Projective.Global
import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision
import QPainleve.Geometry.Toric.Cone.TwoDimensional
import QPainleve.Geometry.Toric.Fan.TwoDimensional

/-!
# Contracting the negative section of the toric Hirzebruch surface of index one

The star subdivision of the plane fan at any coordinate vertex has the rays
of `𝔽₁`. The blowup comparison identifies the inserted ray divisor with the
scheme-theoretic exceptional divisor. This gives the torus-fixed plane link
and its inverse, the negative-section contraction, in Wendelin Lutz's
Proposition 8.11 and Theorem 8.4 in
[the appendix to Hacking and Keating][HKL].

[HKL]: https://api.repository.cam.ac.uk/server/api/core/bitstreams/14b8f6c3-49a3-4961-a139-d11093383ddc/content
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Proj CategoryTheory Module PointedCone
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

local notation "plane[" d "]" => projectiveSpace d Φ.lattice
local notation "reg[" d "]" => isRegular_projectiveSpace d Φ.lattice
local notation "centerCone[" d "]" => projectiveSpaceMaximalCone d Φ.lattice none
attribute [local instance] MvPolynomial.gradedAlgebra

local notation "𝒫" => MvPolynomial.homogeneousSubmodule (Fin 3) ℂ
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "vertex[" d "]" =>
  Fan.distinguishedPointHom plane[d] centerCone[d] ≫ Iso.hom (projectivePlaneIso d Φ.lattice)
local notation "triangle" =>
  Scheme.IdealSheafData.radical (∏ j : Fin 3, coordinateHyperplaneIdeal (k := ℂ) (n := 2) j)

/-- The complete regular fan of `𝔽₁` realizes the blowup of the polynomial projective
plane at its vertex `[1 : 0 : 0]`. The projection is the toric contraction followed
by the plane comparison. The pullback of the vertex ideal is the boundary
ideal of the negative section, and the reduced pullback of the coordinate
triangle is the toric boundary of the source. The contraction reverses one
two-ray star subdivision. -/
theorem exists_iso_blowup_projectivePlane_of_hirzebruchOne
    (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hrays : Set.range (Fan.Ray.primitiveGenerator (Phi := Φ)) =
      {b 0, b 1, -b 0, b 0 - b 1}) :
    ∃ (d : Basis (Fin 2) ℤ N) (h : Φ.IsSubdivision (plane[d])) (r : Φ.Ray)
      (e : Φ.algebraicRealization ≅ (vertex[d]).ker.blowup),
      d 0 = b 0 - b 1 ∧ d 1 = b 1 ∧ r.primitiveGenerator = b 0 ∧
      (vertex[d]) ≫ toSpecCoeff 𝒫 = 𝟙 S ∧
      (∀ (j : Fin 3) (x : S), (vertex[d]) x ∈ basicOpen 𝒫 (MvPolynomial.X j) ↔ j = 0) ∧
      e.hom ≫ (vertex[d]).ker.blowupToBase =
        h.toFanHom.algebraicMap ≫ (projectivePlaneIso d Φ.lattice).hom ∧
      (vertex[d]).ker.comap (e.hom ≫ (vertex[d]).ker.blowupToBase) = Φ.rayBoundaryIdeal hΦ r ∧
      ((triangle).comap (e.hom ≫ (vertex[d]).ker.blowupToBase)).radical =
        Φ.boundaryIdeal hc.nonempty_cones ∧ (plane[d]).IsTwoRayStarSubdivision Φ := by
  obtain ⟨d, hσ, hd₀, hd₁, heq, hnew⟩ :=
    exists_eq_starSubdivision_projectivePlane_of_hirzebruchOne b hΦ hc hrays
  -- Keep the lattice frame of the plane fixed while replacing the source fan.
  generalize hL : Φ.lattice = hi at hσ heq hnew ⊢
  subst Φ
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  let Ψ := projectiveSpace d hi
  let hΨ := isRegular_projectiveSpace d hi
  let σ := projectiveSpaceMaximalCone d hi none
  let g := projectivePlaneIso d hi
  let z := Ψ.distinguishedPointHom σ
  let p := z ≫ g.hom
  have hcenter : p.ker.comap g.hom = z.ker := z.comap_ker_comp_of_isClosedImmersion g.hom
  obtain ⟨h₀, f, -, hf, -⟩ := Ψ.exists_iso_blowup_starSubdivisionAlong hΨ σ hN hσ
  let hstar := Ψ.starSubdivisionAlong_isSubdivision hΨ σ.property h₀
  let u := Ψ.starSubdivisionAlongRay hΨ σ.property h₀
  let e := f ≪≫ blowupIso g hcenter.symm
  have hproj : e.hom ≫ p.ker.blowupToBase = hstar.toFanHom.algebraicMap ≫ g.hom := by
    rw [Iso.trans_hom, Category.assoc, blowupIso_hom_blowupToBase, ← Category.assoc, hf]
  refine ⟨d, hstar, u, e, hd₀, hd₁, hnew, ?_, ?_, hproj, ?_, ?_, .along hΨ σ hσ⟩
  · simp only [Category.assoc, projectivePlaneIso_hom_toSpecCoeff,
      distinguishedPointHom_comp_algebraicRealizationStructureMap]
  · intro j x
    simpa only [Scheme.Hom.comp_apply, finSuccEquiv_zero, eq_comm] using
      projectivePlaneIso_distinguishedPointHom_mem_basicOpen_iff d hi 0 j x
  · rw [hproj, comap_comp, hcenter]
    exact Ψ.comap_ker_distinguishedPointHom_eq_rayBoundaryIdeal hΨ σ h₀ hN hσ
  · rw [hproj, comap_comp, projectivePlaneIso_comap_coordinateTriangle d hi ⟨σ⟩]
    exact hstar.radical_comap_boundaryIdeal hc.nonempty_cones ⟨σ⟩

/-- Blowing up any specified torus-fixed vertex of the plane is the star subdivision
with Hirzebruch-one rays. The projection and the exceptional ideal agree with those
of the actual blowup at the distinguished point. The first basis vector is opposite
to the ray omitted by the vertex cone. -/
theorem exists_blowup_projectivePlane_vertex_hirzebruchOne
    (d : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i) (k : Option (Fin 2)) :
    let Ψ := projectiveSpace d hi
    let hΨ := isRegular_projectiveSpace d hi
    let σ := projectiveSpaceMaximalCone d hi k
    let Γ := Ψ.starSubdivisionAlong hΨ σ.property
    let J := (Ψ.distinguishedPointHom σ).ker
    ∃ (hσ : σ.val ≠ ⊥) (b : Basis (Fin 2) ℤ N) (e : Γ.algebraicRealization ≅ J.blowup),
      Set.range (Ray.primitiveGenerator (Phi := Γ)) = {b 0, b 1, -b 0, b 0 - b 1} ∧
      (Ψ.starSubdivisionAlongRay hΨ σ.property hσ).primitiveGenerator = b 0 ∧
      e.hom ≫ J.blowupToBase =
        (Ψ.starSubdivisionAlong_isSubdivision hΨ σ.property hσ).toFanHom.algebraicMap ∧
      J.comap (e.hom ≫ J.blowupToBase) =
        Γ.rayBoundaryIdeal (Ψ.isRegular_starSubdivisionAlong hΨ σ.property)
          (Ψ.starSubdivisionAlongRay hΨ σ.property hσ) ∧
      b 0 = -projectiveSpaceGenerator d k := by
  intro Ψ hΨ σ Γ J
  have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis d
  obtain ⟨hcard, b, hnew, hrays, hb⟩ := projectivePlane_vertex_starSubdivision_rays d hi k
  obtain ⟨hσ, e, -, he, -⟩ := Ψ.exists_iso_blowup_starSubdivisionAlong hΨ σ hdim hcard
  exact ⟨hσ, b, e, hrays, hnew, he,
    he ▸ Ψ.comap_ker_distinguishedPointHom_eq_rayBoundaryIdeal hΨ σ hσ hdim hcard, hb⟩

/-- The star subdivision of the plane fan at any specified torus-fixed vertex
has projective algebraic realization over `ℂ`. -/
theorem isProjectiveOver_projectivePlane_vertex_starSubdivision
    (d : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i) (k : Option (Fin 2)) :
    let Ψ := projectiveSpace d hi
    let hΨ := isRegular_projectiveSpace d hi
    let σ := projectiveSpaceMaximalCone d hi k
    (Ψ.starSubdivisionAlong hΨ σ.property).algebraicRealization.IsProjectiveOver ℂ := by
  intro Ψ hΨ σ
  obtain ⟨hσ, _, e, -, -, he, -, -⟩ := exists_blowup_projectivePlane_vertex_hirzebruchOne d hi k
  let J := (Ψ.distinguishedPointHom σ).ker
  let : J.blowup.Over S := ⟨J.blowupToBase ≫ Ψ.algebraicRealization ↘ S⟩
  let : Ψ.algebraicRealization.IsProjectiveOver ℂ :=
    Scheme.IsProjectiveOver.of_isClosedImmersion ℂ (projectiveSpaceToProj d hi)
  let : J.blowup.IsProjectiveOver ℂ := J.isProjectiveOver_blowup_of_isNoetherianRing ℂ
  let π := (Ψ.starSubdivisionAlong_isSubdivision hΨ σ.property hσ).toFanHom.algebraicMap
  let : e.hom.IsOver S :=
    ⟨((reassoc_of% he) (Ψ.algebraicRealization ↘ S)).trans (comp_over π S)⟩
  exact Scheme.IsProjectiveOver.of_isClosedImmersion ℂ e.hom

end TauCeti.Toric.Fan
