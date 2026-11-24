/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.CommonResolution
public import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Plane

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Smooth
import QPainleve.Geometry.Toric.Fan.FunctionField
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# Reduction of specified toric contractions to plane resolutions

A common nodal refinement resolves the toric changes from the given targets to
projective planes. In the standard projective plane coordinates, the resulting
maps are compositions of closed point blowups, up to isomorphism over the planes.
The specified maps and the pole ideal are retained on the common surface.

This is the reduction to a plane target in the proof of
[Lutz's Theorem 8.4][HKL]. The two ends of the given map can be reduced using
different lattice frames.

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "s[" Δ "]" => Fan.algebraicRealizationStructureMap Δ
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)
local notation "B[" Δ "," h "]" => Fan.boundaryIdeal Δ (IsComplete.nonempty_cones h)

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "P" => Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "planeIso(" b "," h ")" =>
  Fan.projectivePlaneIso b h ≪≫ Module.Basis.polynomialProjIso (Pi.basisFun ℂ (Fin 3))

private theorem factor_plane_projection
    {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
    (b : Module.Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    {Z : Scheme} [Z.Over S] [Z.IsProjectiveOver ℂ] [IsIntegral Z]
    [SmoothOfRelativeDimension 2 (Z ↘ S)]
    (p : Z ⟶ X[projectiveSpace b hi]) [p.IsOver S] [IsModification p]
    {D : Z.IdealSheafData}
    (hpole : letI : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 _
      (B[projectiveSpace b hi,isComplete_projectiveSpace b hi]).comap p =
        D * ramificationIdealSheaf ℂ p) :
    let e := planeIso(b,hi)
    let q := p ≫ e.hom
    ∃ (n : ℕ) (Y : Scheme) (U : BlowupTower P n Y) (a : Z ≅ Y),
      IsClosedPointTower P U ∧ a.hom ≫ U.toBase = q ∧
      ∃ hover : q ≫ P ↘ S = Z ↘ S,
        letI : q.IsOver S := ⟨hover⟩
        letI : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 _
        ((B[projectiveSpace b hi,isComplete_projectiveSpace b hi]).comap e.inv).comap q =
          D * ramificationIdealSheaf ℂ q := by
  intro e q
  have he : e.hom ≫ (P ↘ S) = s[projectiveSpace b hi] := by
    simp only [e, Iso.trans_hom, Category.assoc, TauCeti.SymmetricAlgebra.over_eq_projToSpec,
      Module.Basis.polynomialProjIso_hom_over, projectivePlaneIso_hom_toSpecCoeff]
  let : e.hom.IsOver S := ⟨he.trans (algebraicRealization_over _).symm⟩
  let : q.IsOver S := inferInstanceAs ((p ≫ e.hom).IsOver S)
  have : IsModification q := inferInstanceAs (IsModification (p ≫ e.hom))
  let : Nonempty (projectiveSpace b hi).cones := (isComplete_projectiveSpace b hi).nonempty_cones
  have : IsIntegral P := IsIntegral.of_isIso e.hom
  have : IsSeparated (P ↘ S) := by
    rw [TauCeti.SymmetricAlgebra.over_eq_projToSpec]
    infer_instance
  let : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have hRank : Module.finrank ℤ N = 2 :=
    (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let : SmoothOfRelativeDimension 2 (X[projectiveSpace b hi] ↘ S) := by
    simpa only [hRank, algebraicRealization_over] using
      (projectiveSpace b hi).smoothOfRelativeDimension_algebraicRealizationStructureMap
        (isRegular_projectiveSpace b hi)
  let : Smooth (X[projectiveSpace b hi] ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  obtain ⟨n, Y, U, a, hU, ha⟩ :=
    q.exists_isClosedPointTower_factorization (k := ℂ) (IsModification.birationalOver q)
  refine ⟨n, Y, U, a, hU, ha, comp_over q S, ?_⟩
  simp only [q, ← comap_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    ramificationIdealSheaf_comp ℂ p e.hom 2, ramificationIdealSheaf_eq_top_of_isOpenImmersion,
    comap_top, mul_top, hpole]

variable {X : Scheme} [X.Over S] [IsIntegral X] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)] {D : X.IdealSheafData}

/-- Reduce specified toric contractions with common pole divisor `-D` to planes
on a single nodal refinement. Each original morphism is recovered through its
common fan, and the projection to every coarsening of that fan realizes the
corresponding prescribed toric change. Each plane projection is isomorphic to
a closed point-blowup tower in the standard coordinates for the degree and
multiplicities. Its pole ideal is the reduced total boundary on the common surface. -/
theorem exists_common_nodal_plane_reduction
    {ι : Type*} [Finite ι] {N V : ι → Type}
    [∀ j, AddCommGroup (N j)] [∀ j, AddCommGroup (V j)] [∀ j, Module ℝ (V j)]
    {i : ∀ j, N j →+ V j} {Φ : ∀ j, Fan (i j)}
    (b : ∀ j, Module.Basis (Fin 2) ℤ (N j))
    (hΦ : ∀ j, (Φ j).IsRegular) (hcΦ : ∀ j, (Φ j).IsComplete)
    (f : ∀ j, X ⟶ X[Φ j]) [∀ j, (f j).IsOver S] [∀ j, IsModification (f j)]
    (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hdiv : ∀ j,
      let hRank : Module.finrank ℤ (N j) = 2 :=
        (Module.finrank_eq_card_basis (b j)).trans (Fintype.card_fin 2)
      letI : SmoothOfRelativeDimension 2 (X[Φ j] ↘ S) :=
        hRank ▸ (Φ j).smoothOfRelativeDimension_algebraicRealizationStructureMap (hΦ j)
      letI : Nonempty (Φ j).cones := (hcΦ j).nonempty_cones
      let hB := (Φ j).isEffectiveCartier_boundaryIdeal (hΦ j) (hcΦ j) hRank
      ∃ (ω : hB.toInvertibleSheaf ≅ canonicalBundle ℂ X[Φ j] 2)
        (hTotal : ((B[Φ j,hcΦ j]).comap (f j)).IsEffectiveCartier)
        (hRam : letI := SmoothOfRelativeDimension.smooth 2 (X ↘ S)
          (ramificationIdealSheaf ℂ (f j)).IsEffectiveCartier),
        pullbackTopFormDivisor ℂ (f j) 2 hB ω hTotal hRam = -hD.toCartierDivisor) :
    letI : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
    ∃ (n : ℕ) (Z : Scheme) (T : BlowupTower X n Z)
      (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T),
      letI : IsIntegral Z := hT.isClosedPointTower.isIntegral (X ↘ S)
      letI : Z.Over S := ⟨T.toBase ≫ X ↘ S⟩
      letI : Smooth (Z ↘ S) := (hT.isClosedPointTower.smoothOfRelativeDimension (X ↘ S)).smooth
      letI : IsModification T.toBase :=
        hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
      ∀ j, let Ψ := projectiveSpace (b j) (Φ j).lattice
        ∃ (Ω : Fan (i j)) (J : Ω.IsSubdivision (Φ j)) (K : Ω.IsSubdivision Ψ)
          (g : Z ⟶ X[Ω]),
          Ω.IsRegular ∧
          Relation.ReflTransGen IsTwoRayStarSubdivision (Φ j) Ω ∧
          Relation.ReflTransGen IsTwoRayStarSubdivision Ψ Ω ∧
          g ≫ π[J] = T.toBase ≫ f j ∧
          (∀ (Δ : Fan (i j)) [Nonempty Δ.cones] (L : Ω.IsSubdivision Δ),
            letI : Nonempty (Φ j).cones := (hcΦ j).nonempty_cones
            (T.toBase ≫ f j).toRationalMap.comp
              ((Φ j).denseTorusPartialIso Δ).toRationalMap = (g ≫ π[L]).toRationalMap) ∧
          let e := planeIso(b j,(Φ j).lattice)
          let q := (g ≫ π[K]) ≫ e.hom
          ∃ (m : ℕ) (W : Scheme) (U : BlowupTower P m W) (a : Z ≅ W),
            IsClosedPointTower P U ∧ a.hom ≫ U.toBase = q ∧
            ∃ hover : q ≫ P ↘ S = Z ↘ S,
              letI : q.IsOver S := ⟨hover⟩
              ((B[Ψ,isComplete_projectiveSpace (b j) (Φ j).lattice]).comap e.inv).comap q =
                (D.comap T.toBase).radical * ramificationIdealSheaf ℂ q := by
  let Ψ j := projectiveSpace (b j) (Φ j).lattice
  have hΨ j : (Ψ j).IsRegular := isRegular_projectiveSpace (b j) (Φ j).lattice
  have hcΨ j : (Ψ j).IsComplete := isComplete_projectiveSpace (b j) (Φ j).lattice
  obtain ⟨n, Z, T, hT, h⟩ := exists_common_nodal_resolution_of_toric_changes
    b hΦ hcΦ hΨ hcΨ f hD hN hdiv
  let : Z.Over S := ⟨T.toBase ≫ X ↘ S⟩
  let : SmoothOfRelativeDimension 2 (Z ↘ S) :=
    hT.isClosedPointTower.smoothOfRelativeDimension (X ↘ S)
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let : IsIntegral Z := hT.isClosedPointTower.isIntegral (X ↘ S)
  let : Z.IsProjectiveOver ℂ := T.isProjectiveOver ℂ
  refine ⟨n, Z, T, hT, fun j ↦ ?_⟩
  obtain ⟨Ω, J, K, g, hΩ, hchain, hchain', hproj, hΔ⟩ := h j
  refine ⟨Ω, J, K, g, hΩ, hchain, hchain', hproj, fun Δ _ L ↦ (hΔ Δ L).1, ?_⟩
  let : Nonempty (Ψ j).cones := (hcΨ j).nonempty_cones
  obtain ⟨hover, hp⟩ := (hΔ (Ψ j) K).2
  let p := g ≫ π[K]
  let : p.IsOver S := ⟨hover⟩
  obtain ⟨hMod, hpole⟩ := hp (hΨ j)
  let : IsModification p := hMod
  exact factor_plane_projection (b j) (Φ j).lattice p hpole

end TauCeti.Toric.Fan
