/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.ZeroComplexity
public import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Recognition
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Transport

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Toric recognition over the projective plane

A complexity-zero anticanonical cycle on a specified point-blowup tower over
the projective plane makes the entire tower toric. The schematic image is a
coordinate triangle in suitable projective coordinates. The nodal blowups
then realize a subdivision of its fan, with the original tower projection.

This is the projective-plane case of the complexity-zero recognition used
in the proof of [Gross, Hacking and Keel, Theorem 1.8][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData LineBundleClass

namespace TauCeti.Toric.Fan

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type) [Field k] [IsAlgClosed k] [NeZero (2 : k)]

local notation "S" => Spec (CommRingCat.of k)
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (ULift (Fin 3)) k
local notation "P" => Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Fin 3 → k))
local notation "K[" X "]" => LineBundleClass.mk (QPainleve.canonicalBundle k X 2)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
  {X Y Z : Scheme} [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k))]
  {n : ℕ} {T : BlowupTower X n Y} {B : Z.IdealSheafData}
  [PrestableFamily (B.subscheme ↘ Spec (.of k))]
  {m : ℕ} [NeZero m] {ι : Type*} {a : ι → (B.subscheme ↘ Spec (.of k)).smoothLocus}

/-- A numbered anticanonical boundary of complexity zero over a specified
closed-point tower with projective-plane base is toric. The base comparison
identifies the schematic image with the coordinate triangle. The comparison
at the top identifies the boundary ideal, and the entire projection is the
morphism of the resulting fan subdivision. -/
theorem exists_toric_of_projectivePlane_tower_boundaryComplexity_zero
    (p : X ≅ Proj 𝒜) (hp : p.hom ≫ Proj.toSpecCoeff 𝒜 = X ↘ S)
    (hT : IsClosedPointTower X T) (e : Z ≅ Y) {f : Z ⟶ X} [f.IsOver S]
    (he : e.hom ≫ T.toBase = f) (hB : B.IsEffectiveCartier)
    (A : Scheme.NodalCycleNumbering (k := k) (X := B.subscheme) a m)
    (hcan : LineBundleClass.mk hB.toInvertibleSheaf = K[Z])
    (hzero : B.boundaryComplexity = 0) :
    let Φ := projectiveSpace b hi
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (hΨ : Ψ.IsComplete) (H : Ψ.IsSubdivision Φ)
      (q : Φ.finiteFanScheme k ≅ X) (r : Ψ.finiteFanScheme k ≅ Z),
      q.hom ≫ X ↘ S = Φ.finiteFanSchemeToSpec k ∧
      (B.map f).comap q.hom =
        Φ.toricBoundaryIdeal k (isComplete_projectiveSpace b hi).nonempty_cones ∧
      r.hom ≫ f = H.toFanHom.finiteFanSchemeHom k ≫ q.hom ∧
      r.hom ≫ Z ↘ S = Ψ.finiteFanSchemeToSpec k ∧
      B.comap r.hom = Ψ.toricBoundaryIdeal k hΨ.nonempty_cones := by
  let c := (Pi.basisFun k (Fin 3)).reindex Equiv.ulift.symm
  let d : X ≅ P := p ≪≫ c.polynomialProjIso
  have hd : d.hom ≫ P ↘ S = X ↘ S := by
    rw [Iso.trans_hom, Category.assoc, SymmetricAlgebra.over_eq_projToSpec,
      Basis.polynomialProjIso_hom_over, hp]
  let : d.hom.IsOver S := ⟨hd⟩
  let : d.symm.hom.IsOver S := ⟨by rw [Iso.symm_hom, ← hd, Iso.inv_hom_id_assoc]⟩
  let : IsIntegral X := IsIntegral.of_isIso d.inv
  let : X.IsProjectiveOver k := Scheme.IsProjectiveOver.of_isClosedImmersion k d.hom
  let : SmoothOfRelativeDimension 2 (X ↘ S) := by
    let : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{0} 2) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange 2).respectsIso
    rw [← hd, MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 2)]
    infer_instance
  let : Module.Finite ℤ (Additive (LineBundleClass X)) :=
    Module.Finite.of_surjective _ (pullbackEquiv d).toAdditive.toIntLinearEquiv.surjective
  obtain ⟨hU, htotal, hzeroD, hD, hpre, hcanD, l, hl, C, -, -, -⟩ :=
    hT.exists_numbering_of_boundaryComplexity_eq_zero_of_iso e he hB A hcan hzero
  let := hpre
  let := hl
  let Φ := projectiveSpace b hi
  let hc := isComplete_projectiveSpace b hi
  obtain ⟨q, hq, hBq⟩ := exists_toric_of_projectivePlane_boundaryComplexity_zero k
    b hi d.symm (B.map f).over_eq_subschemeι_comp C hD hcanD hzeroD
  have hsupport := congrArg Scheme.IdealSheafData.support hBq
  obtain ⟨Ψ, hreg, hc', H, t, ht, htD⟩ :=
    exists_toric_subdivision_of_nodal_boundary_tower_of_iso k (isRegular_projectiveSpace b hi) hc
      ((finrank_eq_card_basis b).trans (Fintype.card_fin 2)) hU q hq hsupport
  let r := t ≪≫ e.symm
  have hr : r.hom ≫ f = t.hom ≫ T.toBase := by
    simp only [r, Iso.trans_hom, Iso.symm_hom, ← he, Category.assoc, Iso.inv_hom_id_assoc]
  have hproj := hr.trans ht
  refine ⟨Ψ, hreg, hc', H, q, r, hq, hBq, hproj, ?_, ?_⟩
  · rw [← comp_over f S, reassoc_of% hproj, hq,
      FanHom.finiteFanSchemeHom_comp_finiteFanSchemeToSpec]
  · rw [← htotal, ← radical_comap_of_isOpenImmersion, ← comap_comp, hr, comap_comp,
      radical_comap_of_isOpenImmersion]
    exact htD

end TauCeti.Toric.Fan
