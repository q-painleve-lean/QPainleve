/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Subdivision
public import QPainleve.Geometry.Toric.Fan.Hirzebruch.HorizontalNodes
public import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Recognition
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.ClosedPoint

import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Complexity
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Numbering
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Subdivision
import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Cycle
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Picard
import QPainleve.Geometry.Toric.Fan.Hirzebruch.Corner
import QPainleve.Geometry.Toric.Fan.Smooth
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Reduction of numbered anticanonical plane boundaries

A plane pair of boundary complexity zero is toric. For positive complexity, a blowup
at any numbered node gives a Hirzebruch-one model. Its reduced total boundary has
the same complexity and carries the oriented subdivision of the original cycle.
The exceptional section in the boundary ensures that a numbered node lies on a
fiber available for the next ruled transformation. This is the plane reduction in
[Gross, Hacking and Keel, Proposition 1.3][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "𝒫" => TauCeti.SymmetricAlgebra.homogeneousSubmodule ℂ (Fin 3 → ℂ)
local notation "P" => Proj 𝒫
local notation "X[" Φ "]" => Fan.algebraicRealization Φ
local notation "Π" => projectiveSpace b hi
local notation "boundaryMap(" D "," π ")" =>
  subschemeMap (radical (comap D π)) D π (le_map_iff_comap_le.mpr (le_radical _))

variable {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]
  {α : Type*} {p : α → (D.subscheme ↘ S).smoothLocus} {n : ℕ} [NeZero n]

/-- A numbered anticanonical cycle on a complex projective plane either has
complexity zero and is the toric boundary, or has positive complexity and
reduces to a Hirzebruch-one pair by blowing up the chosen node. The latter
pair has the same complexity, and the restricted projection preserves the
ordered branches of the original cycle. Its exceptional curve is the invariant
negative section, and a numbered node lies on a ruling fiber omitted from the
boundary. The chosen node may be a self-node. -/
theorem exists_toric_or_hirzebruch_one_of_numbered_plane_boundary
    (e : P ≅ X) [e.hom.IsOver S] (A : Scheme.NodalCycleNumbering p n)
    (hD : D.IsEffectiveCartier)
    (hcan : LineBundleClass.mk hD.toInvertibleSheaf = LineBundleClass.mk (canonicalBundle ℂ X 2))
    (j : ZMod n) :
    (D.boundaryComplexity = 0 ∧
      ∃ a : X[Π] ≅ X, a.hom.IsOver S ∧
        D.comap a.hom = (Π).boundaryIdeal (isComplete_projectiveSpace b hi).nonempty_cones) ∨
    (0 < D.boundaryComplexity ∧
      let I := (X.fromSpecResidueField (A.ambientNode j)).ker
      ∃ (Φ : Fan i) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (d : Basis (Fin 2) ℤ N)
        (r : Fin 4 ≃ Φ.Ray) (f : X[Φ] ≅ I.blowup)
        (hr : (fun k ↦ (r k).primitiveGenerator) = ![d 0, d 1, -d 0, (1 : ℤ) • d 0 - d 1]),
        letI : Nonempty Φ.cones := hc.nonempty_cones
        letI : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := by
          rw [algebraicRealization_over]
          exact ((finrank_eq_card_basis d).trans (Fintype.card_fin 2)) ▸
            Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
        letI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
        let π := f.hom ≫ I.blowupToBase
        let E := (D.comap π).radical
        let q := Φ.characterRuling (LinearMap.toAddMonoidHom (d.coord 1))
          (nonneg_or_nonpos_hirzebruch_ruling_character d 1 r hr)
        π.IsOver S ∧ I.comap π = Φ.rayBoundaryIdeal hΦ (r 0) ∧
        E ≤ Φ.rayBoundaryIdeal hΦ (r 0) ∧ E.boundaryComplexity = D.boundaryComplexity ∧
        ∃ (hE : E.IsEffectiveCartier) (hpre : PrestableFamily (E.subscheme ↘ S)),
          letI := hpre
          LineBundleClass.mk hE.toInvertibleSheaf =
            LineBundleClass.mk (canonicalBundle ℂ X[Φ] 2) ∧
          ∃ (B : Scheme.NodalCycleNumbering (Empty.elim : Empty → (E.subscheme ↘ S).smoothLocus)
            (n + 1)) (k : ZMod (n + 1)) (y : S ⟶ projectiveLine ℂ),
            (boundaryMap(D,π)).IsOver S ∧ (boundaryMap(D,π)).IsOrientedCycleSubdivision B A ∧
            IsClosed ({B.ambientNode k} : Set X[Φ]) ∧
            E.IsNodeOfReducedBoundary (X[Φ] ↘ S) (B.ambientNode k) ∧
            y ≫ (projectiveLine ℂ ↘ S) = 𝟙 S ∧ B.ambientNode k ∈ (y.ker.comap q).support ∧
            ¬ (y.ker.comap q).support ≤ E.support) := by
  let : X.IsProjectiveOver ℂ := Scheme.IsProjectiveOver.of_isClosedImmersion ℂ e.inv
  let : IsIntegral X := IsIntegral.of_isIso e.hom
  let : Module.Finite ℤ (Additive (LineBundleClass X)) :=
    Module.Finite.equiv (LineBundleClass.pullbackEquiv e.symm).toAdditive.toIntLinearEquiv
  by_cases hzero : D.boundaryComplexity = 0
  · obtain ⟨a, ha, hDa⟩ :=
      exists_toric_of_projectivePlane_boundaryComplexity_zero b hi e rfl A hD hcan hzero
    exact Or.inl ⟨hzero, a, ⟨ha.trans (algebraicRealization_over (Φ := Π)).symm⟩, hDa⟩
  have hpos := lt_of_le_of_ne (D.boundaryComplexity_nonneg_of_nodalCycleNumbering hD A)
    (Ne.symm hzero)
  refine Or.inr ⟨hpos, ?_⟩
  let a₀ := projectivePlaneIso b hi ≪≫ (Pi.basisFun ℂ (Fin 3)).polynomialProjIso
  let : a₀.hom.IsOver S := projectivePlaneIso_trans_polynomialProjIso_hom_isOver b hi _
  let a := a₀ ≪≫ e
  let : a.hom.IsOver S := inferInstanceAs ((a₀.hom ≫ e.hom).IsOver S)
  have hnodal : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S) := by
    rw [← D.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  obtain ⟨Φ, hΦ, hc, d, ρ, f, hgens, hρ, hπ, hI, hle, hE, hK, _⟩ :=
    exists_hirzebruch_one_model_of_plane_nodal_blowup b hi a hD hnodal
      (A.ambientNode j) (A.isClosed_ambientNode j)
      (A.isNodeOfReducedBoundary_ambientNode j rfl) hcan
  obtain ⟨r, hr⟩ := exists_rayEquiv_of_hirzebruch_ray_generators d 1
    (by simpa only [one_zsmul] using hgens)
  have hr₀ : r 0 = ρ := Ray.primitiveGenerator_injective
    ((by simpa using congrFun hr 0 : (r 0).primitiveGenerator = d 0).trans hρ.symm)
  let I := (X.fromSpecResidueField (A.ambientNode j)).ker
  have hT := isNodalBoundaryTower_numbered_node A j
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let π := f.hom ≫ I.blowupToBase
  let E := (D.comap π).radical
  have hproj : f.hom ≫ (BlowupTower.nil.snoc I).toBase = π := by simp [π]
  have hEq : E.boundaryComplexity = D.boundaryComplexity := by
    simpa only [E, ← hproj, boundaryComplexity_radical, comap_comp, boundaryComplexity_comap_iso]
      using hT.boundaryComplexity_comap hD
  obtain ⟨hpre, hnumber⟩ :=
    hT.exists_isOrientedCycleSubdivision_nodalBoundaryTower_of_iso hD A f hproj hπ
  obtain ⟨B, hBover, hB⟩ := hnumber (Empty.elim : Empty → (E.subscheme ↘ S).smoothLocus)
  let : PrestableFamily (E.subscheme ↘ S) := hpre
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : X[Φ].IsProjectiveOver ℂ := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc d
  let : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := by
    rw [algebraicRealization_over]
    exact ((finrank_eq_card_basis d).trans (Fintype.card_fin 2)) ▸
      Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  have hle' : E ≤ Φ.rayBoundaryIdeal hΦ (r 0) := hr₀.symm ▸ hle
  have hsection : (Φ.rayBoundaryPoint hΦ (r 0) : X[Φ]) ∈ E.support := support_antitone hle' (by
    rw [rayBoundaryIdeal_def, ← SetLike.mem_coe, coe_support_vanishingIdeal]
    exact subset_closure (Set.mem_singleton _))
  obtain ⟨k, y, hy⟩ := exists_hirzebruch_node_on_omitted_fiber_of_section_mem_support
    d 1 hΦ hc r hr B hE hK rfl (hEq.symm ▸ hpos) hsection
  exact ⟨Φ, hΦ, hc, d, r, f, hr, hπ, hr₀.symm ▸ hI, hle', hEq, hE, hpre, hK,
    B, k, y, hBover, hB, hy⟩

end TauCeti.Toric.Fan
