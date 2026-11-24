/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
public import QPainleve.Geometry.Toric.Fan.Logarithmic.ToricChange
public import TauCeti.AlgebraicGeometry.Noetherian

import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.PoleIdeal
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import QPainleve.Geometry.Toric.Fan.Logarithmic.Subdivision
import QPainleve.Geometry.Toric.Fan.Separated
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# Common nodal resolutions for changes of toric targets

When several prescribed birational morphisms have the same logarithmic pole boundary,
one nodal refinement resolves the toric changes at all their targets. The projections
to all intermediate fans represent the prescribed rational composites. The original
morphisms are recovered by composition with the toric subdivision projections.

In the plane reduction of [Lutz's Theorem 8.4][HKL], the two changes of toric target
are made at opposite ends of the specified map. Their regular projections must be
available on the same refinement so that the reduced plane map has the same pole
boundary on both sides.

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

variable {X : Scheme} [X.Over S] [IsIntegral X] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)] {D : X.IdealSheafData}

private theorem resolved_toric_projection
    {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
    {Φ Ω Δ : Fan i} [Nonempty Φ.cones] [Nonempty Ω.cones] [Nonempty Δ.cones]
    (J : Ω.IsSubdivision Φ) (L : Ω.IsSubdivision Δ)
    (hΦ : Φ.IsRegular) (hΩ : Ω.IsRegular) (hc : Φ.IsComplete)
    (hRank : Module.finrank ℤ N = 2)
    {Z : Scheme} [IsIntegral Z] [Z.Over S] [Z.IsProjectiveOver ℂ]
    [SmoothOfRelativeDimension 2 (Z ↘ S)]
    (g : Z ⟶ X[Ω]) [IsDominant g] (p : Z ⟶ X[Φ]) [IsModification p] [p.IsOver S]
    (he : g ≫ π[J] = p) (P : Z.IdealSheafData)
    (hPole : letI : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 _
      (B[Φ,hc]).comap p = P * ramificationIdealSheaf ℂ p) :
    let q := g ≫ π[L]
    p.toRationalMap.comp (Φ.denseTorusPartialIso Δ).toRationalMap = q.toRationalMap ∧
    ∃ hOver : q ≫ s[Δ] = Z ↘ S,
      letI : q.IsOver S := ⟨hOver⟩
      letI : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 (Z ↘ S)
      Δ.IsRegular → IsModification q ∧ (Δ.boundaryIdeal inferInstance).comap q =
        P * ramificationIdealSheaf ℂ q := by
  subst p
  have hg : g ≫ s[Ω] = Z ↘ S := by
    rw [← J.toFanHom.algebraicMap_comp_algebraicRealizationStructureMap, ← Category.assoc,
      ← Φ.algebraicRealization_over, comp_over]
  let : g.IsOver S := ⟨hg⟩
  have hOver : (g ≫ π[L]) ≫ s[Δ] = Z ↘ S := by
    rw [Category.assoc, L.toFanHom.algebraicMap_comp_algebraicRealizationStructureMap, hg]
  have hrat := J.comp_denseTorusPartialIso L g
  let q := g ≫ π[L]
  have : IsProper (q ≫ s[Δ]) := hOver.symm ▸ inferInstanceAs (IsProper (Z ↘ S))
  let : IsProper q := IsProper.of_comp q s[Δ]
  refine ⟨hrat, hOver, fun hΔ ↦ ⟨?_, ?_⟩⟩
  · exact IsModification.of_resolved_partialIso (g ≫ π[J]) (Φ.denseTorusPartialIso Δ) q hrat
  · exact (comap_boundaryIdeal_eq_mul_ramificationIdealSheaf_iff_of_common_subdivision
      J L hΦ hΔ hΩ hc hRank g P).mp hPole

/-- A finite family of specified birational morphisms to complete regular toric
surfaces with common pole divisor `-D` admits simultaneous changes of toric target.
The lattices may vary with the index. One nodal blowup tower resolves all intermediate
fans on both sides of each common fan, preserving the specified morphisms. Every
regular coarsening yields a modification with pole ideal the reduced total boundary. -/
theorem exists_common_nodal_resolution_of_toric_changes
    {ι : Type*} [Finite ι] {N V : ι → Type}
    [∀ j, AddCommGroup (N j)] [∀ j, AddCommGroup (V j)] [∀ j, Module ℝ (V j)]
    {i : ∀ j, N j →+ V j} {Φ Ψ : ∀ j, Fan (i j)}
    (b : ∀ j, Module.Basis (Fin 2) ℤ (N j))
    (hΦ : ∀ j, (Φ j).IsRegular) (hcΦ : ∀ j, (Φ j).IsComplete)
    (hΨ : ∀ j, (Ψ j).IsRegular) (hcΨ : ∀ j, (Ψ j).IsComplete)
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
      letI : SmoothOfRelativeDimension 2 (Z ↘ S) :=
        hT.isClosedPointTower.smoothOfRelativeDimension (X ↘ S)
      letI : IsModification T.toBase :=
        hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
      ∀ j, ∃ (Ω : Fan (i j)) (J : Ω.IsSubdivision (Φ j)) (_ : Ω.IsSubdivision (Ψ j))
        (g : Z ⟶ X[Ω]),
        Ω.IsRegular ∧
        Relation.ReflTransGen IsTwoRayStarSubdivision (Φ j) Ω ∧
        Relation.ReflTransGen IsTwoRayStarSubdivision (Ψ j) Ω ∧
        g ≫ π[J] = T.toBase ≫ f j ∧
        ∀ (Δ : Fan (i j)) [Nonempty Δ.cones] (L : Ω.IsSubdivision Δ),
          letI : Nonempty (Φ j).cones := (hcΦ j).nonempty_cones
          let q := g ≫ π[L]
          (T.toBase ≫ f j).toRationalMap.comp ((Φ j).denseTorusPartialIso Δ).toRationalMap =
            q.toRationalMap ∧
          ∃ hOver : q ≫ s[Δ] = Z ↘ S,
            letI : q.IsOver S := ⟨hOver⟩
            letI : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 (Z ↘ S)
            Δ.IsRegular → IsModification q ∧
              (Δ.boundaryIdeal inferInstance).comap q =
                (D.comap T.toBase).radical * ramificationIdealSheaf ℂ q := by
  classical
  let := Fintype.ofFinite ι
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  choose ω hTotal hRam hdiv using hdiv
  have hone j := exists_nodal_resolution_of_toric_change_of_pullbackTopFormDivisor
    (b j) (hΦ j) (hcΦ j) (hΨ j) (hcΨ j) (IsModification.birationalOver (f j))
    hD (ω j) (hTotal j) (hRam j) (hdiv j)
  choose Ω J K hΩ hchain hchain' n Y T g _ hg _ hT hproj _ using hone
  obtain ⟨m, Z, U, hU, hRef⟩ := exists_common_nodal_boundary_tower_refinement_finset
    D (X ↘ S) (𝟙 X) Finset.univ T (fun j _ ↦ hT j)
  refine ⟨m, Z, U, hU, fun j ↦ ?_⟩
  obtain ⟨_, W, L, e, hL, hbase, -⟩ := hRef j (Finset.mem_univ _)
  let : (Y j).Over S := ⟨(T j).toBase ≫ X ↘ S⟩
  let : SmoothOfRelativeDimension 2 (Y j ↘ S) :=
    (hT j).isClosedPointTower.smoothOfRelativeDimension (X ↘ S)
  let : IsIntegral (Y j) := (hT j).isClosedPointTower.isIntegral (X ↘ S)
  let : IsModification L.toBase :=
    hL.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Y j ↘ S)
  let : Z.Over S := ⟨U.toBase ≫ X ↘ S⟩
  let : SmoothOfRelativeDimension 2 (Z ↘ S) :=
    hU.isClosedPointTower.smoothOfRelativeDimension (X ↘ S)
  let : IsIntegral Z := hU.isClosedPointTower.isIntegral (X ↘ S)
  let : IsModification U.toBase :=
    hU.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
  let : U.toBase.IsOver S := ⟨rfl⟩
  let : Z.IsProjectiveOver ℂ := U.isProjectiveOver ℂ
  let : Nonempty (Φ j).cones := (hcΦ j).nonempty_cones
  let : Nonempty (Ω j).cones := (J j).nonempty_cones_of_nonempty inferInstance
  let g' := (e.hom ≫ L.toBase) ≫ g j
  let : IsDominant (g j) := hg j
  have : IsDominant g' := inferInstanceAs (IsDominant ((e.hom ≫ L.toBase) ≫ g j))
  have he : g' ≫ π[J j] = U.toBase ≫ f j := by
    simp only [g', Category.assoc, hproj j, reassoc_of% hbase]
  have hRank : Module.finrank ℤ (N j) = 2 :=
    (Module.finrank_eq_card_basis (b j)).trans (Fintype.card_fin 2)
  let : SmoothOfRelativeDimension 2 (X[Φ j] ↘ S) :=
    hRank ▸ (Φ j).smoothOfRelativeDimension_algebraicRealizationStructureMap (hΦ j)
  have hPole := (QPainleve.pullbackTopFormDivisor_eq_neg_iff ℂ (f j) 2
    ((Φ j).isEffectiveCartier_boundaryIdeal (hΦ j) (hcΦ j) hRank)
    (ω j) (hTotal j) hD (hRam j)).mp (hdiv j)
  have hPull :=
    (hU.comap_eq_mul_ramificationIdealSheaf_iff hD hN (f j) (hTotal j) (hRam j)).mpr hPole
  refine ⟨Ω j, J j, K j, g', hΩ j, hchain j, hchain' j, he, fun Δ _ M ↦ ?_⟩
  exact resolved_toric_projection (J j) M (hΦ j) (hΩ j) (hcΦ j) hRank
    g' (U.toBase ≫ f j) he _ hPull

end TauCeti.Toric.Fan
