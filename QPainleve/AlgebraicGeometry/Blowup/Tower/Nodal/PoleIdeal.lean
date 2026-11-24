/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Canonical
public import QPainleve.AlgebraicGeometry.Modules.Differentials.PoleIdeal

import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Common resolutions preserving pole ideals

A nodal refinement keeps the pole ideal equal to the reduced total boundary.
This allows pole factorizations for specified morphisms on different nodal
towers to be carried to one common refinement. For a single refinement, the
pole factorization also descends to the original model.

Tracking the specified morphisms on a common nodal refinement is part of
the factorization of [Lutz, Theorem 8.4][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [IsIntegral X] [IsNoetherian X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] {D : X.IdealSheafData}

local notation "S" => Spec (CommRingCat.of k)
local notation "s" => X ↘ S

section

variable {n : ℕ} {Y : Scheme.{u}} {T : BlowupTower X n Y}
  (hT : IsNodalBoundaryTower D (X ↘ Spec (.of k)) (𝟙 X) T)
  (hD : D.IsEffectiveCartier)
  (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ Spec (.of k)))
include hT hD hN

/-- The pole factorization for a nodal tower also holds for a specified projection
identified with the tower by an isomorphism of sources. -/
theorem IsNodalBoundaryTower.comap_eq_radical_mul_ramificationIdealSheaf_of_iso
    {W : Scheme.{u}} [W.Over S] [SmoothOfRelativeDimension 2 (W ↘ S)]
    (e : W ≅ Y) (f : W ⟶ X) [f.IsOver S] (he : e.hom ≫ T.toBase = f) :
    letI := SmoothOfRelativeDimension.smooth 2 (W ↘ S)
    D.comap f = (D.comap f).radical * ramificationIdealSheaf k f := by
  have := SmoothOfRelativeDimension.smooth 2 (W ↘ S)
  have h := congrArg (fun I : Y.IdealSheafData ↦ I.comap e.hom)
    (hT.comap_toBase_eq_radical_mul_ramification hD hN)
  rwa [comap_mul, ← radical_comap_of_isOpenImmersion, ← comap_comp, he,
    hT.isClosedPointTower.comap_ramificationIdealSheafToBase k e he] at h

/-- Refining by nodal blowups preserves and reflects the assertion that a specified
morphism pulls back a pole ideal to the reduced boundary with no zeros. -/
theorem IsNodalBoundaryTower.comap_eq_mul_ramificationIdealSheaf_iff
    {W : Scheme.{u}} [W.Over S] [SmoothOfRelativeDimension 2 (W ↘ S)]
    (g : X ⟶ W) [g.IsOver S] {E : W.IdealSheafData} (hE : (E.comap g).IsEffectiveCartier) :
    letI : Y.Over S := ⟨T.toBase ≫ s⟩
    letI : T.toBase.IsOver S := ⟨rfl⟩
    letI : Smooth (Y ↘ S) := (hT.isClosedPointTower.smoothOfRelativeDimension s).smooth
    letI := SmoothOfRelativeDimension.smooth 2 s
    (ramificationIdealSheaf k g).IsEffectiveCartier →
      (E.comap (T.toBase ≫ g) = (D.comap T.toBase).radical *
          ramificationIdealSheaf k (T.toBase ≫ g) ↔
        E.comap g = D * ramificationIdealSheaf k g) := by
  let : Y.Over S := ⟨T.toBase ≫ s⟩
  have : T.toBase.IsOver S := ⟨rfl⟩
  have : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.isClosedPointTower.smoothOfRelativeDimension s
  have : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 _
  have : IsRegular X := IsRegular.of_smooth s
  have := hT.isClosedPointTower.isIntegral s
  have := hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two s
  intro hg
  exact comap_eq_mul_ramificationIdealSheaf_comp_iff_of_isModification k T.toBase g 2 hE hD hg
    ((hT.comap_toBase_eq_radical_mul_ramification hD hN).trans
      (congrArg ((D.comap T.toBase).radical * ·)
        (hT.isClosedPointTower.ramificationIdealSheafToBase_def k)))

end

private theorem refinement_comap_eq_radical_mul_ramificationIdealSheaf
    {a b c : ℕ} {Y Z A : Scheme.{u}}
    {T : BlowupTower X a Y} {U : BlowupTower X b Z} {L : BlowupTower Y c A}
    (hT : IsNodalBoundaryTower D s (𝟙 X) T)
    (hU : IsNodalBoundaryTower D s (𝟙 X) U)
    (hL : IsNodalBoundaryTower D s (T.toBase ≫ 𝟙 X) L)
    (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (e : Z ≅ A) (he : U.toBase = e.hom ≫ L.toBase ≫ T.toBase) :
    letI : Y.Over S := ⟨T.toBase ≫ s⟩
    letI : Z.Over S := ⟨U.toBase ≫ s⟩
    let f := e.hom ≫ L.toBase
    letI : f.IsOver S := ⟨(Category.assoc _ _ _).trans ((reassoc_of% he) s).symm⟩
    letI : Smooth (Z ↘ S) := (hU.isClosedPointTower.smoothOfRelativeDimension s).smooth
    (D.comap T.toBase).radical.comap f =
      (D.comap U.toBase).radical * ramificationIdealSheaf k f := by
  let : Y.Over S := ⟨T.toBase ≫ s⟩
  let : Z.Over S := ⟨U.toBase ≫ s⟩
  have : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.isClosedPointTower.smoothOfRelativeDimension s
  have : SmoothOfRelativeDimension 2 (Z ↘ S) := hU.isClosedPointTower.smoothOfRelativeDimension s
  let P := (D.comap T.toBase).radical
  let f := e.hom ≫ L.toBase
  have : f.IsOver S := ⟨(Category.assoc _ _ _).trans ((reassoc_of% he) s).symm⟩
  have : IsIntegral Y := hT.isClosedPointTower.isIntegral s
  have : IsNoetherian Y := T.isNoetherian
  have hL' : IsNodalBoundaryTower P (Y ↘ S) (𝟙 Y) L :=
    hL.congr (by rw [Category.comp_id, Category.id_comp]; rfl)
      (by simp only [Category.comp_id, comap_id, P, support_radical])
  obtain ⟨hP, hNP⟩ := hT.radical_comap_toBase hD hN
  have hfac := hL'.comap_eq_radical_mul_ramificationIdealSheaf_of_iso hP hNP e f rfl
  have hrad : (P.comap f).radical = (D.comap U.toBase).radical := by
    rw [← vanishingIdeal_support, ← vanishingIdeal_support (I := D.comap U.toBase)]
    simp only [support_comap P, P, support_radical, ← support_comap (D.comap T.toBase),
      ← comap_comp, f, Category.assoc, ← he]
  rwa [hrad] at hfac

/-- A finite family of specified morphisms on nodal refinements admits a common nodal
refinement on which all pole factorizations hold. Each specified morphism is
precomposed with the projection to its original tower. -/
theorem exists_common_nodal_boundary_tower_refinement_of_poleIdeals
    (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    {ι : Type*} (F : Finset ι) {n : ι → ℕ} {Y W : ι → Scheme.{u}}
    [∀ i, (W i).Over S] [∀ i, SmoothOfRelativeDimension 2 (W i ↘ S)]
    (T : ∀ i, BlowupTower X (n i) (Y i))
    (hT : ∀ i ∈ F, IsNodalBoundaryTower D s (𝟙 X) (T i))
    (g : ∀ i, Y i ⟶ W i) (hg : ∀ i ∈ F, g i ≫ (W i ↘ S) = (T i).toBase ≫ s)
    (E : ∀ i, (W i).IdealSheafData)
    (hpole : ∀ (i) (hi : i ∈ F),
      letI : (Y i).Over S := ⟨(T i).toBase ≫ s⟩
      letI : (g i).IsOver S := ⟨hg i hi⟩
      letI : Smooth (Y i ↘ S) := ((hT i hi).isClosedPointTower.smoothOfRelativeDimension s).smooth
      (E i).comap (g i) = (D.comap (T i).toBase).radical * ramificationIdealSheaf k (g i)) :
    ∃ (m : ℕ) (Z : Scheme.{u}) (U : BlowupTower X m Z)
      (hU : IsNodalBoundaryTower D s (𝟙 X) U),
      ∀ (i) (hi : i ∈ F), ∃ (a : ℕ) (A : Scheme.{u}) (L : BlowupTower (Y i) a A) (e : Z ≅ A)
        (he : U.toBase = e.hom ≫ L.toBase ≫ (T i).toBase),
        IsNodalBoundaryTower D s ((T i).toBase ≫ 𝟙 X) L ∧
        (letI : Z.Over S := ⟨U.toBase ≫ s⟩
         let f := (e.hom ≫ L.toBase) ≫ g i
         letI : f.IsOver S := ⟨(Category.assoc _ _ _).trans
           ((congrArg ((e.hom ≫ L.toBase) ≫ ·) (hg i hi)).trans
             ((Category.assoc _ _ _).trans ((reassoc_of% he) s).symm))⟩
         letI : Smooth (Z ↘ S) := (hU.isClosedPointTower.smoothOfRelativeDimension s).smooth
         (E i).comap f = (D.comap U.toBase).radical * ramificationIdealSheaf k f) := by
  obtain ⟨m, Z, U, hU, href⟩ :=
    exists_common_nodal_boundary_tower_refinement_finset D s (𝟙 X) F T hT
  refine ⟨m, Z, U, hU, fun i hi ↦ ?_⟩
  obtain ⟨a, A, L, e, hL, he, _⟩ := href i hi
  refine ⟨a, A, L, e, he, hL, ?_⟩
  let : (Y i).Over S := ⟨(T i).toBase ≫ s⟩
  let : Z.Over S := ⟨U.toBase ≫ s⟩
  have : (g i).IsOver S := ⟨hg i hi⟩
  have : SmoothOfRelativeDimension 2 (Y i ↘ S) :=
    (hT i hi).isClosedPointTower.smoothOfRelativeDimension s
  have : SmoothOfRelativeDimension 2 (Z ↘ S) := hU.isClosedPointTower.smoothOfRelativeDimension s
  let f := e.hom ≫ L.toBase
  have : f.IsOver S := ⟨(Category.assoc _ _ _).trans ((reassoc_of% he) s).symm⟩
  have hfac := refinement_comap_eq_radical_mul_ramificationIdealSheaf (hT i hi) hU hL hD hN e he
  exact comap_eq_mul_ramificationIdealSheaf_comp k f (g i) 2 (hpole i hi) hfac

end QPainleve.BlowupTower
