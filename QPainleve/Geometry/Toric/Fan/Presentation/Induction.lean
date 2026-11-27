/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Cycle
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import QPainleve.Geometry.Toric.Fan.Presentation.Basic

import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Numbering
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.MinimalModel
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
import QPainleve.Geometry.Toric.Fan.Hirzebruch.BoundarySplit
import QPainleve.Geometry.Toric.Fan.Hirzebruch.Classification
import QPainleve.Geometry.Toric.Fan.Hirzebruch.PositiveComplexity
import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
import QPainleve.Geometry.Toric.Fan.Presentation.NodalBlowup
import QPainleve.Geometry.Toric.Fan.Presentation.NodalReduction
import QPainleve.Geometry.Toric.Fan.Presentation.PointTower
import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Reduction
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective

/-!
# Induction for toric presentations of rational anticanonical pairs

The minimal-model tower reduces existence of toric presentations to the projective
plane and the ruled surfaces. On the plane, blowing up a node passes to the ruled
case unless the plane boundary is already toric. On a Hirzebruch surface, a nodal
blowup followed by an internal contraction reduces boundary complexity by one.
The presentations obtained at the end of the induction lift through the specified
blowups and contractions.

This is the reduction used in [Gross, Hacking and Keel, Proposition 1.3][GHK].
The ruled induction uses the identification of split projective bundles with
Hirzebruch surfaces and the toric recognition of their complexity-zero boundaries.

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [NeZero (2 : k₀)]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "K[" X "]" => LineBundleClass.mk (canonicalBundle k₀ X 2)
local notation "J[" x "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ x)
local notation "T[" x "]" => BlowupTower.nil.snoc J[x]
local notation "X[" Φ "]" => Fan.finiteFanScheme k₀ Φ

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (b : Basis (Fin 2) ℤ N)

omit [IsAlgClosed k₀] [NeZero (2 : k₀)] in
private theorem smoothOfRelativeDimension_two {Φ : Fan i} (hΦ : Φ.IsRegular)
    (d : Basis (Fin 2) ℤ N) : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := by
  rw [finiteFanScheme_over]
  exact ((finrank_eq_card_basis d).trans (Fintype.card_fin 2)) ▸
    Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ

variable {b}

private theorem exists_numbering_on_fan_model
    {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
    {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]
    {n : ℕ} [NeZero n] {ι : Type} {p : ι → (D.subscheme ↘ S).smoothLocus}
    (A : Scheme.NodalCycleNumbering p n) (hD : D.IsEffectiveCartier)
    (hK : LineBundleClass.mk hD.toInvertibleSheaf = K[X])
    {Φ : Fan i} (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (d : Basis (Fin 2) ℤ N)
    (e : X[Φ] ≅ X) (he : e.hom ≫ X ↘ S = (Φ.finiteFanSchemeToSpec k₀)) :
    letI : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := smoothOfRelativeDimension_two k₀ hΦ d
    ∃ (hE : (D.comap e.hom).IsEffectiveCartier)
      (_ : PrestableFamily ((D.comap e.hom).subscheme ↘ S)),
      LineBundleClass.mk hE.toInvertibleSheaf = K[X[Φ]] ∧
      ∃ (m : ℕ) (_ : NeZero m),
        Nonempty (Scheme.NodalCycleNumbering
          (PEmpty.elim : PEmpty.{1} → ((D.comap e.hom).subscheme ↘ S).smoothLocus) m) := by
  let : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := smoothOfRelativeDimension_two k₀ hΦ d
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : X[Φ].IsProjectiveOver k₀ := Φ.isProjectiveOver_finiteFanScheme_of_isComplete k₀ hΦ hc d
  let : Smooth (X[Φ] ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have he' : e.inv ≫ X[Φ] ↘ S = X ↘ S := by
    rw [finiteFanScheme_over, ← he, Iso.inv_hom_id_assoc]
  let : e.inv.IsOver S := ⟨he'⟩
  obtain ⟨hE, hpre, hcan, m, hm, B, -, -, -⟩ :=
    IsClosedPointTower.exists_numbering_of_anticanonical_boundary_tower_blowdown_of_iso
      (T := BlowupTower.nil (X := X[Φ])) .nil e.symm (f := e.inv) (by simp) hD A hK
  have hmap : D.map e.inv = D.comap e.hom := by
    simpa only [← comap_comp, Iso.inv_hom_id, comap_id, Scheme.Hom.ker_eq_bot_of_isIso,
      sup_bot_eq] using map_comap_of_isClosedImmersion (D.comap e.hom) e.inv
  revert hE hpre hcan B
  rw [hmap]
  intro hE hpre hcan B
  exact ⟨hE, hpre, hcan, m, hm, ⟨B⟩⟩

private theorem hasToricPresentation_of_hirzebruch
    {Φ : Fan i} (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (d : Basis (Fin 2) ℤ N)
    (k : ℕ) (r : Fin 4 ≃ Φ.Ray)
    (hr : (fun j ↦ (r j).primitiveGenerator) = ![d 0, d 1, -d 0, (k : ℤ) • d 0 - d 1])
    [SmoothOfRelativeDimension 2 (X[Φ] ↘ S)]
    {D : (X[Φ]).IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]
    {n : ℕ} [NeZero n] {ι : Type} {p : ι → (D.subscheme ↘ S).smoothLocus}
    (A : Scheme.NodalCycleNumbering p n) (hD : D.IsEffectiveCartier)
    (hK : LineBundleClass.mk hD.toInvertibleSheaf = K[X[Φ]]) :
    D.HasToricPresentation (X[Φ] ↘ S) b i := by
  generalize hl : D.boundaryComplexity.toNat = l
  induction l using Nat.strong_induction_on generalizing Φ d k n ι with
  | ind l ih =>
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : X[Φ].IsProjectiveOver k₀ := Φ.isProjectiveOver_finiteFanScheme_of_isComplete k₀ hΦ hc d
    let : Smooth (X[Φ] ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : IsNoetherian X[Φ] := isNoetherian_of_finiteType (X[Φ] ↘ S)
    let hRat : Scheme.IsRationalOver (X[Φ] ↘ S) :=
      isRationalOver_of_hirzebruch k₀ d (k : ℤ) hΦ r hr hc
    let : IsIntegral X[Φ] := hRat.isIntegral_of_smooth
    let : Module.Finite ℤ (Additive (LineBundleClass X[Φ])) :=
      Module.Finite.of_basis (Φ.hirzebruchPicardBasis k₀ d (k : ℤ) hΦ r hr)
    by_cases hzero : D.boundaryComplexity = 0
    · let : IsReduced D.subscheme :=
        (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := D.subscheme ↘ S)).isReduced
      obtain ⟨Ψ, hΨ, hcΨ, e, he, hE⟩ :=
        exists_toric_of_hirzebruch_boundaryComplexity_zero k₀ d (k : ℤ) hΦ hc r hr
          (Int.natCast_nonneg k) hD hzero hK
      exact hasToricPresentation_of_toric_boundary b hΨ hcΨ e
        (he.trans (finiteFanScheme_over k₀ (Φ := Ψ))) hE
    have hq := D.boundaryComplexity_nonneg_of_nodalCycleNumbering hD A
    have hpos := lt_of_le_of_ne hq (Ne.symm hzero)
    obtain ⟨j, Y, s, y, u, f, hSm, hT, hInt, hProj, hy, hg, hOmit, hfOver, hfFlat, hfiber,
      hE, hKE, hdrop, hpre, ⟨B⟩⟩ :=
      exists_hirzebruch_positive_complexity_reduction k₀ d hΦ hc r hr hD hK A
        (Int.natCast_nonneg k) hpos
    let : Y.Over S := ⟨s⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hSm
    let : IsIntegral Y := hInt
    let : Y.IsProjectiveOver k₀ := hProj
    let : f.IsOver S := hfOver
    let : Flat f := hfFlat
    let : Scheme.IsRationalOver (Y ↘ S) :=
      hT.isClosedPointTower.isRationalOver_of_common_pointBlowup (t := s) hy u
        (by simpa only [Category.assoc, toBase_snoc, toBase_nil, Category.comp_id] using hg)
    obtain ⟨Ψ, hΨ, hcΨ, k', r', hr', e, hruling⟩ :=
      f.exists_hirzebruch_model_of_projectiveLine_fibers k₀ b Φ.lattice hfiber
    have he : e.hom ≫ Y ↘ S = (Ψ.finiteFanSchemeToSpec k₀) := by
      rw [← comp_over f S, ← Category.assoc, hruling, comp_over, finiteFanScheme_over]
    let g := u.hom ≫ J[y].blowupToBase
    let E := ((D.comap J[A.ambientNode j].blowupToBase).radical).map g
    let : PrestableFamily (E.subscheme ↘ S) := hpre
    obtain ⟨hE', hpre', hK', m, hm, ⟨C⟩⟩ := exists_numbering_on_fan_model k₀ B hE hKE hΨ hcΨ b e he
    let : PrestableFamily ((E.comap e.hom).subscheme ↘ S) := hpre'
    let : NeZero m := hm
    have hover : e.hom ≫ Y ↘ S = X[Ψ] ↘ S := he.trans (finiteFanScheme_over k₀ (Φ := Ψ)).symm
    -- Complexity is unchanged by the new model and drops strictly under the link.
    have hlt : (E.comap e.hom).boundaryComplexity.toNat < l := by
      have hdrop' : E.boundaryComplexity + 1 = D.boundaryComplexity := hdrop
      rw [boundaryComplexity_comap_iso, ← hl]
      omega
    let : SmoothOfRelativeDimension 2 (X[Ψ] ↘ S) := smoothOfRelativeDimension_two k₀ hΨ b
    have hEp := (ih _ hlt hΨ hcΨ b k' r' hr' C hE' hK' rfl).of_comap_iso
      (e := e.symm) (by rw [Iso.symm_hom, ← hover, Iso.inv_hom_id_assoc])
    exact hasToricPresentation_of_nodal_blowup_and_internal_contraction k₀
      b hD hK hT hy u hg hOmit hEp

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "Π" => Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k₀ (Fin 3 → k₀))

private theorem hasToricPresentation_of_plane (hi : IsIntegralLattice i)
    {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
    {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]
    {n : ℕ} [NeZero n] {ι : Type} {p : ι → (D.subscheme ↘ S).smoothLocus}
    (A : Scheme.NodalCycleNumbering p n) (hD : D.IsEffectiveCartier)
    (hK : LineBundleClass.mk hD.toInvertibleSheaf = K[X])
    (a : Π ≅ X) [a.hom.IsOver S] :
    D.HasToricPresentation (X ↘ S) b i := by
  rcases exists_toric_or_hirzebruch_one_of_numbered_plane_boundary k₀ b hi a A hD hK 0 with
    ⟨-, e, hover, he⟩ | ⟨-, Φ, hΦ, hc, d, r, e, hr, hover, -, -, -, hE, hpre, hcan, B, _⟩
  · let Φ := projectiveSpace b hi
    exact hasToricPresentation_of_toric_boundary b (isRegular_projectiveSpace b hi)
      (isComplete_projectiveSpace b hi) e
      (hover.comp_over.trans (finiteFanScheme_over k₀ (Φ := Φ))) he
  · let E := (D.comap (e.hom ≫ J[A.ambientNode 0].blowupToBase)).radical
    let : PrestableFamily (E.subscheme ↘ S) := hpre
    let : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := smoothOfRelativeDimension_two k₀ hΦ d
    have hEp := hasToricPresentation_of_hirzebruch k₀ (b := b) hΦ hc d 1 r
      (by simpa only [Int.natCast_one] using hr) B hE hcan
    have hT := isNodalBoundaryTower_numbered_node A (0 : ZMod n)
    have hb : e.inv ≫ X[Φ] ↘ S = T[A.ambientNode 0].toBase ≫ X ↘ S := by
      simpa only [toBase_snoc, toBase_nil, Category.comp_id, ← Category.assoc,
        Iso.inv_hom_id, Category.id_comp] using (congrArg (e.inv ≫ ·) hover.comp_over).symm
    refine hasToricPresentation_of_nodal_tower b hT e.symm hb ?_ hEp
    rw [Iso.symm_hom, ← radical_comap_of_isOpenImmersion, support_radical, ← comap_comp,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      toBase_snoc, toBase_nil, Category.comp_id]

/-- Every numbered anticanonical cycle on a smooth projective rational
surface has a toric presentation in the prescribed lattice frame. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.hasToricPresentation_of_anticanonical_cycle
    {X : Scheme} [X.Over S] [X.IsProjectiveOver k₀] [SmoothOfRelativeDimension 2 (X ↘ S)]
    [Scheme.IsRationalOver (X ↘ S)]
    (D : X.IdealSheafData) [PrestableFamily (D.subscheme ↘ S)]
    {n : ℕ} [NeZero n] {ι : Type} {p : ι → (D.subscheme ↘ S).smoothLocus}
    (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    (A : Scheme.NodalCycleNumbering p n) (hD : D.IsEffectiveCartier)
    (hK : LineBundleClass.mk hD.toInvertibleSheaf = K[X]) :
    D.HasToricPresentation (X ↘ S) b i := by
  obtain ⟨Y, s, _, W, T, e, hproj, hsmooth, hrat, hmin, hT, he, -⟩ :=
    X.exists_isClosedPointTower_of_minimal_model k₀
  let : Y.Over S := ⟨s⟩
  let : Y.IsProjectiveOver k₀ := hproj
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hsmooth
  let : Scheme.IsRationalOver (Y ↘ S) := hrat
  let : Smooth s := SmoothOfRelativeDimension.smooth 2 s
  let : IsIntegral Y := hrat.isIntegral_of_smooth
  let f := e.hom ≫ T.toBase
  have hf : f ≫ s = X ↘ S := he
  let : f.IsOver S := ⟨hf⟩
  obtain ⟨hE, hPre, hKE, m, hm, B, -, -, -⟩ :=
    hT.exists_numbering_of_anticanonical_boundary_tower_blowdown_of_iso e (f := f) rfl hD A hK
  let E := D.map f
  let : PrestableFamily (E.subscheme ↘ S) := hPre
  let : NeZero m := hm
  have hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S) := by
    rw [← D.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  refine hT.hasToricPresentation_of_closedPointTower_of_iso k₀ e he hD hN hK ?_
  rcases Y.exists_iso_projectivePlane_or_hirzebruch k₀ b hi hmin with
    ⟨a, ha⟩ | ⟨Φ, hΦ, hc, k, r, a, -, hr, ha⟩
  · let d := a ≪≫ ((Pi.basisFun k₀ (Fin 3)).reindex Equiv.ulift.symm).polynomialProjIso
    have hd : d.hom ≫ Π ↘ S = Y ↘ S := by
      rw [Iso.trans_hom, Category.assoc, SymmetricAlgebra.over_eq_projToSpec,
        Basis.polynomialProjIso_hom_over, ha]
    let : d.symm.hom.IsOver S := ⟨by rw [Iso.symm_hom, ← hd, Iso.inv_hom_id_assoc]⟩
    exact hasToricPresentation_of_plane k₀ hi B hE hKE d.symm
  · obtain ⟨hE', hPre', hK', l, hl, ⟨C⟩⟩ := exists_numbering_on_fan_model k₀ B hE hKE hΦ hc b a ha
    let : PrestableFamily ((E.comap a.hom).subscheme ↘ S) := hPre'
    let : NeZero l := hl
    let : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := smoothOfRelativeDimension_two k₀ hΦ b
    have hpresentation :=
      hasToricPresentation_of_hirzebruch k₀ (b := b) hΦ hc b k r hr C hE' hK'
    exact hpresentation.of_comap_iso (e := a.symm)
      (by rw [finiteFanScheme_over, ← ha, Iso.symm_hom, Iso.inv_hom_id_assoc])

end TauCeti.Toric.Fan
