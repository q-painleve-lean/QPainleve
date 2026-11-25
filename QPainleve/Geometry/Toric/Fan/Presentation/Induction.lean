/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.Analysis.Complex.Polynomial.Basic
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
import QPainleve.Geometry.Toric.Fan.Presentation.NodalReduction
import QPainleve.Geometry.Toric.Fan.Presentation.PointTower
import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Reduction
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

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

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "K[" X "]" => LineBundleClass.mk (canonicalBundle ℂ X 2)
local notation "J[" x "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ x)
local notation "T[" x "]" => BlowupTower.nil.snoc J[x]
local notation "X[" Φ "]" => Fan.algebraicRealization Φ

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (b : Basis (Fin 2) ℤ N)

private theorem smoothOfRelativeDimension_two {Φ : Fan i} (hΦ : Φ.IsRegular)
    (d : Basis (Fin 2) ℤ N) : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := by
  rw [algebraicRealization_over]
  exact ((finrank_eq_card_basis d).trans (Fintype.card_fin 2)) ▸
    Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ

private theorem hasToricPresentation_of_toric_boundary {X : Scheme} {D : X.IdealSheafData}
    {s : X ⟶ S} {Φ : Fan i} (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (e : X[Φ] ≅ X) (he : e.hom ≫ s = Φ.algebraicRealizationStructureMap)
    (hD : D.comap e.hom = Φ.boundaryIdeal hc.nonempty_cones) :
    D.HasToricPresentation s b i := by
  refine (hasToricPresentation_iff ..).mpr
    ⟨Φ, hΦ, hc, 0, Fin.elim0, Fin.elim0, 0, X, .nil, .nil, ?_⟩
  let : Nonempty Φ.cones := hc.nonempty_cones
  rw [internalBlowupTower_zero]
  refine ⟨e, by simpa using he, ?_⟩
  simp only [toBase_nil, comap_id, ← radical_comap_of_isOpenImmersion,
    WithBoundary.boundaryι_nil, ker_subschemeι, hD, Φ.boundaryIdeal_def]
  exact (isReduced_subscheme_iff_radical_eq _).mp inferInstance

private theorem hasToricPresentation_of_nodal_tower
    {X Y Z : Scheme} {D : X.IdealSheafData} {E : Z.IdealSheafData}
    {s : X ⟶ S} {t : Z ⟶ S} {m : ℕ} {T : BlowupTower X m Y}
    (hT : IsNodalBoundaryTower D s (𝟙 X) T) (a : Y ≅ Z)
    (ht : a.hom ≫ t = T.toBase ≫ s)
    (hE : (E.comap a.hom).support = (D.comap T.toBase).support)
    (h : E.HasToricPresentation t b i) : D.HasToricPresentation s b i := by
  obtain ⟨Φ, hΦ, hc, n, rays, c, l, W, U, hU, e, he, hB⟩ := (hasToricPresentation_iff ..).mp h
  obtain ⟨W', Wtower, f, hW, hbase, hrad⟩ := hT.exists_append_of_iso hU a ht hE
  have ht' : a.inv ≫ T.toBase ≫ s = t := by rw [← ht, Iso.inv_hom_id_assoc]
  refine (hasToricPresentation_iff ..).mpr
    ⟨Φ, hΦ, hc, n, rays, c, m + l, W', Wtower, hW, e ≪≫ f.symm, ?_, ?_⟩
  · simpa only [Iso.trans_hom, Iso.symm_hom, hbase, Category.assoc, Iso.inv_hom_id_assoc, ht']
      using he
  · simpa only [Iso.trans_hom, Iso.symm_hom, hrad, ← comap_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id] using hB

private theorem hasToricPresentation_of_nodal_blowup_and_internal_contraction
    {X Y : Scheme} [X.Over S] [Y.Over S] [IsIntegral X] [IsIntegral Y]
    [X.IsProjectiveOver ℂ] [Y.IsProjectiveOver ℂ]
    [SmoothOfRelativeDimension 2 (X ↘ S)] [SmoothOfRelativeDimension 2 (Y ↘ S)]
    {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)] (hD : D.IsEffectiveCartier)
    (hK : LineBundleClass.mk hD.toInvertibleSheaf = K[X])
    {x : X} (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T[x])
    {y : Y} (hy : IsClosed ({y} : Set Y)) (u : J[x].blowup ≅ J[y].blowup) :
    let g := u.hom ≫ J[y].blowupToBase
    let R := (D.comap J[x].blowupToBase).radical
    g ≫ Y ↘ S = J[x].blowupToBase ≫ X ↘ S →
    ¬ (J[y].comap g).support ≤ R.support →
    (R.map g).HasToricPresentation (Y ↘ S) b i →
    D.HasToricPresentation (X ↘ S) b i := by
  intro g R hg hOmit h
  have hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S) := by
    rw [← D.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ S)
  have hπ : T[x].toBase = J[x].blowupToBase := by simp
  obtain ⟨Φ, hΦ, hc, n, r, c, l, W, U, hU, e, he, hB⟩ := (hasToricPresentation_iff ..).mp h
  let : Nonempty Φ.cones := hc.nonempty_cones
  obtain ⟨r', c', Z', T', hT', d, hd, hD'⟩ :=
    exists_toric_presentation_of_internal_contraction_after_nodal_tower b hΦ hc r c hD hN hK
      hT g (by rwa [hπ]) hy u rfl (by simpa only [hπ, R, support_radical] using hOmit)
      (by rwa [hπ]) e he (by rwa [hπ, radical_comap_of_isOpenImmersion])
  exact (hasToricPresentation_iff ..).mpr ⟨Φ, hΦ, hc, n + 1, Fin.snoc r r', Fin.snoc c c',
    1 + l, Z', T', hT', d, hd, by rwa [← radical_comap_of_isOpenImmersion]⟩

variable {b}

private theorem exists_numbering_on_fan_model
    {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
    {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]
    {n : ℕ} [NeZero n] {ι : Type} {p : ι → (D.subscheme ↘ S).smoothLocus}
    (A : Scheme.NodalCycleNumbering p n) (hD : D.IsEffectiveCartier)
    (hK : LineBundleClass.mk hD.toInvertibleSheaf = K[X])
    {Φ : Fan i} (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (d : Basis (Fin 2) ℤ N)
    (e : X[Φ] ≅ X) (he : e.hom ≫ X ↘ S = Φ.algebraicRealizationStructureMap) :
    letI : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := smoothOfRelativeDimension_two hΦ d
    ∃ (hE : (D.comap e.hom).IsEffectiveCartier)
      (_ : PrestableFamily ((D.comap e.hom).subscheme ↘ S)),
      LineBundleClass.mk hE.toInvertibleSheaf = K[X[Φ]] ∧
      ∃ (m : ℕ) (_ : NeZero m),
        Nonempty (Scheme.NodalCycleNumbering
          (PEmpty.elim : PEmpty.{1} → ((D.comap e.hom).subscheme ↘ S).smoothLocus) m) := by
  let : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := smoothOfRelativeDimension_two hΦ d
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : X[Φ].IsProjectiveOver ℂ := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc d
  let : Smooth (X[Φ] ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have he' : e.inv ≫ X[Φ] ↘ S = X ↘ S := by
    rw [algebraicRealization_over, ← he, Iso.inv_hom_id_assoc]
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
    let : X[Φ].IsProjectiveOver ℂ := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc d
    let : Smooth (X[Φ] ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : IsNoetherian X[Φ] := isNoetherian_of_finiteType (X[Φ] ↘ S)
    let hRat : Scheme.IsRationalOver (X[Φ] ↘ S) :=
      isRationalOver_of_hirzebruch d (k : ℤ) hΦ r hr hc
    let : IsIntegral X[Φ] := hRat.isIntegral_of_smooth
    let : Module.Finite ℤ (Additive (LineBundleClass X[Φ])) :=
      Module.Finite.of_basis (Φ.hirzebruchPicardBasis d (k : ℤ) hΦ r hr)
    by_cases hzero : D.boundaryComplexity = 0
    · let : IsReduced D.subscheme :=
        (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := D.subscheme ↘ S)).isReduced
      obtain ⟨Ψ, hΨ, hcΨ, e, he, hE⟩ :=
        exists_toric_of_hirzebruch_boundaryComplexity_zero d (k : ℤ) hΦ hc r hr
          (Int.natCast_nonneg k) hD hzero hK
      exact hasToricPresentation_of_toric_boundary b hΨ hcΨ e
        (he.trans (algebraicRealization_over (Φ := Ψ))) hE
    have hq := D.boundaryComplexity_nonneg_of_nodalCycleNumbering hD A
    have hpos := lt_of_le_of_ne hq (Ne.symm hzero)
    obtain ⟨j, Y, s, y, u, f, hSm, hT, hInt, hProj, hy, hg, hOmit, hfOver, hfFlat, hfiber,
      hE, hKE, hdrop, hpre, ⟨B⟩⟩ :=
      exists_hirzebruch_positive_complexity_reduction d hΦ hc r hr hD hK A
        (Int.natCast_nonneg k) hpos
    let : Y.Over S := ⟨s⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hSm
    let : IsIntegral Y := hInt
    let : Y.IsProjectiveOver ℂ := hProj
    let : f.IsOver S := hfOver
    let : Flat f := hfFlat
    let : Scheme.IsRationalOver (Y ↘ S) :=
      hT.isClosedPointTower.isRationalOver_of_common_pointBlowup (t := s) hy u
        (by simpa only [Category.assoc, toBase_snoc, toBase_nil, Category.comp_id] using hg)
    obtain ⟨Ψ, hΨ, hcΨ, k', r', hr', e, hruling⟩ :=
      f.exists_hirzebruch_model_of_projectiveLine_fibers b Φ.lattice hfiber
    have he : e.hom ≫ Y ↘ S = Ψ.algebraicRealizationStructureMap := by
      rw [← comp_over f S, ← Category.assoc, hruling, comp_over, algebraicRealization_over]
    let g := u.hom ≫ J[y].blowupToBase
    let E := ((D.comap J[A.ambientNode j].blowupToBase).radical).map g
    let : PrestableFamily (E.subscheme ↘ S) := hpre
    obtain ⟨hE', hpre', hK', m, hm, ⟨C⟩⟩ := exists_numbering_on_fan_model B hE hKE hΨ hcΨ b e he
    let : PrestableFamily ((E.comap e.hom).subscheme ↘ S) := hpre'
    let : NeZero m := hm
    have hover : e.hom ≫ Y ↘ S = X[Ψ] ↘ S := he.trans (algebraicRealization_over (Φ := Ψ)).symm
    -- Complexity is unchanged by the new model and drops strictly under the link.
    have hlt : (E.comap e.hom).boundaryComplexity.toNat < l := by
      have hdrop' : E.boundaryComplexity + 1 = D.boundaryComplexity := hdrop
      rw [boundaryComplexity_comap_iso, ← hl]
      omega
    let : SmoothOfRelativeDimension 2 (X[Ψ] ↘ S) := smoothOfRelativeDimension_two hΨ b
    have hEp := (ih _ hlt hΨ hcΨ b k' r' hr' C hE' hK' rfl).of_comap_iso
      (e := e.symm) (by rw [Iso.symm_hom, ← hover, Iso.inv_hom_id_assoc])
    exact hasToricPresentation_of_nodal_blowup_and_internal_contraction
      b hD hK hT hy u hg hOmit hEp

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "Π" => Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule ℂ (Fin 3 → ℂ))

private theorem hasToricPresentation_of_plane (hi : IsIntegralLattice i)
    {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
    {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]
    {n : ℕ} [NeZero n] {ι : Type} {p : ι → (D.subscheme ↘ S).smoothLocus}
    (A : Scheme.NodalCycleNumbering p n) (hD : D.IsEffectiveCartier)
    (hK : LineBundleClass.mk hD.toInvertibleSheaf = K[X])
    (a : Π ≅ X) [a.hom.IsOver S] :
    D.HasToricPresentation (X ↘ S) b i := by
  rcases exists_toric_or_hirzebruch_one_of_numbered_plane_boundary b hi a A hD hK 0 with
    ⟨-, e, hover, he⟩ | ⟨-, Φ, hΦ, hc, d, r, e, hr, hover, -, -, -, hE, hpre, hcan, B, _⟩
  · let Φ := projectiveSpace b hi
    exact hasToricPresentation_of_toric_boundary b (isRegular_projectiveSpace b hi)
      (isComplete_projectiveSpace b hi) e
      (hover.comp_over.trans (algebraicRealization_over (Φ := Φ))) he
  · let E := (D.comap (e.hom ≫ J[A.ambientNode 0].blowupToBase)).radical
    let : PrestableFamily (E.subscheme ↘ S) := hpre
    let : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := smoothOfRelativeDimension_two hΦ d
    have hEp := hasToricPresentation_of_hirzebruch (b := b) hΦ hc d 1 r
      (by simpa only [Int.natCast_one] using hr) B hE hcan
    have hT := isNodalBoundaryTower_numbered_node A (0 : ZMod n)
    have hb : e.inv ≫ X[Φ] ↘ S = T[A.ambientNode 0].toBase ≫ X ↘ S := by
      simpa only [toBase_snoc, toBase_nil, Category.comp_id, ← Category.assoc,
        Iso.inv_hom_id, Category.id_comp] using (congrArg (e.inv ≫ ·) hover.comp_over).symm
    refine hasToricPresentation_of_nodal_tower b hT e.symm hb ?_ hEp
    rw [Iso.symm_hom, ← radical_comap_of_isOpenImmersion, support_radical, ← comap_comp,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      toBase_snoc, toBase_nil, Category.comp_id]

/-- Every numbered anticanonical cycle on a smooth projective rational complex
surface has a toric presentation in the prescribed lattice basis. The proof
reduces the ruled cases by boundary complexity and transports the presentation
through the original point-blowup tower. -/
theorem hasToricPresentation_of_ruled_reduction (hi : IsIntegralLattice i)
    {X : Scheme} [X.Over S] [X.IsProjectiveOver ℂ] [SmoothOfRelativeDimension 2 (X ↘ S)]
    [Scheme.IsRationalOver (X ↘ S)]
    {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]
    {n : ℕ} [NeZero n] {ι : Type} {p : ι → (D.subscheme ↘ S).smoothLocus}
    (A : Scheme.NodalCycleNumbering p n) (hD : D.IsEffectiveCartier)
    (hK : LineBundleClass.mk hD.toInvertibleSheaf = K[X]) :
    D.HasToricPresentation (X ↘ S) b i := by
  obtain ⟨Y, s, _, W, T, e, hproj, hsmooth, hrat, hmin, hT, he, -⟩ :=
    X.exists_isClosedPointTower_of_minimal_model ℂ
  let : Y.Over S := ⟨s⟩
  let : Y.IsProjectiveOver ℂ := hproj
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
  refine hT.hasToricPresentation_of_closedPointTower_of_iso e he hD hN hK ?_
  rcases Y.exists_iso_projectivePlane_or_hirzebruch b hi hmin with
    ⟨a, ha⟩ | ⟨Φ, hΦ, hc, k, r, a, -, hr, ha⟩
  · let d := a ≪≫ ((Pi.basisFun ℂ (Fin 3)).reindex Equiv.ulift.symm).polynomialProjIso
    have hd : d.hom ≫ Π ↘ S = Y ↘ S := by
      rw [Iso.trans_hom, Category.assoc, SymmetricAlgebra.over_eq_projToSpec,
        Basis.polynomialProjIso_hom_over, ha]
    let : d.symm.hom.IsOver S := ⟨by rw [Iso.symm_hom, ← hd, Iso.inv_hom_id_assoc]⟩
    exact hasToricPresentation_of_plane hi B hE hKE d.symm
  · obtain ⟨hE', hPre', hK', l, hl, ⟨C⟩⟩ := exists_numbering_on_fan_model B hE hKE hΦ hc b a ha
    let : PrestableFamily ((E.comap a.hom).subscheme ↘ S) := hPre'
    let : NeZero l := hl
    let : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := smoothOfRelativeDimension_two hΦ b
    have hpresentation :=
      hasToricPresentation_of_hirzebruch (b := b) hΦ hc b k r hr C hE' hK'
    exact hpresentation.of_comap_iso (e := a.symm)
      (by rw [algebraicRealization_over, ← ha, Iso.symm_hom, Iso.inv_hom_id_assoc])

end TauCeti.Toric.Fan
