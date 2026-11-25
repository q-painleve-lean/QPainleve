/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Ruling.ElementaryTransform
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Complexity
public import TauCeti.AlgebraicGeometry.Curves.Prestable

import QPainleve.AlgebraicGeometry.Blowup.Point.Basic
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Cartier
import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Complexity
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Complexity
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Subdivision
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.ClosedImmersion
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.IdealSheaf.Fiber
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Dominant
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Elementary transformations of numbered anticanonical cycles

A nodal elementary transformation of a ruling inserts one component into the
boundary cycle and lowers its complexity by one. The resulting surface is again
ruled by projective lines over the same base. This is the decreasing step in
[Gross, Hacking and Keel, Proposition 1.3][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry LineBundleClass
open QPainleve QPainleve.BlowupTower AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Hom

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k] {X C : Scheme.{u}}
variable [X.Over (Spec (.of k))] [IsIntegral X] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "P₁" => projectiveLine k
local notation "J[" x "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ x)
local notation "I[" p "]" => vanishingIdeal (Closeds.mk (closure ({p} : Set X)) isClosed_closure)
local notation "B[" p "]" => blowup (I[p])
local notation "π[" p "]" => blowupToBase (I[p])
local notation "R[" p "," D "]" => radical (comap D (π[p]))
local notation "F[" f "," y "]" => comap (J[y]) f
local notation "K[" Y "]" => LineBundleClass.mk (QPainleve.canonicalBundle k Y 2)

private theorem numberedCycle_of_transformedBoundary
    {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)] (hD : D.IsEffectiveCartier)
    {n : ℕ} [NeZero n] {ι : Type v} {marks : ι → (D.subscheme ↘ S).smoothLocus}
    (A : Scheme.NodalCycleNumbering marks n) (j : ZMod n)
    {Y : Scheme.{u}} [Y.Over S] {D' : Y.IdealSheafData}
    (g : B[A.ambientNode j] ⟶ Y) (hg : g ≫ Y ↘ S = π[A.ambientNode j] ≫ X ↘ S)
    (e : (R[A.ambientNode j,D]).subscheme ≅ D'.subscheme)
    (he : e.hom ≫ D'.subschemeι = (R[A.ambientNode j,D]).subschemeι ≫ g) :
    ∃ _ : PrestableFamily (D'.subscheme ↘ S),
      Nonempty (Scheme.NodalCycleNumbering
        (Empty.elim : Empty → (D'.subscheme ↘ S).smoothLocus) (n + 1)) := by
  let p := A.ambientNode j
  let T : BlowupTower X 1 B[p] := BlowupTower.nil.snoc (I[p])
  have hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T :=
    IsNodalBoundaryTower.of_node (A.isClosed_ambientNode j)
      (A.isNodeOfReducedBoundary_ambientNode j rfl)
  have hπ : T.toBase = π[p] := by simp [T, toBase_snoc, toBase_nil]
  let : B[p].Over S := ⟨π[p] ≫ X ↘ S⟩
  have hR :
      let : B[p].Over S := ⟨π[p] ≫ X ↘ S⟩
      let E := (D.comap π[p]).radical
      ∃ _ : PrestableFamily (E.subscheme ↘ S),
        Nonempty (Scheme.NodalCycleNumbering
          (Empty.elim : Empty → (E.subscheme ↘ S).smoothLocus) (n + 1)) := by
    -- Abstract the surface projection so the induced base map varies with it.
    rw [← hπ]
    let : B[p].Over S := ⟨T.toBase ≫ X ↘ S⟩
    have hp : PrestableFamily ((D.comap T.toBase).radical.subscheme ↘ S) :=
      hT.prestableFamily_radical_comap_toBase hD
    obtain ⟨A', -, -⟩ := hT.exists_isOrientedCycleSubdivision_nodalBoundaryTower hD A
      (Empty.elim : Empty → _)
    exact ⟨hp, ⟨A'⟩⟩
  obtain ⟨hp, ⟨A'⟩⟩ := hR
  have := hp
  have hcomp : e.hom ≫ (D'.subscheme ↘ S) = (R[p,D]).subscheme ↘ S := by
    rw [IdealSheafData.over_eq_subschemeι_comp, ← Category.assoc, he, Category.assoc, hg]
    rfl
  have hpre : PrestableFamily (D'.subscheme ↘ S) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily) e.hom _).mp
      (hcomp.symm ▸ hp)
  have := hpre
  let : e.hom.IsOver S := ⟨hcomp⟩
  exact ⟨hpre, ⟨e.mapNodalCycleNumbering A'⟩⟩

private theorem finite_picard_and_complexity_of_nodal_elementary_transform
    [Module.Finite ℤ (Additive (LineBundleClass X))]
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier) {p : X}
    (hp : IsClosed ({p} : Set X)) (hn : D.IsNodeOfReducedBoundary (X ↘ S) p)
    {Y : Scheme.{u}} [Y.Over S] [IsIntegral Y] [Y.IsProjectiveOver k]
    [SmoothOfRelativeDimension 2 (Y ↘ S)] {q : Y} (hq : IsClosed ({q} : Set Y))
    {D' : Y.IdealSheafData} (hD' : D'.IsEffectiveCartier)
    (e : B[p] ≅ (J[q]).blowup) (d : (R[p,D]).subscheme ≅ D'.subscheme)
    (hR : (R[p,D]).IsEffectiveCartier)
    (hd : d.hom ≫ D'.subschemeι = (R[p,D]).subschemeι ≫ e.hom ≫ (J[q]).blowupToBase) :
    Module.Finite ℤ (Additive (LineBundleClass Y)) ∧
      D'.boundaryComplexity + 1 = D.boundaryComplexity := by
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  have : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ S)
  let T : BlowupTower X 1 B[p] := BlowupTower.nil.snoc (I[p])
  let U : BlowupTower Y 1 (J[q]).blowup := BlowupTower.nil.snoc (J[q])
  have hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T := IsNodalBoundaryTower.of_node hp hn
  have hU : IsClosedPointTower Y U := .snoc .nil q hq rfl
  have : Module.Finite ℤ (Additive (LineBundleClass Y)) :=
    (finite_picard_iff_of_common_resolution k hT.isClosedPointTower hU e.symm).mp inferInstance
  let B := (R[p,D]).comap e.inv
  have hB : B.IsEffectiveCartier := hR.comap e.inv
  obtain ⟨hb, hbi⟩ := (R[p,D]).exists_iso_of_comap_eq_ker e.symm B.subschemeι
    (ker_subschemeι B).symm
  have hcomp : (hb ≪≫ d).hom ≫ D'.subschemeι = B.subschemeι ≫ U.toBase := by
    rw [Iso.trans_hom, Category.assoc, hd, ← Category.assoc hb.hom, hbi]
    simp [U, toBase_snoc, toBase_nil, Category.assoc]
  have hcomplex := hU.boundaryComplexity_eq_add_length_of_subschemeIso k hD' hB (hb ≪≫ d) hcomp
  have hnodal := hT.boundaryComplexity_comap hD
  simp only [B, ← Iso.symm_hom e, boundaryComplexity_comap_iso, boundaryComplexity_radical]
    at hcomplex
  have hπ : T.toBase = π[p] := by simp [T, toBase_snoc, toBase_nil]
  rw [hπ] at hnodal
  exact ⟨inferInstance, hcomplex.symm.trans hnodal⟩

omit [IsIntegral X] [X.IsProjectiveOver k] in
private theorem exists_projectiveLine_iso_fiber_of_elementary_transform
    (f : X ⟶ C)
    (hf : ∀ z : C, IsClosed ({z} : Set C) →
      ∃ a : P₁ ≅ f.fiber z, a.hom ≫ f.fiberι z ≫ X ↘ S = P₁ ↘ S)
    {p : X} (hp : IsClosed ({p} : Set X)) {Y : Scheme.{u}} [Y.Over S]
    (g : B[p] ⟶ Y) (hg : g ≫ Y ↘ S = π[p] ≫ X ↘ S) (f' : Y ⟶ C)
    (v : (I[p].comap π[p]).subscheme ≅ (F[f',f p]).subscheme)
    (hv : v.hom ≫ (F[f',f p]).subschemeι = (I[p].comap π[p]).subschemeι ≫ g)
    (haway : ∀ z : C, IsClosed ({z} : Set C) → z ≠ f p →
      ∃ a : (F[f',z]).subscheme ≅ (F[f,z]).subscheme, a.hom.IsOver S)
    (z : C) (hz : IsClosed ({z} : Set C)) :
    ∃ a : P₁ ≅ f'.fiber z, a.hom ≫ f'.fiberι z ≫ Y ↘ S = P₁ ↘ S := by
  obtain ⟨b, hb⟩ := f'.exists_fiberIso_subscheme_of_isClosed hz
  suffices h : ∃ a : P₁ ≅ (F[f',z]).subscheme,
      a.hom ≫ (F[f',z]).subschemeι ≫ Y ↘ S = P₁ ↘ S by
    obtain ⟨a, ha⟩ := h
    exact ⟨a ≪≫ b.symm, by
      rw [Iso.trans_hom, Iso.symm_hom, ← hb]
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using ha⟩
  by_cases hzy : z = f p
  · subst z
    obtain ⟨w, hw⟩ :=
      SmoothOfRelativeDimension.exists_iso_projectiveLine_exceptional_blowup_closedPoint_over
        (X ↘ S) p hp
    refine ⟨w ≪≫ v, ?_⟩
    rw [Iso.trans_hom, Category.assoc, ← Category.assoc v.hom, hv, Category.assoc, hg]
    exact hw
  · obtain ⟨a, ha⟩ := haway z hz hzy
    obtain ⟨c, hc⟩ := hf z hz
    obtain ⟨d, hd⟩ := f.exists_fiberIso_subscheme_of_isClosed hz
    refine ⟨c ≪≫ d ≪≫ a.symm, ?_⟩
    rw [← IdealSheafData.over_eq_subschemeι_comp, ← ha.comp_over]
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
      IdealSheafData.over_eq_subschemeι_comp, ← Category.assoc d.hom, hd] using hc

omit [IsAlgClosed k] [X.IsProjectiveOver k] in
private theorem birationalOver_of_nodal_elementary_transform
    {D : X.IdealSheafData} {p : X} (hp : IsClosed ({p} : Set X))
    (hn : D.IsNodeOfReducedBoundary (X ↘ S) p) {Y : Scheme.{u}}
    (g : B[p] ⟶ Y) [IsModification g] {s : Y ⟶ S}
    (hg : g ≫ s = π[p] ≫ X ↘ S) :
    Scheme.BirationalOver (X ↘ S) s := by
  let T : BlowupTower X 1 B[p] := BlowupTower.nil.snoc (I[p])
  have hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T := IsNodalBoundaryTower.of_node hp hn
  have hπ : T.toBase = π[p] := by simp [T, toBase_snoc, toBase_nil]
  have : IsModification π[p] :=
    hπ ▸ hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
  obtain ⟨a, ha⟩ := IsModification.birationalOver π[p]
  obtain ⟨b, hb⟩ := IsModification.birationalOver g
  have h₁ : Scheme.BirationalOver (π[p] ≫ X ↘ S) (X ↘ S) :=
    ⟨a, by simpa only [Category.assoc, Category.comp_id] using congrArg (· ≫ X ↘ S) ha⟩
  have h₂ : Scheme.BirationalOver (π[p] ≫ X ↘ S) s :=
    ⟨b, by simpa only [Category.assoc, Category.comp_id, hg] using congrArg (· ≫ s) hb⟩
  exact h₁.symm.trans h₂

variable [C.Over (Spec (.of k))] [IsIntegral C] [IsSeparated (C ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))]

/-- At a numbered boundary node on a fiber omitted by the boundary, a nodal
elementary transformation gives a proper flat ruling with projective-line
closed fibers over the same base. The contracted surface has a numbered
anticanonical cycle with one more component and complexity one less than
the original cycle. The reduced total boundary omits the contracted curve. The
new surface is birational to the original over the ground field and the
replaced fiber is a component of its boundary. -/
theorem exists_elementary_transform_of_numbered_nodal_fiber
    [Module.Finite ℤ (Additive (LineBundleClass X))]
    (f : X ⟶ C) [f.IsOver S] [IsDominant f]
    (hf : ∀ z : C, IsClosed ({z} : Set C) →
      ∃ a : P₁ ≅ f.fiber z, a.hom ≫ f.fiberι z ≫ X ↘ S = P₁ ↘ S)
    {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)] (hD : D.IsEffectiveCartier)
    (hK : LineBundleClass.mk hD.toInvertibleSheaf = K[X])
    {n : ℕ} [NeZero n] {ι : Type v} {marks : ι → (D.subscheme ↘ S).smoothLocus}
    (A : Scheme.NodalCycleNumbering marks n) (j : ZMod n)
    (hF : ¬ (F[f,f (A.ambientNode j)]).support ≤ D.support) :
    let p := A.ambientNode j
    let : B[p].Over S := ⟨π[p] ≫ X ↘ S⟩
    ∃ (Y : Scheme.{u}) (s : Y ⟶ S) (g : B[p] ⟶ Y) (q : Y) (f' : Y ⟶ C),
      let : Y.Over S := ⟨s⟩
      ∃ hSmooth : SmoothOfRelativeDimension 2 s,
      let : SmoothOfRelativeDimension 2 (Y ↘ S) := hSmooth
      let D' := (R[p,D]).map g
      IsIntegral Y ∧ Y.IsProjectiveOver k ∧ Scheme.BirationalOver (X ↘ S) s ∧
      IsModification g ∧ g.IsOver S ∧
      IsDominant f' ∧ f'.IsOver S ∧ g ≫ f' = π[p] ≫ f ∧ IsProper f' ∧ Flat f' ∧
      (∀ z : C, IsClosed ({z} : Set C) → ∃ a : P₁ ≅ f'.fiber z,
        a.hom ≫ f'.fiberι z ≫ Y ↘ S = P₁ ↘ S) ∧
      IsClosed ({q} : Set Y) ∧
      (∃ e : B[p] ≅ (J[q]).blowup, e.hom ≫ (J[q]).blowupToBase = g) ∧
      ¬ ((J[q]).comap g).support ≤ (R[p,D]).support ∧
      D'.comap g = R[p,D] * (J[q]).comap g ∧ D' ≤ F[f',f p] ∧
      ∃ hD' : D'.IsEffectiveCartier,
        LineBundleClass.mk hD'.toInvertibleSheaf = K[Y] ∧
        Module.Finite ℤ (Additive (LineBundleClass Y)) ∧
        D'.boundaryComplexity + 1 = D.boundaryComplexity ∧
        ∃ _ : PrestableFamily (D'.subscheme ↘ S),
          Nonempty (Scheme.NodalCycleNumbering
            (Empty.elim : Empty → (D'.subscheme ↘ S).smoothLocus) (n + 1)) := by
  intro p hOver
  let := hOver
  have hn := A.isNodeOfReducedBoundary_ambientNode j rfl
  have hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S) := by
    rw [← IdealSheafData.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have hp := A.isClosed_ambientNode j
  let y := f p
  have : IsProper (f ≫ C ↘ S) :=
    (comp_over f S).symm ▸ inferInstanceAs (IsProper (X ↘ S))
  have : IsProper f := IsProper.of_comp f (C ↘ S)
  have hy : IsClosed ({y} : Set C) := by simpa only [Set.image_singleton] using f.isClosedMap _ hp
  have : Smooth (C ↘ S) := SmoothOfRelativeDimension.smooth 1 _
  have : TauCeti.AlgebraicGeometry.IsRegular C := IsRegular.of_smooth (C ↘ S)
  have hJ := C.isEffectiveCartier_ker_fromSpecResidueField_of_dim_eq_one hy
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension (C ↘ S))
  obtain ⟨a, ha⟩ := hf y hy
  obtain ⟨b, hb⟩ := f.exists_fiberIso_subscheme_of_isClosed hy
  have ha' : (a ≪≫ b).inv.IsOver S := ⟨by
    have hab : (a ≪≫ b).hom ≫ (F[f,y]).subscheme ↘ S = P₁ ↘ S := by
      rw [Iso.trans_hom, IdealSheafData.over_eq_subschemeι_comp, Category.assoc,
        ← Category.assoc b.hom, hb, ha]
    rw [← hab, Iso.inv_hom_id_assoc]⟩
  obtain ⟨Y, s, g, q, f', hSmooth, hY, hProj, hmod, hg, hdom, hf', hcomp, hq, -, hqF, homit,
    -, hnew, -, ⟨v, hv⟩, -, htotal, haway, ⟨e, he⟩, hD', hK', -, d, hd⟩ :=
    f.exists_elementary_transform_of_nodal_fiber hD hN hK hp hn hy rfl hJ (a ≪≫ b).symm ha' hF
  let : Y.Over S := ⟨s⟩
  let := hY
  let := hProj
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hSmooth
  let := hdom
  have := hmod
  have hbir := birationalOver_of_nodal_elementary_transform hp hn g hg.comp_over
  have : IsProper (f' ≫ C ↘ S) := hf'.comp_over.symm ▸ inferInstanceAs (IsProper (Y ↘ S))
  refine ⟨Y, s, g, q, f', hSmooth, hY, hProj, hbir, hmod, hg, hdom, hf', hcomp,
    IsProper.of_comp f' (C ↘ S), f'.flat_of_isDominant_of_smooth (C ↘ S), ?_,
    hq, ⟨e, he⟩, homit, hqF.symm ▸ htotal, hnew, hD', hK', ?_⟩
  · exact exists_projectiveLine_iso_fiber_of_elementary_transform f hf hp g hg.comp_over f' v hv
      (fun z hz hzy ↦ by
        obtain ⟨a, ha, -⟩ := haway z hz hzy
        exact ⟨a, ha⟩)
  · have : IsReduced D.subscheme := hN.isReduced
    have hR := hD.radical_comap_blowupToBase_of_closedPoint (X ↘ S) hp
      (mem_support_of_isNodeOfReducedBoundary hn)
    obtain ⟨hfinite, hcomplexity⟩ :=
      finite_picard_and_complexity_of_nodal_elementary_transform hD hp hn hq hD' e d hR
        (by rwa [he])
    exact ⟨hfinite, hcomplexity, numberedCycle_of_transformedBoundary hD A j g hg.comp_over d hd⟩

end AlgebraicGeometry.Scheme.Hom
