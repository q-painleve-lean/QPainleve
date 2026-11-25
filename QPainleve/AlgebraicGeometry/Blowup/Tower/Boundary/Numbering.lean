/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Numbering
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Nodality

import QPainleve.AlgebraicGeometry.Blowup.Point.BoundaryPrimes
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Curves.Node.Image
import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Descending numbered boundaries through point-blowup towers

A numbered nodal anticanonical boundary descends along a specified closed-point
blowup tower. A contraction with center smooth on the image boundary induces
a boundary isomorphism. At a nodal center it removes one component, with the
ordered attachments giving the branches at the descended node.

This gives the numbered boundary in the reduction to a minimal pair in
[Gross, Hacking and Keel, Proposition 1.3](https://arxiv.org/html/1106.4977v3#S1.Thmproposition3).
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry Scheme.Hom Scheme.IdealSheafData LineBundleClass

universe u v

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [IsAlgClosed k]

local notation "SpecK" => Spec (CommRingCat.of k)
local notation "K[" X "]" => mk (QPainleve.canonicalBundle k X 2)

variable {X : Scheme.{u}} [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [IsIntegral X] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "J[" p "]" =>
  vanishingIdeal (Closeds.mk (closure ({p} : Set X)) isClosed_closure)

private theorem exists_numbering_nodal_step {p : X} (hp : IsClosed ({p} : Set X))
    {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ SpecK)]
    (hD : D.IsEffectiveCartier) (hnode : D.IsNodeOfReducedBoundary (X ↘ SpecK) p)
    {B : (J[p]).blowup.IdealSheafData}
    [((J[p]).blowup).Over SpecK] [PrestableFamily (B.subscheme ↘ SpecK)]
    (hBOver : B.subscheme ↘ SpecK = B.subschemeι ≫ (J[p]).blowupToBase ≫ (X ↘ SpecK))
    (hB : B = (D.comap (J[p]).blowupToBase).radical)
    {m : ℕ} [NeZero m] {ι : Type v} {a : ι → (B.subscheme ↘ SpecK).smoothLocus}
    (A : Scheme.NodalCycleNumbering a m) :
    ∃ (l : ℕ) (_ : NeZero l)
      (C : Scheme.NodalCycleNumbering
        (fun x : PEmpty.{v + 1} ↦ x.elim : PEmpty.{v + 1} → (D.subscheme ↘ SpecK).smoothLocus) l)
      (g : B.subscheme ⟶ D.subscheme),
      g ≫ D.subschemeι = B.subschemeι ≫ (J[p]).blowupToBase ∧
      g.IsOrientedCycleSubdivision A C := by
  have hN := PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := D.subscheme ↘ SpecK)
  have hDOver := D.over_eq_subschemeι_comp (S := SpecK)
  have : IsReduced D.subscheme := hN.isReduced
  obtain ⟨q, hq, hqN⟩ := (D.isNodeOfReducedBoundary_iff_of_isReduced (X ↘ SpecK) p).mp hnode
  subst p
  have hsing := (D.subscheme.mem_support_singularLocus_iff_notMem_smoothLocus q).mpr
    (fun h ↦ (hDOver.symm ▸ hqN).not_formallySmooth_stalkMap (Scheme.Hom.mem_smoothLocus.mp h))
  subst B
  obtain ⟨l, hl, -, C, hC⟩ :=
    D.exists_numbering_of_nodal_boundary_blowdown hp hsing hDOver hBOver hD A
      (fun x : PEmpty.{v + 1} ↦ x.elim)
  exact ⟨l, hl, C, _, subschemeMap_subschemeι .., hC⟩

variable [NeZero (2 : k)]

private theorem exists_numbering_point_step {p : X} (hp : IsClosed ({p} : Set X))
    {B : (J[p]).blowup.IdealSheafData}
    (hB : B.IsEffectiveCartier) :
    let π := (J[p]).blowupToBase
    let : (J[p]).blowup.Over SpecK := ⟨π ≫ (X ↘ SpecK)⟩
    let : SmoothOfRelativeDimension 2 ((J[p]).blowup ↘ SpecK) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ SpecK) hp
    ∀ [PrestableFamily (B.subscheme ↘ SpecK)] {m : ℕ} [NeZero m]
      {ι : Type v} {a : ι → (B.subscheme ↘ SpecK).smoothLocus},
    ∀ (A : Scheme.NodalCycleNumbering a m), mk hB.toInvertibleSheaf = K[(J[p]).blowup] →
    let D := B.map π
    ∃ (hD : D.IsEffectiveCartier) (_ : PrestableFamily (D.subscheme ↘ SpecK)),
      mk hD.toInvertibleSheaf = K[X] ∧
      ∃ (l : ℕ) (_ : NeZero l)
        (C : Scheme.NodalCycleNumbering
          (fun x : PEmpty.{v + 1} ↦ x.elim : PEmpty.{v + 1} → (D.subscheme ↘ SpecK).smoothLocus) l)
        (g : B.subscheme ⟶ D.subscheme),
        g ≫ D.subschemeι = B.subschemeι ≫ π ∧ g.IsOrientedCycleSubdivision A C := by
  intro π _ _ hpre m hm ι a A hcan D
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ SpecK)
  let E := (J[p]).comap π
  have hBOver : B.subscheme ↘ SpecK = B.subschemeι ≫ π ≫ (X ↘ SpecK) := rfl
  have hN := hBOver ▸ hpre.atWorstNodalOfRelativeDimensionOne
  obtain ⟨hD, hK, hnodal, htotal, hcases⟩ :=
    hB.anticanonical_nodal_boundary_point_blowdown k hp hN hcan
  let : PrestableFamily ((B.subschemeι ≫ π) ≫ (X ↘ SpecK)) := by
    rw [Category.assoc, ← hBOver]
    exact hpre
  let hpreD : PrestableFamily (D.subscheme ↘ SpecK) := by
    rw [D.over_eq_subschemeι_comp]
    exact (B.subschemeι ≫ π).prestableFamily_image (X ↘ SpecK) hnodal
  refine ⟨hD, hpreD, hK, ?_⟩
  by_cases hE : E.support ≤ B.support
  · have hrad : (D.comap π).radical = B := by
      rw [← vanishingIdeal_support, htotal, support_mul, sup_eq_left.mpr hE,
        vanishingIdeal_support]
      exact B.isReduced_subscheme_iff_radical_eq.mp hN.isReduced
    exact exists_numbering_nodal_step hp hD (hcases.mp hE) hBOver hrad.symm A
  · obtain ⟨_, _, _, _, _, _, _, _, e, he⟩ :=
      hB.internalBlowdown_of_anticanonical k hp hE hN hcan
    have : e.hom.IsOver SpecK := ⟨by rw [D.over_eq_subschemeι_comp, reassoc_of% he, hBOver]⟩
    let C := e.mapNodalCycleNumbering A (q := fun x : PEmpty.{v + 1} ↦ x.elim)
    exact ⟨m, hm, C, e.hom, he, e.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one A C
      (by simp [C])⟩

/-- The schematic image of a numbered nodal anticanonical boundary along a
closed-point blowup tower is again a numbered nodal anticanonical boundary.
The image numbering uses the empty set of marks. The induced map is an oriented
subdivision. Smooth boundary blowups and nodal blowups can occur in any order,
including at infinitely near points. -/
theorem exists_numbering_of_anticanonical_boundary_tower_blowdown
    {Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)
    {B : Y.IdealSheafData} (hB : B.IsEffectiveCartier)
    (t : Y ⟶ SpecK) (ht : t = T.toBase ≫ (X ↘ SpecK)) :
    let : Y.Over SpecK := ⟨t⟩
    ∀ [_hSm : SmoothOfRelativeDimension 2 (Y ↘ SpecK)]
      [_hPre : PrestableFamily (B.subscheme ↘ SpecK)] {m : ℕ}
      [NeZero m] {ι : Type v} {a : ι → (B.subscheme ↘ SpecK).smoothLocus},
    ∀ (A : Scheme.NodalCycleNumbering a m), mk hB.toInvertibleSheaf = K[Y] →
    let D := B.map T.toBase
    ∃ (hD : D.IsEffectiveCartier) (_ : PrestableFamily (D.subscheme ↘ SpecK)),
      mk hD.toInvertibleSheaf = K[X] ∧
      ∃ (l : ℕ) (_ : NeZero l)
        (C : Scheme.NodalCycleNumbering
          (fun x : PEmpty.{v + 1} ↦ x.elim : PEmpty.{v + 1} → (D.subscheme ↘ SpecK).smoothLocus) l)
        (g : B.subscheme ⟶ D.subscheme),
        g ≫ D.subschemeι = B.subschemeι ≫ T.toBase ∧ g.IsOrientedCycleSubdivision A C := by
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ SpecK)
  induction hT with
  | nil =>
    rw [toBase_nil, Category.id_comp] at ht
    subst t
    dsimp only
    intro hs hpre m hm ι a A hcan
    rw [toBase_nil, map_id]
    let : PrestableFamily (B.subscheme ↘ SpecK) := hpre
    let e := Iso.refl B.subscheme
    let marks : PEmpty.{v + 1} → (B.subscheme ↘ SpecK).smoothLocus := PEmpty.elim
    -- The two copies of the boundary use the same structure map and different marks.
    let C := @Iso.mapNodalCycleNumbering k _ _ B.subscheme B.subscheme _ _ hpre hpre
      ι a _ marks m hm e ⟨Category.id_comp _⟩ A
    refine ⟨hB, hpre, hcan, m, hm, C, e.hom, by simp [e], ?_⟩
    have hact := @Iso.boundaryCycleAction_mapNodalCycleNumbering
      k _ _ B.subscheme B.subscheme _ _ hpre hpre ι a _ marks m hm e ⟨Category.id_comp _⟩ A
    exact @Iso.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one
      k _ _ B.subscheme B.subscheme _ _ hpre hpre ι _ a marks m hm e
      ⟨Category.id_comp _⟩ A C (by rw [hact, map_one])
  | @snoc n W U I hU p hp hI ih =>
    have hcenter := hI.trans (W.ker_fromSpecResidueField_eq_vanishingIdeal p)
    subst hcenter
    let J := vanishingIdeal (Closeds.mk (closure ({p} : Set W)) isClosed_closure)
    rw [toBase_snoc, Category.assoc] at ht
    subst t
    let : W.Over SpecK := ⟨U.toBase ≫ (X ↘ SpecK)⟩
    let : SmoothOfRelativeDimension 2 (W ↘ SpecK) := hU.smoothOfRelativeDimension (X ↘ SpecK)
    have : IsIntegral W := hU.isIntegral (X ↘ SpecK)
    have : W.IsProjectiveOver k := U.isProjectiveOver k
    dsimp only
    intro hs hpre m hm ι a A hcan
    rw [toBase_snoc, map_comp]
    let : J.blowup.Over SpecK := ⟨J.blowupToBase ≫ (W ↘ SpecK)⟩
    let : PrestableFamily (B.subscheme ↘ SpecK) := hpre
    obtain ⟨hE, hpreE, hKE, l, hl, C, f, hf, hC⟩ := exists_numbering_point_step hp hB A hcan
    obtain ⟨hD, hpreD, hKD, j, hj, D, g, hg, hDsub⟩ :=
      ih hE (W ↘ SpecK) rfl (_hSm := ‹SmoothOfRelativeDimension 2 (W ↘ SpecK)›)
        (_hPre := hpreE) C hKE
    exact ⟨hD, hpreD, hKD, j, hj, D, f ≫ g, by rw [Category.assoc, hg, reassoc_of% hf],
      hC.comp hDsub⟩

/-- Descend a numbered nodal anticanonical boundary along a projection presented
as a closed-point blowup tower by an isomorphism over the field. The resulting
numbering is on the schematic image under the given projection. -/
theorem exists_numbering_of_anticanonical_boundary_tower_blowdown_of_iso
    {Y Z : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)
    [Z.Over SpecK] [SmoothOfRelativeDimension 2 (Z ↘ SpecK)]
    (e : Z ≅ Y) {f : Z ⟶ X} [f.IsOver SpecK] (he : e.hom ≫ T.toBase = f)
    {B : Z.IdealSheafData} (hB : B.IsEffectiveCartier) [PrestableFamily (B.subscheme ↘ SpecK)]
    {m : ℕ} [NeZero m] {ι : Type v} {a : ι → (B.subscheme ↘ SpecK).smoothLocus}
    (A : Scheme.NodalCycleNumbering a m) (hcan : mk hB.toInvertibleSheaf = K[Z]) :
    let D := B.map f
    ∃ (hD : D.IsEffectiveCartier) (_ : PrestableFamily (D.subscheme ↘ SpecK)),
      mk hD.toInvertibleSheaf = K[X] ∧
      ∃ (l : ℕ) (_ : NeZero l)
        (C : Scheme.NodalCycleNumbering
          (fun x : PEmpty.{v + 1} ↦ x.elim : PEmpty.{v + 1} → (D.subscheme ↘ SpecK).smoothLocus) l)
        (g : B.subscheme ⟶ D.subscheme),
        g ≫ D.subschemeι = B.subschemeι ≫ f ∧ g.IsOrientedCycleSubdivision A C := by
  let : Y.Over SpecK := ⟨T.toBase ≫ (X ↘ SpecK)⟩
  let hSm : SmoothOfRelativeDimension 2 (Y ↘ SpecK) := hT.smoothOfRelativeDimension (X ↘ SpecK)
  have : e.inv.IsOver SpecK := ⟨by
    rw [← comp_over f SpecK, ← he, Category.assoc, Iso.inv_hom_id_assoc]
    rfl⟩
  let B' := B.comap e.inv
  have hB' : B'.IsEffectiveCartier := hB.comap e.inv
  obtain ⟨d, hd⟩ := B.exists_iso_of_comap_eq_ker e.symm B'.subschemeι B'.ker_subschemeι.symm
  simp only [Iso.symm_hom] at hd
  have hd' : d.hom ≫ B.subschemeι ≫ f = B'.subschemeι ≫ T.toBase := by
    rw [reassoc_of% hd, ← he, Iso.inv_hom_id_assoc]
  have hdOver : d.hom ≫ (B.subscheme ↘ SpecK) = (B'.subscheme ↘ SpecK) := by
    rw [B.over_eq_subschemeι_comp, B'.over_eq_subschemeι_comp, reassoc_of% hd,
      comp_over]
  let : d.symm.hom.IsOver SpecK := ⟨by rw [Iso.symm_hom, ← hdOver, Iso.inv_hom_id_assoc]⟩
  let hpre' : PrestableFamily (B'.subscheme ↘ SpecK) := by
    rw [← hdOver]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily) d.hom _).mpr
      inferInstance
  let : PrestableFamily (B'.subscheme ↘ SpecK) := hpre'
  let A' := d.symm.mapNodalCycleNumbering A (q := fun x : PEmpty.{v + 1} ↦ x.elim)
  have hA' : d.inv.IsOrientedCycleSubdivision A A' :=
    d.symm.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one A A' (by simp [A'])
  have hcan' : mk hB'.toInvertibleSheaf = K[Y] := by
    rw [← hB.pullback_mk_toInvertibleSheaf hB', hcan, pullback_mk, mk_pullback_canonicalBundle]
  have hmap : B'.map T.toBase = B.map f := by
    rw [map, ← hd', Scheme.Hom.ker_comp_of_isIso, map]
  dsimp only
  rw [← hmap]
  obtain ⟨hD, hpre, hK, l, hl, C, g, hg, hC⟩ :=
    hT.exists_numbering_of_anticanonical_boundary_tower_blowdown hB' (Y ↘ SpecK) rfl (_hSm := hSm)
      (_hPre := hpre') A' hcan'
  exact ⟨hD, hpre, hK, l, hl, C, d.inv ≫ g,
    by rw [Category.assoc, hg, ← hd', Iso.inv_hom_id_assoc], hA'.comp hC⟩

end QPainleve.BlowupTower.IsClosedPointTower

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

open QPainleve.BlowupTower

variable {k : Type u} [Field k] [IsAlgClosed k] [NeZero (2 : k)]

variable {X Z : Scheme.{u}} [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [Z.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k))]
  {p : X} {f : Z ⟶ X} [f.IsOver (Spec (.of k))] {B : Z.IdealSheafData}

local notation "S" => Spec (CommRingCat.of k)
local notation "K[" Y "]" => LineBundleClass.mk (QPainleve.canonicalBundle k Y 2)

local notation "I" => Scheme.Hom.ker (X.fromSpecResidueField p)

/-- Contracting a boundary component of a numbered nodal anticanonical cycle by
a closed-point blowdown removes exactly one component and preserves the oriented
subdivision on the remaining branches. -/
theorem exists_numbering_of_exceptional_boundary_contraction
    (hB : B.IsEffectiveCartier) [PrestableFamily (B.subscheme ↘ S)]
    {m : ℕ} [NeZero m] {ι : Type v} {a : ι → (B.subscheme ↘ S).smoothLocus}
    (A : Scheme.NodalCycleNumbering a m) (hcan : LineBundleClass.mk hB.toInvertibleSheaf = K[Z])
    (hp : IsClosed ({p} : Set X)) (e : Z ≅ (I).blowup)
    (he : e.hom ≫ (I).blowupToBase = f) (hF : ((I).comap f).support ≤ B.support) :
    let D := B.map f
    ∃ (hD : D.IsEffectiveCartier) (_ : PrestableFamily (D.subscheme ↘ S)),
      LineBundleClass.mk hD.toInvertibleSheaf = K[X] ∧
      D.comap f = B * (I).comap f ∧
      ∃ (l : ℕ) (_ : NeZero l),
        m = l + 1 ∧
        ∃ (C : Scheme.NodalCycleNumbering
            (fun x : PEmpty.{v + 1} ↦ x.elim : PEmpty.{v + 1} → (D.subscheme ↘ S).smoothLocus) l)
          (g : B.subscheme ⟶ D.subscheme),
          g ≫ D.subschemeι = B.subschemeι ≫ f ∧ g.IsOrientedCycleSubdivision A C := by
  let T := QPainleve.BlowupTower.nil.snoc (I)
  have hT : IsClosedPointTower X T := .snoc .nil p hp rfl
  have hπ : T.toBase = (I).blowupToBase := by simp [T]
  have h : e.hom ≫ T.toBase = f := by simpa only [hπ] using he
  obtain ⟨hD, hpre, hK, l, hl, C, g, hg, hC⟩ :=
    hT.exists_numbering_of_anticanonical_boundary_tower_blowdown_of_iso e h hB A hcan
  let : NeZero l := hl
  let D := B.map f
  let : PrestableFamily (D.subscheme ↘ S) := hpre
  let π := (I).blowupToBase
  have hN : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ Z ↘ S) := by
    rw [← B.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  obtain ⟨_, -, -, htotal⟩ := hT.anticanonical_nodal_boundary_blowdown k e h hB hN hcan
  have hr : hT.ramificationIdealSheafToBase k = (I).comap π := by
    rw [IsClosedPointTower.ramificationIdealSheafToBase_snoc,
      IsClosedPointTower.ramificationIdealSheafToBase_nil, comap_top, ← one_eq_top, mul_one]
  rw [hr, ← comap_comp, he] at htotal
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  have : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
  have : IsProper f := h ▸ inferInstanceAs (IsProper (e.hom ≫ T.toBase))
  have : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ S)
  have hsurj : Function.Surjective f := h ▸ (e.hom ≫ T.toBase).surjective
  obtain ⟨z, hz⟩ := hsurj p
  have hzB : z ∈ B.support := hF (by
    rw [support_comap, ← SetLike.mem_coe, Closeds.coe_preimage, Set.mem_preimage, hz,
      X.support_ker_fromSpecResidueField_of_isClosed hp]
    exact Set.mem_singleton p)
  have hpD : p ∈ D.support := by
    dsimp only [D]
    rw [← hz, ← SetLike.mem_coe, support_map, Closeds.coe_closure]
    exact subset_closure (Set.mem_image_of_mem f hzB)
  have htot' := congrArg (fun J : Z.IdealSheafData ↦ J.comap e.inv) htotal
  have hf : e.inv ≫ f = π := by rw [← he, e.inv_hom_id_assoc]
  simp only [← comap_comp, comap_mul, hf] at htot'
  have hF' : ((I).comap π).support ≤ (B.comap e.inv).support := by
    rw [← hf, comap_comp, support_comap ((I).comap f), support_comap B]
    apply SetLike.coe_subset_coe.mp
    rw [Closeds.coe_preimage, Closeds.coe_preimage]
    exact Set.preimage_mono (SetLike.coe_subset_coe.mpr hF)
  have hcard := D.ncard_boundaryPrimes_of_totalTransform (X ↘ S) hp hpD hD
    (hB.comap e.inv) htot'
  have hBcard := ncard_boundaryPrimes_eq_of_iso e.symm B
  rw [Iso.symm_hom] at hBcard
  rw [ite_eq_left hF', add_zero, hBcard] at hcard
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr (A.boundaryPrimeEquiv hB), Nat.card_zmod,
    ← Nat.card_coe_set_eq, ← Nat.card_congr (C.boundaryPrimeEquiv hD), Nat.card_zmod] at hcard
  exact ⟨hD, hpre, hK, htotal, l, hl, hcard, C, g, hg, hC⟩

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
