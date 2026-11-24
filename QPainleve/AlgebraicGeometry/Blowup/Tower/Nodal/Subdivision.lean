/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Subdivision
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Boundary

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Oriented subdivisions along nodal blowup towers

A numbering of a nodal boundary cycle lifts through a specified tower of point
blowups at nodes. Every blowup inserts one component in the cycle, including
blowups at self-nodes. The composite projection preserves the order on the
retained conductor branches and therefore preserves periods.

The proof iterates `IdealSheafData.exists_isOrientedCycleSubdivision_nodalBlowup`
using `Scheme.Hom.IsOrientedCycleSubdivision.comp`. For the geometry of nodal
blowups of anticanonical cycles, see [Gross, Hacking and Keel, §1][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S1
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u v w

namespace QPainleve.BlowupTower.IsNodalBoundaryTower

variable {k : Type u} [Field k] [IsSepClosed k] [PerfectField k] {X Y : Scheme.{u}}

variable [X.Over (Spec (.of k))] [IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] {D : X.IdealSheafData}
  [PrestableFamily (D.subscheme ↘ Spec (.of k))] {n m : ℕ} [NeZero n]
  {T : BlowupTower X m Y}
  {ι : Type w} {p : ι → (D.subscheme ↘ Spec (.of k)).smoothLocus}

local notation "R[" T "]" => radical (D.comap (BlowupTower.toBase T))
local notation "boundaryMap(" E "," f ")" =>
  subschemeMap (radical (comap E f)) E f (le_map_iff_comap_le.mpr (le_radical _))

-- Keeping the top ideal and structure morphism independent lets the induction
-- replace the reduced inverse image for a composite by the iterated one.
private abbrev HasSubdivision (A : Scheme.NodalCycleNumbering (k := k) (X := D.subscheme) p n)
    (f : Y ⟶ X) (g : Y ⟶ Spec (.of k)) (E : Y.IdealSheafData) (l : ℕ) : Prop :=
  letI : Y.Over (Spec (.of k)) := ⟨g⟩
  ∀ (h : D.comap f ≤ E) [PrestableFamily (E.subscheme ↘ Spec (.of k))] [NeZero l]
    {ι' : Type v} (p' : ι' → (E.subscheme ↘ Spec (.of k)).smoothLocus),
    ∃ B : Scheme.NodalCycleNumbering (k := k) (X := E.subscheme) p' l,
      (E.subschemeMap D f (le_map_iff_comap_le.mpr h)).IsOrientedCycleSubdivision B A

omit [PerfectField k] [AlgebraicGeometry.IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] in
private theorem hasSubdivision_nil
    (A : Scheme.NodalCycleNumbering (k := k) (X := D.subscheme) p n) :
    HasSubdivision.{u, v, w} A (𝟙 X) (X ↘ Spec (.of k)) D n := by
  intro h _ _ ι' p'
  let over : (Iso.refl D.subscheme).hom.IsOver (Spec (.of k)) := by
    rw [Iso.refl_hom]
    infer_instance
  -- Use the same structure morphism on both copies of the boundary while changing marks.
  let B := @Iso.mapNodalCycleNumbering k _ _ D.subscheme D.subscheme _ _ _ _ ι p ι' p' n _
    (Iso.refl D.subscheme) over A
  have hact : @Iso.boundaryCycleAction k _ _ D.subscheme D.subscheme _ _ _ _ ι' p' ι p n _
      (Iso.refl D.subscheme) over B A = 1 := by
    have hs := @Iso.boundaryCycleAction_symm k _ _ D.subscheme D.subscheme _ _ _ _ ι p ι' p' n _
      (Iso.refl D.subscheme) over A B
    have hforward := @Iso.boundaryCycleAction_mapNodalCycleNumbering
      k _ _ D.subscheme D.subscheme _ _ _ _ ι p ι' p' n _ (Iso.refl D.subscheme) over A
    rw [hforward, inv_one] at hs
    simpa only [Iso.refl_symm] using hs
  have hb : subschemeMap D D (𝟙 X) (le_map_iff_comap_le.mpr h) = 𝟙 D.subscheme := by
    rw [← cancel_mono D.subschemeι]
    simp
  have hsign := congrArg (fun a ↦ DihedralGroup.cycleOrientationSign a) hact
  rw [map_one] at hsign
  exact ⟨B, hb.symm ▸ @Iso.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one
    k _ _ D.subscheme D.subscheme _ _ _ _ ι' ι p' p n _ (Iso.refl D.subscheme) over B A hsign⟩

omit [AlgebraicGeometry.IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] in
private theorem hasSubdivision_blowup
    {Z : Scheme.{u}} {m : ℕ} (A : Scheme.NodalCycleNumbering (k := k) (X := D.subscheme) p n)
    (U : BlowupTower X m Z)
    [IsIntegral Z] [QuasiCompact (U.toBase ≫ X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 2 (U.toBase ≫ X ↘ Spec (.of k))]
    [PrestableFamily ((R[U]).subschemeι ≫ U.toBase ≫ X ↘ Spec (.of k))]
    {z : (R[U]).subscheme} (hz : IsClosed ({(R[U]).subschemeι z} : Set Z))
    (hn : ((R[U]).subschemeι ≫ U.toBase ≫ X ↘ Spec (.of k)).IsNodeAt z)
    (hP : (R[U]).IsEffectiveCartier)
    (ih : HasSubdivision.{u, v, w} A U.toBase (U.toBase ≫ X ↘ Spec (.of k)) (R[U]) (n + m)) :
    let J := vanishingIdeal
      (⟨closure ({(R[U]).subschemeι z} : Set Z), isClosed_closure⟩ : Closeds Z)
    HasSubdivision.{u, v, w} A (J.blowupToBase ≫ U.toBase)
      (J.blowupToBase ≫ U.toBase ≫ X ↘ Spec (.of k))
      ((D.comap U.toBase).comap J.blowupToBase).radical (n + m + 1) := by
  intro J
  have hR : ((D.comap U.toBase).comap J.blowupToBase).radical =
      ((R[U]).comap J.blowupToBase).radical := by
    rw [← vanishingIdeal_support, ← vanishingIdeal_support (I := (R[U]).comap _),
      support_comap (D.comap U.toBase), support_comap (R[U]), support_radical]
  rw [hR]
  intro hmap hpre hlen ι' p'
  let : Z.Over (Spec (.of k)) := ⟨U.toBase ≫ X ↘ Spec (.of k)⟩
  let : J.blowup.Over (Spec (.of k)) := ⟨J.blowupToBase ≫ Z ↘ Spec (.of k)⟩
  have : PrestableFamily (((R[U]).comap J.blowupToBase).radical.subscheme ↘ Spec (.of k)) := hpre
  have : PrestableFamily ((R[U]).subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (PrestableFamily ((R[U]).subschemeι ≫ U.toBase ≫ X ↘ Spec (.of k)))
  have : SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 2 (U.toBase ≫ X ↘ Spec (.of k)))
  have : QuasiCompact (Z ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (U.toBase ≫ X ↘ Spec (.of k)))
  have : NeZero (n + m) := ⟨by have := NeZero.ne n; omega⟩
  obtain ⟨B, hB⟩ := ih (le_radical _) (PEmpty.elim : PEmpty.{v+1} → _)
  have hsing : z ∈ ((R[U]).subscheme.singularLocus k).support :=
    ((R[U]).subscheme.mem_support_singularLocus_iff_notMem_smoothLocus z).mpr
      (fun hs ↦ hn.not_formallySmooth_stalkMap (Scheme.Hom.mem_smoothLocus.mp hs))
  obtain ⟨C, hC⟩ := (R[U]).exists_isOrientedCycleSubdivision_nodalBlowup
    (k := k) hz hsing rfl rfl hP B p'
  have hc :
      boundaryMap(R[U],J.blowupToBase) ≫ boundaryMap(D,U.toBase) =
        subschemeMap _ D (J.blowupToBase ≫ U.toBase) (le_map_iff_comap_le.mpr hmap) := by
    rw [← cancel_mono D.subschemeι]
    simp [Category.assoc]
  exact ⟨C, hc ▸ hC.comp hB⟩

private theorem hasSubdivision_toBase
    (hT : IsNodalBoundaryTower D (X ↘ Spec (.of k)) (𝟙 X) T)
    (hD : D.IsEffectiveCartier) (A : Scheme.NodalCycleNumbering (k := k) (X := D.subscheme) p n) :
    HasSubdivision.{u, v, w} A T.toBase (T.toBase ≫ X ↘ Spec (.of k)) (R[T]) (n + m) := by
  have hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ Spec (.of k)) := by
    rw [← D.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have : IsReduced D.subscheme := hN.isReduced
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  induction hT with
  | nil =>
    rw [toBase_nil, comap_id, Category.id_comp, Nat.add_zero,
      D.isReduced_subscheme_iff_radical_eq.mp ‹IsReduced D.subscheme›]
    exact hasSubdivision_nil A
  | @snoc m Z U I hU x hx hI hnode ih =>
    let : Z.Over (Spec (.of k)) := ⟨U.toBase ≫ X ↘ Spec (.of k)⟩
    have : IsIntegral Z := hU.isClosedPointTower.isIntegral (X ↘ Spec (.of k))
    have : SmoothOfRelativeDimension 2 (U.toBase ≫ X ↘ Spec (.of k)) :=
      hU.isClosedPointTower.smoothOfRelativeDimension (X ↘ Spec (.of k))
    have : IsProper U.toBase := U.isProper_toBase
    have : QuasiCompact (U.toBase ≫ X ↘ Spec (.of k)) :=
      inferInstanceAs (QuasiCompact (U.toBase ≫ X ↘ Spec (.of k)))
    have hpre := prestableFamily_radical_comap_toBase hU hD
    have : PrestableFamily ((R[U]).subscheme ↘ Spec (.of k)) := hpre
    have hnode' : (R[U]).IsNodeOfReducedBoundary (U.toBase ≫ X ↘ Spec (.of k)) x := by
      simpa only [isNodeOfReducedBoundary_radical, Category.comp_id] using hnode
    have : IsReduced ((R[U]).subscheme) :=
      (PrestableFamily.atWorstNodalOfRelativeDimensionOne
        (f := (R[U]).subscheme ↘ Spec (.of k))).isReduced
    obtain ⟨z, hz, hn⟩ :=
      ((R[U]).isNodeOfReducedBoundary_iff_of_isReduced (U.toBase ≫ X ↘ Spec (.of k)) x).mp hnode'
    subst x
    subst I
    rw [Scheme.ker_fromSpecResidueField_eq_vanishingIdeal, toBase_snoc, Category.assoc,
      comap_comp, Nat.add_succ]
    apply hasSubdivision_blowup A U hx hn (radical_comap_toBase hU hD hN).1 ih

/-- The reduced total boundary of a specified tower of m nodal point blowups
has a numbering with n + m components extending any given orientation of the
original n-component boundary. The restricted tower projection is an oriented
conductor subdivision over the ground field for this numbering. The final dual graph may use any
smooth marked points. -/
theorem exists_isOrientedCycleSubdivision_nodalBoundaryTower
    (hT : IsNodalBoundaryTower D (X ↘ Spec (.of k)) (𝟙 X) T)
    (hD : D.IsEffectiveCartier) (A : Scheme.NodalCycleNumbering (k := k) (X := D.subscheme) p n) :
    letI : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ X ↘ Spec (.of k)⟩
    letI : PrestableFamily ((R[T]).subscheme ↘ Spec (.of k)) :=
      hT.prestableFamily_radical_comap_toBase hD
    letI : NeZero (n + m) := ⟨by have := NeZero.ne n; omega⟩
    ∀ {ι' : Type v} (p' : ι' → ((R[T]).subscheme ↘ Spec (.of k)).smoothLocus),
      ∃ B : Scheme.NodalCycleNumbering (k := k) (X := (R[T]).subscheme) p' (n + m),
        (boundaryMap(D,T.toBase)).IsOver (Spec (.of k)) ∧
          (boundaryMap(D,T.toBase)).IsOrientedCycleSubdivision B A := by
  intro ι' p'
  let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ X ↘ Spec (.of k)⟩
  have : PrestableFamily ((R[T]).subscheme ↘ Spec (.of k)) :=
    hT.prestableFamily_radical_comap_toBase hD
  have : NeZero (n + m) := ⟨by have := NeZero.ne n; omega⟩
  obtain ⟨B, hB⟩ := hasSubdivision_toBase hT hD A (le_radical _) p'
  refine ⟨B, ⟨?_⟩, hB⟩
  rw [D.over_eq_subschemeι_comp, ← Category.assoc, subschemeMap_subschemeι, Category.assoc]
  rfl

end QPainleve.BlowupTower.IsNodalBoundaryTower
