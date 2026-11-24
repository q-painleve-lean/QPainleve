/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Boundary
public import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Automorphism
import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Orientation
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Smooth
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Lifting branch-fixing automorphisms through nodal blowups

An automorphism of a surface and its nodal boundary which fixes all boundary
branches lifts through any specified tower of blowups at boundary nodes. The
induction retains fixation of the branches of the reduced total boundary.
For a nef square-zero boundary cycle, Picard triviality and orientation
preservation suffice for this lift.

This supplies the lift through toric blowups in the proof of Proposition 2.6 of
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData Scheme.Hom

universe u v

namespace QPainleve.BlowupTower

variable {k : Type u} [Field k] [IsSepClosed k] [PerfectField k]
  {X Y : Scheme.{u}}

omit [IsSepClosed k] [PerfectField k] in
private theorem fixes_node_of_fixesBranches {C : Scheme.{u}} {s : C ⟶ Spec (.of k)}
    {hN : AtWorstNodalOfRelativeDimensionOne s} {d : C ≅ C} {hd : d.hom ≫ s = s}
    (hbranches : d.FixesNodalBranches s hN hd) (p : C) (hp : s.IsNodeAt p) : d.hom p = p := by
  let : C.Over (Spec (.of k)) := ⟨s⟩
  let : d.hom.IsOver (Spec (.of k)) := ⟨hd⟩
  have : SyntomicOfRelativeDimension 1 (C ↘ Spec (.of k)) := hN.syntomic
  have : Surjective (C.singularLocus k).blowupToBase :=
    C.surjective_blowupToBase_singularLocus (K := k) hN
  obtain ⟨y, rfl⟩ := (C.singularLocus k).blowupToBase.surjective p
  have hy := (C.mem_support_singularLocus_iff_notMem_smoothLocus (R := k) _).mpr
    ((s.isNodeAt_iff_notMem_smoothLocus hN _).mp hp)
  have hh := (d.fixesNodalBranches_iff s hN hd).mp hbranches y hy
  have hcomm := congrArg (fun f : (C.singularLocus k).blowup ⟶ C ↦ f y)
    (d.singularLocusBlowupIso_hom_blowupToBase (R := k))
  simpa only [Scheme.Hom.comp_apply, hh] using hcomm.symm

section Step

variable [X.Over (Spec (.of k))] [IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] {D : X.IdealSheafData}
  (hD : D.IsEffectiveCartier)
  (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ Spec (.of k)))
  (e : X ≅ X) (he : e.hom ≫ X ↘ Spec (.of k) = (X ↘ Spec (.of k)))
  (d : D.subscheme ≅ D.subscheme) (hd : d.hom ≫ D.subschemeι = D.subschemeι ≫ e.hom)
  (hdOver : d.hom ≫ D.subschemeι ≫ X ↘ Spec (.of k) = D.subschemeι ≫ X ↘ Spec (.of k))
  {p : D.subscheme} (hp : IsClosed ({D.subschemeι p} : Set X))
  (hpN : (D.subschemeι ≫ X ↘ Spec (.of k)).IsNodeAt p)

local notation "I" =>
  vanishingIdeal (Closeds.mk (closure (Set.singleton (D.subschemeι p))) isClosed_closure)
local notation "π" => blowupToBase (I)
local notation "R" => radical (D.comap (π))

include hD he hd hp hpN in
private theorem exists_blowupIso_fixesBranches
    (hb : d.FixesNodalBranches (D.subschemeι ≫ X ↘ Spec (.of k)) hN hdOver)
    (hR : AtWorstNodalOfRelativeDimensionOne ((R).subschemeι ≫ (π) ≫ X ↘ Spec (.of k))) :
    ∃ (hI : (I).comap e.hom = I) (r : (R).subscheme ≅ (R).subscheme),
      r.hom ≫ (R).subschemeι = (R).subschemeι ≫ (blowupIso e hI.symm).hom ∧
      ∃ hr : r.hom ≫ (R).subschemeι ≫ (π) ≫ X ↘ Spec (.of k) =
          (R).subschemeι ≫ (π) ≫ X ↘ Spec (.of k),
        r.FixesNodalBranches _ hR hr := by
  let : D.subscheme.Over (Spec (.of k)) := ⟨D.subschemeι ≫ X ↘ Spec (.of k)⟩
  let : d.hom.IsOver (Spec (.of k)) := ⟨hdOver⟩
  have hqfix := fixes_node_of_fixesBranches hb p hpN
  have hI : (I).comap e.hom = I := comap_nodeIdeal_eq_of_iso D.subschemeι D.subschemeι d e hd hqfix
  obtain ⟨r, hr⟩ := D.exists_radicalComapSubschemeIso (π) hd (blowupIso_hom_blowupToBase e hI.symm)
  have hover : r.hom ≫ (R).subschemeι ≫ (π) ≫ X ↘ Spec (.of k) =
      (R).subschemeι ≫ (π) ≫ X ↘ Spec (.of k) := by
    rw [reassoc_of% hr, blowupIso_hom_blowupToBase_assoc, he]
  refine ⟨hI, r, hr, hover, ?_⟩
  let : (R).subscheme.Over (Spec (.of k)) := ⟨(R).subschemeι ≫ (π) ≫ X ↘ Spec (.of k)⟩
  let : r.hom.IsOver (Spec (.of k)) := ⟨hover⟩
  have : SyntomicOfRelativeDimension 1 (D.subscheme ↘ Spec (.of k)) := hN.syntomic
  have hqsing : p ∈ (D.subscheme.singularLocus k).support :=
    (D.subscheme.mem_support_singularLocus_iff_notMem_smoothLocus p).mpr
      (((D.subschemeι ≫ X ↘ Spec (.of k)).isNodeAt_iff_notMem_smoothLocus hN p).mp hpN)
  apply (r.fixesNodalBranches_iff _ hR hover).mpr
  exact hD.singularLocusBlowupIso_fixes_over_nodeBlowup hN hqsing hp e d hd hqfix r hR
    hr rfl rfl ((d.fixesNodalBranches_iff _ hN hdOver).mp hb)

end Step

section Tower

variable [X.Over (Spec (.of k))] [IsIntegral X] [IsNoetherian X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] {D : X.IdealSheafData}
  (hD : D.IsEffectiveCartier)
  (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ Spec (.of k)))
  (e : X ≅ X) (d : D.subscheme ≅ D.subscheme) (he : e.hom ≫ X ↘ Spec (.of k) = (X ↘ Spec (.of k)))
  (hd : d.hom ≫ D.subschemeι = D.subschemeι ≫ e.hom)
  (hdOver : d.hom ≫ D.subschemeι ≫ X ↘ Spec (.of k) = D.subschemeι ≫ X ↘ Spec (.of k))

include hD hN he hd hdOver in
private theorem exists_isLift_aux
    (hb : d.FixesNodalBranches (D.subschemeι ≫ X ↘ Spec (.of k)) hN hdOver)
    {n : ℕ} {T : BlowupTower X n Y}
    (hT : IsNodalBoundaryTower D (X ↘ Spec (.of k)) (𝟙 X) T)
    {P : Y.IdealSheafData} (hP : P = (D.comap T.toBase).radical)
    (hNP : AtWorstNodalOfRelativeDimensionOne (P.subschemeι ≫ T.toBase ≫ X ↘ Spec (.of k))) :
    ∃ (g : Y ≅ Y) (r : P.subscheme ≅ P.subscheme),
      IsLift e T T g ∧ r.hom ≫ P.subschemeι = P.subschemeι ≫ g.hom ∧
      ∃ hr : r.hom ≫ P.subschemeι ≫ T.toBase ≫ X ↘ Spec (.of k) =
          P.subschemeι ≫ T.toBase ≫ X ↘ Spec (.of k),
        r.FixesNodalBranches _ hNP hr := by
  induction hT with
  | nil =>
    have : IsReduced D.subscheme := hN.isReduced
    have heq : P = D := by
      simpa only [toBase_nil, comap_id, D.isReduced_subscheme_iff_radical_eq.mp inferInstance]
        using hP
    clear hP
    subst P
    have hd' : d.hom ≫ D.subschemeι ≫ (nil (X := X)).toBase ≫ X ↘ Spec (.of k) =
        D.subschemeι ≫ (nil (X := X)).toBase ≫ X ↘ Spec (.of k) := by
      simpa only [toBase_nil, Category.id_comp] using hdOver
    exact ⟨e, d, IsLift.nil_iff.mpr rfl, hd, hd', by
      simpa only [toBase_nil, Category.id_comp] using hb⟩
  | @snoc m Z U J hU p hp hJ hpN ih =>
    let f := U.toBase ≫ X ↘ Spec (.of k)
    let Q := (D.comap U.toBase).radical
    let : Z.Over (Spec (.of k)) := ⟨f⟩
    have hfo : Z ↘ Spec (.of k) = f := rfl
    have : IsProper U.toBase := U.isProper_toBase
    have : QuasiCompact (Z ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact f)
    have : IsIntegral Z := hU.isClosedPointTower.isIntegral (X ↘ Spec (.of k))
    have : SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k)) :=
      hU.isClosedPointTower.smoothOfRelativeDimension (X ↘ Spec (.of k))
    obtain ⟨hQ, hnQ⟩ := IsNodalBoundaryTower.radical_comap_toBase hU hD hN
    obtain ⟨g, a, hg, ha, haOver, hqa⟩ := ih (P := Q) rfl hnQ
    have hgOver : g.hom ≫ Z ↘ Spec (.of k) = (Z ↘ Spec (.of k)) := by
      rw [hfo, hg.hom_toBase_assoc, he]
    have hnode : Q.IsNodeOfReducedBoundary (Z ↘ Spec (.of k)) p := by
      simpa only [Q, hfo, f, isNodeOfReducedBoundary_radical, Category.comp_id] using hpN
    have : IsReduced Q.subscheme := hnQ.isReduced
    obtain ⟨q, hq, hqN⟩ := (Q.isNodeOfReducedBoundary_iff_of_isReduced _ _).mp hnode
    subst p
    let J' :=
      vanishingIdeal (Closeds.mk (closure (Set.singleton (Q.subschemeι q))) isClosed_closure)
    have hJ' : J = J' := hJ.trans (Z.ker_fromSpecResidueField_eq_vanishingIdeal (Q.subschemeι q))
    clear hJ
    subst J
    have hP' : P = (Q.comap J'.blowupToBase).radical := by
      rw [hP, toBase_snoc, comap_comp, ← vanishingIdeal_support,
        ← vanishingIdeal_support (I := Q.comap _), support_comap, support_comap Q]
      rfl
    clear hP
    subst P
    have hNP' : AtWorstNodalOfRelativeDimensionOne
        ((Q.comap J'.blowupToBase).radical.subschemeι ≫ J'.blowupToBase ≫ Z ↘ Spec (.of k)) := by
      simpa only [toBase_snoc, Category.assoc, hfo, f] using hNP
    obtain ⟨hJ, r, hr, hrOver, hrB⟩ := exists_blowupIso_fixesBranches
      hQ hnQ g hgOver a ha haOver hp hqN hqa hNP'
    refine ⟨_, r, hg.snoc hJ, hr, ?_⟩
    simp only [toBase_snoc, Category.assoc]
    exact ⟨hrOver, hrB⟩

omit [AlgebraicGeometry.IsNoetherian X] in
include he hd hD in
/-- A surface automorphism compatible with a branch-fixing automorphism of its nodal
boundary lifts through a specified tower of closed nodal blowups. -/
theorem IsNodalBoundaryTower.exists_isLift_of_fixes_nodal_branches
    {n : ℕ} {T : BlowupTower X n Y} (hT : IsNodalBoundaryTower D (X ↘ Spec (.of k)) (𝟙 X) T)
    (hfix :
      letI : D.subscheme.Over (Spec (.of k)) := ⟨D.subschemeι ≫ X ↘ Spec (.of k)⟩
      letI : d.hom.IsOver (Spec (.of k)) := ⟨
        ((reassoc_of% hd) _).trans (congrArg (D.subschemeι ≫ ·) he)⟩
      letI : SyntomicOfRelativeDimension 1 (D.subscheme ↘ Spec (.of k)) := hN.syntomic
      ∀ y : (D.subscheme.singularLocus k).blowup,
        (D.subscheme.singularLocus k).blowupToBase y ∈ (D.subscheme.singularLocus k).support →
          (d.singularLocusBlowupIso (R := k)).hom y = y) :
    ∃! g : Y ≅ Y, IsLift e T T g := by
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  have hdOver : d.hom ≫ D.subschemeι ≫ X ↘ Spec (.of k) =
      D.subschemeι ≫ X ↘ Spec (.of k) := by
    rw [← Category.assoc, hd, Category.assoc, he]
  have hb := (d.fixesNodalBranches_iff _ hN hdOver).mpr hfix
  obtain ⟨g, _, hg, -⟩ := exists_isLift_aux hD hN e d he hd hdOver hb hT rfl
    (hT.radical_comap_toBase hD hN).2
  exact ⟨g, hg, fun _ hh ↦ hh.unique hg⟩

end Tower

end QPainleve.BlowupTower

namespace QPainleve.BlowupTower.IsNodalBoundaryTower

open DihedralGroup LineBundleClass


variable {k : Type u} [Field k] {X : Scheme.{u}}
  {D : X.IdealSheafData} {n : ℕ} [NeZero n]

local notation "s" => (X ↘ Spec (CommRingCat.of k))

variable [IsAlgClosed k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

/-- A Picard-trivial, orientation-preserving automorphism of a nef square-zero nodal
boundary cycle lifts uniquely through any specified tower of blowups at boundary nodes. -/
theorem existsUnique_isLift_of_picard_trivial_of_preserves_orientation
    {Y : Scheme.{u}} {m : ℕ} {T : BlowupTower X m Y}
    (hT : IsNodalBoundaryTower D s (𝟙 X) T)
    (hD : D.IsEffectiveCartier) (e : X ≅ X) [e.hom.IsOver (Spec (.of k))]
    (d : D.subscheme ≅ D.subscheme) (hd : d.hom ≫ D.subschemeι = D.subschemeι ≫ e.hom)
    (hPic : ∀ L, LineBundleClass.pullback e.hom L = L)
    (hnef : ((mk hD.toInvertibleSheaf)⁻¹).IsNef k s)
    (hsq : Chow.classIntersectionNumber k X (mk hD.toInvertibleSheaf)⁻¹
      (mk hD.toInvertibleSheaf)⁻¹ = 0) :
    letI : d.hom.IsOver (Spec (.of k)) := ⟨by
      rw [D.over_eq_subschemeι_comp, reassoc_of% hd, comp_over]⟩
    ∀ [PrestableFamily (D.subscheme ↘ Spec (.of k))] {ι : Type v}
      {marks : ι → (D.subscheme ↘ Spec (.of k)).smoothLocus}
      (numbering : Scheme.NodalCycleNumbering marks n),
      cycleOrientationSign (d.boundaryCycleAction numbering numbering) = 1 →
      ∃! g : Y ≅ Y, IsLift e T T g := by
  have : d.hom.IsOver (Spec (.of k)) :=
    ⟨by rw [D.over_eq_subschemeι_comp, reassoc_of% hd, comp_over]⟩
  intro _ ι marks numbering horient
  have hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s) := by
    rw [← D.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have he := comp_over e.hom (Spec (.of k))
  have hm := (hD.mem_picardNodalBoundaryAut_iff_preserves_orientation
    (Aut.of e) he d hd numbering hnef hsq).mpr ⟨hPic, horient⟩
  have hb := D.fixesNodalBranches_of_mem_picardNodalBoundaryAut hN he hm d hd
  exact hT.exists_isLift_of_fixes_nodal_branches hD hN e d he hd
    ((d.fixesNodalBranches_iff _ hN _).mp hb)

end QPainleve.BlowupTower.IsNodalBoundaryTower
