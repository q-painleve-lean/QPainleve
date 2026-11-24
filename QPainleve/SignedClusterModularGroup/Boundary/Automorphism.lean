/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Automorphism
public import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over

import QPainleve.AlgebraicGeometry.Chow.Nef.Boundary
import QPainleve.AlgebraicGeometry.Curves.Node.BoundaryRestriction
import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Orientation
import QPainleve.AlgebraicGeometry.Curves.Node.NormalizationComponent

/-!
# Picard-trivial automorphisms of square-zero boundary cycles

The component classes of a connected nef square-zero boundary are distinct. A Picard-trivial
automorphism preserving the boundary fixes these components. If it also preserves orientation,
it fixes the individual branches and lifts through any specified nodal blowup tower.

This supplies the branch-fixing hypothesis in the reduction through nodal blowups of
[Gross, Hacking and Keel, Proposition 2.6][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup TopologicalSpace TauCeti.AlgebraicGeometry
open QPainleve.BlowupTower
open Scheme.IdealSheafData LineBundleClass

universe u v

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {k : Type u} [Field k] {X : Scheme.{u}}
  {D : X.IdealSheafData} {n : ℕ} [NeZero n]

variable [IsSepClosed k] [IsLocallyNoetherian X] [X.Over (Spec (.of k))]
  [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  {ι : Type v} {marks : ι → (D.subscheme ↘ Spec (.of k)).smoothLocus}

local notation "C" => (D.subscheme)
local notation "I" => Scheme.singularLocus k C
local notation "ν" => Scheme.IdealSheafData.blowupToBase I
local notation "N" => Scheme.IdealSheafData.blowup I

omit [IsSepClosed k] [IsLocallyNoetherian X] in
private theorem eq_of_range_normalizedComponent_comp_subset
    {v w : irreducibleComponents N}
    (h : Set.range (((C).blowupComponent v).ι ≫ ν ≫ D.subschemeι) ⊆
      Set.range (((C).blowupComponent w).ι ≫ ν ≫ D.subschemeι)) : v = w := by
  apply (C).eq_of_range_blowupComponent_subset
  apply (Set.image_subset_image_iff D.subschemeι.injective).mp
  have hrange (a : irreducibleComponents N) :
      Set.range (((C).blowupComponent a).ι ≫ ν ≫ D.subschemeι) =
        D.subschemeι '' Set.range (((C).blowupComponent a).ι ≫ ν) := by
    rw [← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  simpa only [hrange] using h

/-- An orientation-preserving automorphism fixing the ambient boundary primes acts
as the identity on the numbered boundary cycle, including its individual branches. -/
theorem boundaryCycleAction_eq_one_of_fixes_components
    (hD : D.IsEffectiveCartier) (e : X ≅ X) (d : C ≅ C)
    (hd : d.hom ≫ D.subschemeι = D.subschemeι ≫ e.hom)
    [d.hom.IsOver (Spec (.of k))] (numbering : Scheme.NodalCycleNumbering marks n)
    (hfix : ∀ x : CodimensionOnePoint X, (x : X) ∈ D.support → e.hom x = x)
    (horient : cycleOrientationSign (d.boundaryCycleAction numbering numbering) = 1) :
    d.boundaryCycleAction numbering numbering = 1 := by
  let action := d.boundaryCycleAction numbering numbering
  let v := numbering.component 0
  let w := numbering.component (cycleVertexPerm action 0)
  let A := (d.singularLocusBlowupIso (R := k)).hom
  let f := ν ≫ D.subschemeι
  have hcomp : A ≫ f = f ≫ e.hom := by
    dsimp only [A, f]
    rw [← Category.assoc, d.singularLocusBlowupIso_hom_blowupToBase,
      Category.assoc, hd, Category.assoc]
  have hcomm (x : N) : f (A x) = e.hom (f x) :=
    congrArg (fun m : N ⟶ X ↦ m x) hcomp
  have hrange (a : irreducibleComponents N) :
      Set.range (((C).blowupComponent a).ι ≫ f) = f '' (a : Set N) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      (C).coe_blowupComponent]
  have hmap : (w : Set N) = A '' (v : Set N) :=
    d.component_boundaryCycleAction numbering numbering 0
  obtain ⟨p, hp, hprime⟩ := hD.range_blowupComponent_comp_subschemeι (k := k) v
  have hprime' : f '' (v : Set N) = closure {(p : X)} := (hrange v).symm.trans hprime
  have hclosure : e.hom '' closure {(p : X)} = closure {(p : X)} := by
    have h := (Scheme.homeoOfIso e).image_closure ({(p : X)} : Set X)
    have he : (Scheme.homeoOfIso e : X → X) = e.hom :=
      funext (Scheme.homeoOfIso_apply e)
    simpa only [he, Set.image_singleton, hfix p hp] using h
  have himage : f '' (w : Set N) = f '' (v : Set N) := by
    calc
      f '' (w : Set N) = e.hom '' (f '' (v : Set N)) := by
        rw [hmap, Set.image_image, Set.image_image]
        exact congrArg (fun m : N → X ↦ m '' (v : Set N)) (funext hcomm)
      _ = f '' (v : Set N) := by rw [hprime', hclosure]
  have hv : cycleVertexPerm action 0 = 0 := by
    apply numbering.component.injective
    exact eq_of_range_normalizedComponent_comp_subset (k := k) (D := D) (v := w) (w := v)
      (((hrange w).trans (himage.trans (hrange v).symm)).le)
  cases hg : action with
  | r a =>
    simp only [hg, cycleVertexPerm_r_apply, zero_add] at hv
    exact (hg.trans (congrArg DihedralGroup.r hv)).trans DihedralGroup.one_def.symm
  | sr a =>
    have : (-1 : ℤˣ) = 1 := (cycleOrientationSign_sr a).symm.trans
      ((congrArg cycleOrientationSign hg).symm.trans horient)
    exact (by decide : (-1 : ℤˣ) ≠ 1) this |>.elim

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

namespace QPainleve.BlowupTower.IsNodalBoundaryTower

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
    (hPic : ∀ L, pullback e.hom L = L)
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
  have : IsNoetherian X := isNoetherian_of_finiteType s
  have hN := PrestableFamily.atWorstNodalOfRelativeDimensionOne
    (f := D.subscheme ↘ Spec (.of k))
  have hpb : IsPullback D.subschemeι d.hom e.hom D.subschemeι :=
    .of_vert_isIso ⟨hd.symm⟩
  have hmap : D.comap e.hom = D := by
    simpa only [ker_subschemeι] using (ker_eq_comap_of_isPullback D.subschemeι hpb).symm
  have : ConnectedSpace D.subscheme :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := D.subscheme ↘ Spec (.of k))
  have hconn : _root_.IsPreconnected (D.support : Set X) := by
    simpa only [Set.image_univ, D.range_subschemeι] using
      isPreconnected_univ.image D.subschemeι D.subschemeι.continuous.continuousOn
  have hfix := hD.fixes_boundary_components_of_picard_trivial hconn hnef hsq e hmap hPic
  have ha := hD.boundaryCycleAction_eq_one_of_fixes_components e d hd numbering hfix horient
  exact hT.exists_isLift_of_fixes_nodal_branches hD hN e d (comp_over e.hom _) hd
    (d.fixes_normalization_branches_of_boundaryCycleAction_eq_one numbering ha)

end QPainleve.BlowupTower.IsNodalBoundaryTower
