/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic

import QPainleve.AlgebraicGeometry.Curves.Node.BoundaryRestriction
import QPainleve.AlgebraicGeometry.Curves.Node.NormalizationComponent
import TauCeti.AlgebraicGeometry.Pullback.Carrier

/-!
# Orientation and fixed branches of numbered nodal cycles

An orientation-preserving automorphism fixing the ambient boundary primes has identity
dihedral action on the cycle. The identity action fixes the individual points on the
normalization over the nodes, via the conductor square.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup TopologicalSpace TauCeti.AlgebraicGeometry

universe u v

namespace CategoryTheory.Iso

variable {k : Type u} [Field k] [IsSepClosed k] {C : Scheme.{u}} [C.Over (Spec (.of k))]
  [PrestableFamily (C ↘ Spec (.of k))] {n : ℕ} [NeZero n]
  {ι : Type v} {marks : ι → (C ↘ Spec (.of k)).smoothLocus}

local notation "I" => Scheme.singularLocus k C
local notation "ν" => Scheme.IdealSheafData.blowupToBase I
local notation "N" => Scheme.IdealSheafData.blowup I

/-- When a boundary automorphism has identity dihedral action, it fixes every
point of the normalization lying over a node. -/
theorem fixes_normalization_branches_of_boundaryCycleAction_eq_one
    (d : C ≅ C) [d.hom.IsOver (Spec (.of k))] (numbering : Scheme.NodalCycleNumbering marks n)
    (h : d.boundaryCycleAction numbering numbering = 1) (y : N)
    (hy : ν y ∈ (I).support) : (d.singularLocusBlowupIso (R := k)).hom y = y := by
  have hrange : Set.range (C.branchSchemeToBlowup k) = (ν) ⁻¹' Set.range (I).subschemeι :=
    Scheme.Pullback.range_snd_of_isPullback (C.isPullback_branchScheme k)
  rw [(I).range_subschemeι] at hrange
  obtain ⟨b, rfl⟩ := hrange.symm ▸ (show y ∈ (ν) ⁻¹' ((I).support : Set C) from hy)
  obtain ⟨⟨j, a⟩, rfl⟩ := numbering.branch.surjective b
  have hb := d.branch_boundaryCycleAction numbering numbering j a
  rw [h, map_one, Equiv.Perm.one_apply] at hb
  rw [← Scheme.Hom.comp_apply, ← d.branchSchemeIso_hom_branchSchemeToBlowup (R := k),
    Scheme.Hom.comp_apply, ← hb]

end CategoryTheory.Iso

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
