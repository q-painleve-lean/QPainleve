/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.FixedBranches
public import QPainleve.AlgebraicGeometry.Curves.Node.GenericPoint
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic

import QPainleve.AlgebraicGeometry.Curves.Node.BoundaryRestriction

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

/-- An automorphism fixes every branch of a numbered nodal cycle exactly when its
dihedral action is the identity. -/
theorem fixesNodalBranches_iff_boundaryCycleAction_eq_one
    (d : C ≅ C) [d.hom.IsOver (Spec (.of k))] (numbering : Scheme.NodalCycleNumbering marks n) :
    d.FixesNodalBranches (C ↘ Spec (.of k))
      PrestableFamily.atWorstNodalOfRelativeDimensionOne (HomIsOver.comp_over (f := d.hom)) ↔
      d.boundaryCycleAction numbering numbering = 1 := by
  -- Match the `Over` instance built by `FixesNodalBranches` from the structure map.
  cases ‹C.Over (Spec (.of k))› with
  | ofHom f =>
    let : C.Over (Spec (.of k)) := ⟨f⟩
    rw [fixesNodalBranches_iff_branchScheme]
    constructor
    · intro hfix
      apply (d.existsUnique_boundaryCycleAction numbering (D := numbering)).unique
        (d.branch_boundaryCycleAction numbering numbering)
      intro j b
      rw [map_one, Equiv.Perm.one_apply]
      exact (hfix (numbering.branch (j, b))).symm
    · intro h b
      obtain ⟨⟨j, a⟩, rfl⟩ := numbering.branch.surjective b
      have hb := d.branch_boundaryCycleAction numbering numbering j a
      rw [h, map_one, Equiv.Perm.one_apply] at hb
      exact hb.symm

end CategoryTheory.Iso

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {k : Type u} [Field k] {X : Scheme.{u}}
  {D : X.IdealSheafData} {n : ℕ} [NeZero n]

variable [IsSepClosed k] [IsLocallyNoetherian X] [X.Over (Spec (.of k))]
  [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  {ι : Type v} {marks : ι → (D.subscheme ↘ Spec (.of k)).smoothLocus}

local notation "C" => (D.subscheme)

/-- If the action on a numbered boundary cycle is the identity, the ambient
isomorphism fixes each prime of the boundary at its generic point. -/
theorem fixes_components_of_boundaryCycleAction_eq_one
    (hD : D.IsEffectiveCartier) (e : X ≅ X) (d : C ≅ C)
    (hd : d.hom ≫ D.subschemeι = D.subschemeι ≫ e.hom)
    [d.hom.IsOver (Spec (.of k))] (numbering : Scheme.NodalCycleNumbering marks n)
    (ha : d.boundaryCycleAction numbering numbering = 1)
    (p : CodimensionOnePoint X) (hp : (p : X) ∈ D.support) : e.hom p = p := by
  obtain ⟨v, hv⟩ := hD.exists_subschemeι_blowupComponentGeneric_eq (k := k) hp
  obtain ⟨j, rfl⟩ := numbering.component.surjective v
  rw [← numbering.componentGenericPoint_def] at hv
  have he := d.apply_componentGenericPoint numbering numbering j
  rw [ha, map_one, Equiv.Perm.one_apply] at he
  rw [← hv, ← Scheme.Hom.comp_apply, ← hd, Scheme.Hom.comp_apply, he]

/-- An orientation-preserving automorphism fixing the ambient boundary primes acts
as the identity on the numbered boundary cycle, including its individual branches. -/
theorem boundaryCycleAction_eq_one_of_fixes_components
    (hD : D.IsEffectiveCartier) (e : X ≅ X) (d : C ≅ C)
    (hd : d.hom ≫ D.subschemeι = D.subschemeι ≫ e.hom)
    [d.hom.IsOver (Spec (.of k))] (numbering : Scheme.NodalCycleNumbering marks n)
    (hfix : ∀ x : CodimensionOnePoint X, (x : X) ∈ D.support → e.hom x = x)
    (horient : cycleOrientationSign (d.boundaryCycleAction numbering numbering) = 1) :
    d.boundaryCycleAction numbering numbering = 1 := by
  let x := numbering.componentGenericPoint 0
  obtain ⟨p, hp, hprime⟩ := hD.range_blowupComponent_comp_subschemeι (k := k)
    (numbering.component 0)
  rw [D.subscheme.range_blowupComponent_comp _ _ D.subschemeι.isClosedMap,
    ← numbering.componentGenericPoint_def] at hprime
  have hx : D.subschemeι x = p.val :=
    isGenericPoint_closure.eq (hprime.symm ▸ isGenericPoint_closure)
  have hdx : d.hom x = x := by
    apply D.subschemeι.injective
    rw [← Scheme.Hom.comp_apply, hd, Scheme.Hom.comp_apply, hx]
    exact hfix p hp
  have hvertex := numbering.componentGenericPoint_injective
    ((d.apply_componentGenericPoint numbering numbering 0).symm.trans hdx)
  exact ((eq_r_iff_cycleVertexPerm_zero_eq horient).mpr hvertex).trans DihedralGroup.one_def.symm

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
