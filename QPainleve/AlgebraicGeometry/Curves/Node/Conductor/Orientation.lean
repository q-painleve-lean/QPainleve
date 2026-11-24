/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction

import TauCeti.AlgebraicGeometry.Pullback.Carrier

/-!
# Fixed branches of numbered nodal cycles

The identity dihedral action fixes the individual points on the normalization over
the nodes, via the conductor square.
-/

public section

open AlgebraicGeometry DihedralGroup TauCeti.AlgebraicGeometry

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
