/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Fiber.BaseChange
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import TauCeti.AlgebraicGeometry.Cohomology.FieldTower

/-!
# Cohomology of closed fibers over an algebraically closed field

A closed fiber has the same cohomology dimensions over its residue field and the original
base field. This compares the two scalar actions on the same scheme-theoretic fiber.
-/

public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
  [hX : X.Over (Spec (.of k))] [hY : Y.Over (Spec (.of k))]
  (f : X ⟶ Y) [hf : f.IsOver (Spec (.of k))] [hft : LocallyOfFiniteType (Y ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)

include hX hY hf hft in
/-- On a closed fiber over an algebraically closed base field, the dimension of
cohomology over the residue field equals its dimension over the base field. -/
theorem fiberCohomologyFinrank_eq_finrank_of_isClosed {y : Y} (hy : IsClosed ({y} : Set Y))
    (M : X.Modules) (q : ℕ) :
    letI : (f.fiber y).Over S := ⟨f.fiberι y ≫ X ↘ S⟩
    fiberCohomologyFinrank M f q y =
      Module.finrank k (Cohomology ((Scheme.Modules.pullback (f.fiberι y)).obj M) q) := by
  let C := f.fiber y
  let : C.Over S := ⟨f.fiberι y ≫ X ↘ S⟩
  let := f.fiberOverSpecResidueField y
  let ρ := residueFieldIsoBase (Y ↘ S) y hy
  let : Algebra k (Y.residueField y) := ρ.inv.hom.toAlgebra
  have hcomp : (C ↘ Spec (Y.residueField y)) ≫ Spec.map ρ.inv = C ↘ S := by
    rw [SpecMap_residueFieldIsoBase_inv]
    exact (f.fiber_fac_assoc y (Y ↘ S)).symm.trans
      (congrArg (fun g ↦ f.fiberι y ≫ g) (comp_over f S))
  have hr : Module.finrank k (Y.residueField y) = 1 :=
    Module.finrank_of_bijective_algebraMap ρ.commRingCatIsoToRingEquiv.symm.bijective
  let N := (Scheme.Modules.pullback (f.fiberι y)).obj M
  have h := finrank_cohomology_eq_finrank_mul (k := k) (κ := Y.residueField y) hcomp N q
  have h' : Module.finrank k (Cohomology N q) =
      Module.finrank (Y.residueField y) (Cohomology N q) := by
    simpa only [hr, one_mul] using h
  exact (fiberCohomologyFinrank_def M f q y).trans h'.symm

end AlgebraicGeometry.Scheme.Hom
