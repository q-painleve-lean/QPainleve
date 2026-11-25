/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Degree

/-!
# Degrees of line bundles on closed fibers

Over an algebraically closed field, a closed fiber has the same Euler degree
whether its base is taken to be the residue field or the original field.
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] [IsAlgClosed k] {X S : Scheme.{u}}
  [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
  (g : X ⟶ S) [g.IsOver (Spec (.of k))] [LocallyOfFiniteType (S ↘ Spec (.of k))]

local notation "K" => Spec (CommRingCat.of k)

/-- On a closed fiber over an algebraically closed field, the Euler degree
over the residue field equals the Euler degree over the ground field. -/
theorem eulerDegree_fiber_eq_of_isClosed {s : S} (hs : IsClosed ({s} : Set S))
    (L : LineBundleClass (g.fiber s)) :
    let : (g.fiber s).Over K := ⟨g.fiberι s ≫ X ↘ K⟩
    let := g.fiberOverSpecResidueField s
    LineBundleClass.eulerDegree (S.residueField s) L = LineBundleClass.eulerDegree k L := by
  let C := g.fiber s
  let : C.Over K := ⟨g.fiberι s ≫ X ↘ K⟩
  let := g.fiberOverSpecResidueField s
  let e := residueFieldIsoBase (S ↘ K) s hs
  let : Algebra k (S.residueField s) := e.inv.hom.toAlgebra
  have he : (C ↘ Spec (S.residueField s)) ≫ Spec.map e.inv = C ↘ K := by
    rw [SpecMap_residueFieldIsoBase_inv]
    exact (g.fiber_fac_assoc s (S ↘ K)).symm.trans
      (congrArg (g.fiberι s ≫ ·) (comp_over g K))
  have hr : Module.finrank k (S.residueField s) = 1 :=
    Module.finrank_of_bijective_algebraMap e.commRingCatIsoToRingEquiv.symm.bijective
  -- Fix the two structure maps before rewriting the degree over the ground field.
  change LineBundleClass.eulerDegree (S.residueField s) L = LineBundleClass.eulerDegree k L
  rw [LineBundleClass.eulerDegree_eq_finrank_mul (k := k) (κ := S.residueField s) he L,
    hr, Nat.cast_one, one_mul]

end AlgebraicGeometry.Scheme.Hom
