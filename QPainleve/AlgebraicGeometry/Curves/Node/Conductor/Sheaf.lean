/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor

import QPainleve.AlgebraicGeometry.IdealSheaf.Conductor.Pullback
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# The conductor square of a nodal curve on structure sheaves

Functions on a nodal curve are functions on the blowup separating the branches
whose restrictions to the branch scheme come from the singular subscheme. The
comparison uses the actual closed subschemes in the conductor square and works
on all opens, including at self-nodes and nonsplit nodes.

See the Stacks Project, Proposition 37.67.3, Tag 0E25, for the structure sheaf
formula for a pushout along a closed immersion.
-/

public section

open CategoryTheory Limits TopCat.Presheaf
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The structure presheaf of a nodal curve is the pullback of the pushforwards
of the structure presheaves of the blowup and the singular subscheme over the
pushforward from the branch scheme. -/
theorem isPullback_nodal_conductor_presheaf
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) :
    letI := hnodal.syntomic
    let I := X.singularLocus k
    let ν := I.blowupToBase
    let i := I.subschemeι
    let j := X.branchSchemeToBlowup k
    let g := X.branchSchemeToSingularLocus k
    IsPullback ν.c i.c ((pushforward _ ν.base).map j.c)
      (((pushforward _ i.base).map g.c) ≫
        (pushforwardEq
          (congrArg (fun m : X.branchScheme k ⟶ X ↦ m.base)
            (X.branchSchemeToSingularLocus_subschemeι k))
          (X.branchScheme k).presheaf).hom) := by
  let := hnodal.syntomic
  let I := X.singularLocus k
  let ν := I.blowupToBase
  have : IsFinite ν := X.isFinite_blowupToBase_singularLocus hnodal
  have : Surjective ν := X.surjective_blowupToBase_singularLocus hnodal
  have : IsReduced X := hnodal.isReduced
  have : IsSchemeTheoreticallyDominant ν := .of_isDominant ν
  exact (X.isPullback_branchScheme k).flip.isPullback_presheaf_of_ker_eq_conductor
    ((IdealSheafData.ker_subschemeι I).trans
      (conductor_blowupToBase_singularLocus hnodal).symm)

end AlgebraicGeometry.Scheme
