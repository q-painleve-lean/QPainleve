/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor
public import QPainleve.AlgebraicGeometry.IdealSheaf.Conductor.Modules

import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Descent of bundle maps on nodal curves

A bundle morphism on a nodal curve is determined by its restrictions to the blowup
separating the branches and the singular subscheme. Every pair of morphisms agreeing
on the branch scheme comes from a morphism on the curve. In particular, this applies
to maps between line bundles on a nodal cycle, including at a self-node.
-/

public section

open CategoryTheory
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

open Modules

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- Compatible maps of finite locally free sheaves on the blowup and the singular
subscheme descend uniquely to the nodal curve. -/
theorem existsUnique_hom_of_nodal_conductor
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)))
    (E F : FiniteLocallyFreeSheaf X) :
    letI := hnodal.syntomic
    let I := X.singularLocus k
    let ν := I.blowupToBase
    let i := I.subschemeι
    let j := X.branchSchemeToBlowup k
    let g := X.branchSchemeToSingularLocus k
    let e := pullbackComp g i ≪≫ pullbackCongr (X.branchSchemeToSingularLocus_subschemeι k)
    ∀ (a : (pullback ν).obj E.obj ⟶ (pullback ν).obj F.obj)
      (b : (pullback i).obj E.obj ⟶ (pullback i).obj F.obj),
      (pullbackComp j ν).inv.app E.obj ≫ (pullback j).map a ≫
        (pullbackComp j ν).hom.app F.obj =
          e.inv.app E.obj ≫ (pullback g).map b ≫ e.hom.app F.obj →
      ∃! c : E.obj ⟶ F.obj, (pullback ν).map c = a ∧ (pullback i).map c = b := by
  let := hnodal.syntomic
  let I := X.singularLocus k
  let ν := I.blowupToBase
  have : IsFinite ν := X.isFinite_blowupToBase_singularLocus hnodal
  have : Surjective ν := X.surjective_blowupToBase_singularLocus hnodal
  have : IsReduced X := hnodal.isReduced
  have : IsSchemeTheoreticallyDominant ν := .of_isDominant ν
  dsimp only
  intro a b hab
  exact (X.isPullback_branchScheme k).flip.existsUnique_hom_of_ker_eq_conductor
    ((IdealSheafData.ker_subschemeι I).trans
      (conductor_blowupToBase_singularLocus hnodal).symm) E F a b hab

end AlgebraicGeometry.Scheme
