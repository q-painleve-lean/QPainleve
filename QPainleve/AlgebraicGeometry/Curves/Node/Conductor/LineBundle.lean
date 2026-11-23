/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor
public import QPainleve.AlgebraicGeometry.IdealSheaf.Conductor.LineBundle

import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Gluing line bundles on a nodal curve

A unit on the branch scheme prescribes the identification between the trivial
line on the normalization and the trivial line on the singular subscheme.
The resulting line bundle is trivial on the normalization, so over a cycle
of projective lines it has multidegree zero. The branch scheme retains both
branches at a self-node.
-/

public section

open CategoryTheory MonoidalCategory
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

open Modules

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- A unit on the branch scheme glues the trivial lines on the blowup separating the
branches and on the singular subscheme. The two induced trivializations differ on
the branch scheme by multiplication by the given unit. -/
theorem exists_glued_line_of_nodal_conductor
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) :
    letI := hnodal.syntomic
    let I := X.singularLocus k
    let ν := I.blowupToBase
    let i := I.subschemeι
    let j := X.branchSchemeToBlowup k
    let g := X.branchSchemeToSingularLocus k
    ∀ a : Γ(X.branchScheme k, ⊤)ˣ,
      ∃ (L : InvertibleSheaf X)
        (e : (pullback ν).obj L.obj ≅ 𝟙_ _)
        (d : (pullback i).obj L.obj ≅ 𝟙_ _),
        (pullbackComp j ν).inv.app L.obj ≫ (pullback j).map e.hom ≫
          (pullbackObjUnitIso j).hom =
        (pullbackCongr (X.branchSchemeToSingularLocus_subschemeι k)).inv.app L.obj ≫
          (pullbackComp g i).inv.app L.obj ≫ (pullback g).map d.hom ≫
          (pullbackObjUnitIso g).hom ≫ globalSectionsSmul (𝟙_ _) (a : Γ(X.branchScheme k, ⊤)) := by
  let := hnodal.syntomic
  let I := X.singularLocus k
  let ν := I.blowupToBase
  have : IsFinite ν := X.isFinite_blowupToBase_singularLocus hnodal
  have : Surjective ν := X.surjective_blowupToBase_singularLocus hnodal
  have : IsReduced X := hnodal.isReduced
  have : IsSchemeTheoreticallyDominant ν := .of_isDominant ν
  dsimp only
  intro a
  exact (X.isPullback_branchScheme k).flip.exists_glued_line_of_conductor_square a
    ((IdealSheafData.ker_subschemeι I).trans
      (conductor_blowupToBase_singularLocus hnodal).symm)

end AlgebraicGeometry.Scheme
