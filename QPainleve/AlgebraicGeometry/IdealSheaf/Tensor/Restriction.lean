/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.VectorBundle.ProjectionFormula
public import TauCeti.AlgebraicGeometry.IdealSheaf.TensorSequence

/-!
# Restriction of a line bundle to a closed subscheme

The quotient of a line bundle by its ideal-sheaf twist is the direct image of the
restricted line bundle. The canonical projection morphism identifies the quotient
arrow with restriction, and identifies the map of quotients with the pullback of
the original map of line bundles.
-/

public noncomputable section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal
open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

open Scheme.Modules Scheme.Hom

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData)

local notation "i" => I.subschemeι
local notation "F" => pullback i
local notation "G" => pushforward i

/-- The canonical comparison from the ideal-sheaf quotient to the direct image of the
restricted line bundle. -/
def tensorRestrictionHom (M : InvertibleSheaf X) :
    M.obj ⊗ I.pushforwardSubscheme ⟶ (G).obj ((F).obj M.obj) :=
  (i).tensorPushforwardHom M.obj (𝟙_ I.subscheme.Modules) ≫
    (G).map (ρ_ ((F).obj M.obj)).hom

/-- The canonical comparison on the ideal-sheaf quotient of a line bundle is an isomorphism. -/
theorem isIso_tensorRestrictionHom (M : InvertibleSheaf X) :
    IsIso (I.tensorRestrictionHom M) := by
  have := (i).isIso_tensorPushforwardHom M (𝟙_ I.subscheme.Modules)
  unfold tensorRestrictionHom
  infer_instance

/-- The ideal-sheaf quotient arrow followed by the comparison is the adjunction unit
for restriction to the closed subscheme. -/
@[reassoc]
theorem tensorRestrictionHom_unit (M : InvertibleSheaf X) :
    (ρ_ M.obj).inv ≫ M.obj ◁ I.toPushforwardSubscheme ≫ I.tensorRestrictionHom M =
      (pullbackPushforwardAdjunction i).unit.app M.obj := by
  have hε : I.toPushforwardSubscheme = ε G :=
    I.toPushforwardSubscheme_def.trans (pushforward_ε i).symm
  simp only [hε, tensorRestrictionHom, tensorPushforwardHom_def, Category.assoc]
  let u : M.obj ⟶ (G).obj ((F).obj M.obj) :=
    (pullbackPushforwardAdjunction i).unit.app M.obj
  have h := whisker_exchange_assoc u (ε G)
    (μ G ((F).obj M.obj) (𝟙_ I.subscheme.Modules) ≫ (G).map (ρ_ ((F).obj M.obj)).hom)
  refine (congrArg ((ρ_ M.obj).inv ≫ ·) h).trans ?_
  rw [← Functor.LaxMonoidal.right_unitality G ((F).obj M.obj),
    rightUnitor_naturality u, Iso.inv_hom_id_assoc]

/-- Under the quotient comparison, the map of quotients is the direct image of the
pullback of the original morphism. -/
@[reassoc]
theorem tensorRestrictionHom_naturality {M N : InvertibleSheaf X} (a : M.obj ⟶ N.obj) :
    a ▷ I.pushforwardSubscheme ≫ I.tensorRestrictionHom N =
      I.tensorRestrictionHom M ≫ (G).map ((F).map a) := by
  simp only [tensorRestrictionHom, Category.assoc]
  refine (tensorPushforwardHom_naturality_left_assoc i a (𝟙_ I.subscheme.Modules) _).trans ?_
  exact congrArg ((i).tensorPushforwardHom M.obj (𝟙_ I.subscheme.Modules) ≫ ·)
    ((Functor.map_comp _ _ _).symm.trans
      ((congrArg (G).map (rightUnitor_naturality ((F).map a))).trans (Functor.map_comp _ _ _)))

end AlgebraicGeometry.Scheme.IdealSheafData
