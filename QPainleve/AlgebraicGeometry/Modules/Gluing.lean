/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Gluing

/-!
# The pullback adjunction for glued modules

Under the canonical comparison of restriction and pullback along a chart inclusion,
the restriction map of a glued module is adjoint to the gluing projection.
-/

public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.ModulesGlueData

/-- Under the pullback–pushforward adjunction, the restriction map of a glued module,
transported along the canonical pullback-to-restriction isomorphism, is adjoint to the
gluing projection. -/
theorem homEquiv_restrictGluedHom {J : Type u} [SmallCategory J]
    {F : J ⥤ Scheme.{u}} (D : ModulesGlueData F)
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]
    [(F ⋙ Scheme.forget).IsLocallyDirected] [Quiver.IsThin J] (i : J) :
    let j := Limits.colimit.ι F i
    (pullbackPushforwardAdjunction j).homEquiv _ _
      ((restrictFunctorIsoPullback j).inv.app D.glued ≫ D.restrictGluedHom i) = D.π i := by
  intro j
  let a := pullbackPushforwardAdjunction j
  let r := restrictAdjunction j
  have he : D.restrictGluedHom i = (r.homEquiv _ _).symm (D.π i) := by
    rw [Adjunction.homEquiv_counit]
    exact Scheme.Modules.hom_ext _ _ fun W ↦
      ConcreteCategory.hom_ext _ _ (D.restrictGluedHom_app_apply i W)
  calc
    _ = a.homEquiv _ _ ((restrictFunctorIsoPullback j).inv.app D.glued) ≫
        (pushforward j).map (D.restrictGluedHom i) := a.homEquiv_naturality_right _ _
    _ = r.homEquiv _ _ (D.restrictGluedHom i) := by
      rw [restrictFunctorIsoPullback, Adjunction.leftAdjointUniq_inv_app,
        a.homEquiv_leftAdjointUniq_hom_app]
      exact (r.homEquiv_unit _ _ _).symm
    _ = D.π i := by rw [he, Equiv.apply_symm_apply]

end TauCeti.ModulesGlueData
