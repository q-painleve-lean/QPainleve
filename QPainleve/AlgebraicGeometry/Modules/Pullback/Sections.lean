/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.AlgebraicGeometry.Modules.Sections

/-!
# Pullback of sections

The equivalence between global sections of a sheaf of modules and morphisms from
the structure sheaf commutes with pullback. The counit recovers a section over
an inverse image open from its pullback as a section of the pushforward.
-/

public section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Hom

open Scheme.Modules in
/-- Evaluation on the pullback of a section of the pushforward recovers the original section. -/
@[simp]
theorem counit_app_pullbackSections {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules)
    (U : Y.Opens) (s : Γ(M, f ⁻¹ᵁ U)) :
    dsimp% only [Functor.comp_obj, Functor.id_obj, pushforward_obj_obj]
      (((pullbackPushforwardAdjunction f).counit.app M).app (f ⁻¹ᵁ U)
        (f.pullbackSections ((pushforward f).obj M) U s)) = s := by
  let adj := pullbackPushforwardAdjunction f
  have h : adj.homEquiv _ _ (adj.counit.app M) = 𝟙 ((pushforward f).obj M) := by
    rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components]
  have h' := pullbackPushforwardAdjunction_homEquiv_app_apply f (adj.counit.app M) U s
  exact h'.symm.trans ((congrArg (fun p : (pushforward f).obj M ⟶ (pushforward f).obj M ↦
    p.app U s) h).trans (by rfl))

/-- Pulling a global section back to the top open agrees with its canonical pullback. -/
theorem pullbackSectionsLE_top {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} (s : Γ(M, ⊤)) :
    f.pullbackSectionsLE M ⊤ ⊤ f.preimage_top.ge s = f.pullbackSections M ⊤ s := by
  let N := (Modules.pullback f).obj M
  let a : Γ(N, ⊤) := f.pullbackSections M ⊤ s
  refine (f.pullbackSectionsLE_apply M ⊤ ⊤ f.preimage_top.ge s).trans ?_
  exact (congrArg (fun h : Γ(N, ⊤) ⟶ Γ(N, ⊤) ↦ h a)
    (N.presheaf.map_id (Opposite.op ⊤))).trans (id_apply a)

/-- Pulling back the morphism of a global section gives the morphism of its pullback. -/
theorem unitHomEquivTop_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} (s : 𝟙_ Y.Modules ⟶ M) :
    ((Modules.pullback f).obj M).unitHomEquivTop
        ((Modules.pullbackObjUnitIso f).inv ≫ (Modules.pullback f).map s) =
      f.pullbackSections M ⊤ (M.unitHomEquivTop s) := by
  have h := (congrArg (((Modules.pullback f).map s).app (f ⁻¹ᵁ ⊤) ·)
    (f.pullbackObjUnitIso_inv_app_one)).trans
    (f.pullbackSections_naturality _ ⊤ s (1 : Γ(Y, ⊤)))
  exact (Modules.unitHomEquivTop_apply _ _).trans
    (h.trans (congrArg (f.pullbackSections M ⊤) (Modules.unitHomEquivTop_apply M s).symm))

/-- The morphism of the pulled-back section is the pullback of the morphism of the section. -/
theorem unitHomEquivTop_symm_pullbackSections {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} (s : Γ(M, ⊤)) :
    (((Modules.pullback f).obj M).unitHomEquivTop).symm (f.pullbackSections M ⊤ s) =
      (Modules.pullbackObjUnitIso f).inv ≫
        (Modules.pullback f).map (M.unitHomEquivTop.symm s) := by
  let t : 𝟙_ Y.Modules ⟶ M := M.unitHomEquivTop.symm s
  exact ((Modules.pullback f).obj M).unitHomEquivTop.symm_apply_eq.mpr
    ((f.unitHomEquivTop_pullback t).trans
      (congrArg (f.pullbackSections M ⊤) (M.unitHomEquivTop.apply_symm_apply s))).symm

end AlgebraicGeometry.Scheme.Hom
