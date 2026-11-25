/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

import TauCeti.AlgebraicGeometry.Modules.Pushforward.Basic

/-!
# Restriction of a direct image to a section

The canonical comparison from the direct image along a scheme morphism to the
pullback along its section respects transposition by the pullback–pushforward
adjunction and compositions through intermediate schemes.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X Y : Scheme.{u}}

noncomputable section

/-- If a section is an isomorphism, restricting a direct image along that section
recovers the pullback along the inverse. -/
theorem isIso_pushforwardToPullback_app_of_isIso {s : X ⟶ Y} [IsIso s]
    {p : Y ⟶ X} (hs : s ≫ p = 𝟙 X) (M : Y.Modules) :
    IsIso ((pushforwardToPullback hs).app M) := by
  have hp : p ≫ s = 𝟙 Y := IsIso.eq_inv_of_hom_inv_id hs ▸ IsIso.inv_hom_id s
  let e : Y.Modules ≌ X.Modules := CategoryTheory.Equivalence.mk (pullback s) (pullback p)
    ((pullbackId Y).symm ≪≫ pullbackCongr hp.symm ≪≫ (pullbackComp p s).symm)
    (pullbackComp s p ≪≫ pullbackCongr hs ≪≫ pullbackId X)
  let : (pullback s).IsEquivalence := e.isEquivalence_functor
  rw [pushforwardToPullback_app]
  infer_instance

/-- Composing restriction to a section with a map out of the pullback amounts to
pushing forward the adjoint transpose of that map. -/
@[reassoc]
theorem pushforwardToPullback_app_comp {p : Y ⟶ X} {s : X ⟶ Y} (hs : s ≫ p = 𝟙 X)
    {M : Y.Modules} {N : X.Modules} (f : (pullback s).obj M ⟶ N) :
    (pushforwardToPullback hs).app M ≫ f =
      (pushforward p).map ((pullbackPushforwardAdjunction s).homEquiv _ _ f) ≫
        (pushforwardComp s p).hom.app N ≫ (pushforwardCongr hs).hom.app N ≫
          (pushforwardId X).hom.app N := by
  have h := (pushforwardId X).hom.naturality f
  simp only [Functor.id_map] at h
  rw [pushforwardToPullback_app, Category.assoc, Category.assoc, Category.assoc, ← h,
    ← (pushforwardCongr hs).hom.naturality_assoc, ← (pushforwardComp s p).hom.naturality_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc, Adjunction.homEquiv_unit]

/-- Restriction to a composite section commutes with transposition along its second
morphism and restriction along its first morphism. -/
@[reassoc]
theorem pushforwardToPullback_app_comp_pullbackComp_inv_app
    {Z : Scheme.{u}} {p : Y ⟶ X} {q : Z ⟶ X} (i : X ⟶ Z) (g : Z ⟶ Y)
    (hg : g ≫ p = q) (hi : i ≫ q = 𝟙 X) (hs : (i ≫ g) ≫ p = 𝟙 X)
    {M : Y.Modules} {N : Z.Modules} (τ : (pullback g).obj M ⟶ N) :
    (pushforwardToPullback hs).app M ≫ (pullbackComp i g).inv.app M ≫
        (pullback i).map τ =
      (pushforward p).map ((pullbackPushforwardAdjunction g).homEquiv _ _ τ) ≫
        (pushforwardComp g p).hom.app N ≫ (pushforwardCongr hg).hom.app N ≫
          (pushforwardToPullback hi).app N := by
  rw [pushforwardToPullback_app_comp, TauCeti.AlgebraicGeometry.homEquiv_pullbackComp,
    Adjunction.comp_homEquiv, Equiv.trans_apply]
  -- Transposing the pullback of `τ` inserts the unit of the adjunction for `i`.
  have h := (pullbackPushforwardAdjunction i).homEquiv_naturality_left τ
    (𝟙 ((pullback i).obj N))
  rw [Category.comp_id, Adjunction.homEquiv_id] at h
  rw [h, Adjunction.homEquiv_naturality_right, pushforwardToPullback_app hi]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  let N' := (pullback i).obj N
  let η := (pullbackPushforwardAdjunction i).unit.app N
  let π := (pushforward g).map η ≫ (pushforwardComp i g).hom.app N'
  have hCongr : (pushforwardCongr (rfl : i ≫ g = i ≫ g)).hom.app N' = 𝟙 _ := by
    apply hom_ext
    intro U
    simp only [pushforwardCongr_hom_app_app, Hom.id_app, pushforward_obj_obj]
    exact N'.presheaf.map_id _
  have hcomp := TauCeti.AlgebraicGeometry.pushforward_compatible
    (i ≫ g) g p i (𝟙 X) q rfl hs hg ((pushforward g).obj N) N' N π (𝟙 _) η
    (fun U x ↦ by
      have hx : (Hom.app (𝟙 ((pushforward g).obj N)) U) x = x := ModuleCat.id_apply _ _
      rw [hx]
      have hπ := TauCeti.AlgebraicGeometry.pushforward_composite_app i g (i ≫ g) rfl
        N' N η U x
      rw [hCongr, Category.comp_id] at hπ
      exact hπ.symm)
  simpa [Category.assoc, π, η, N'] using congrArg (· ≫ (pushforwardId X).hom.app N') hcomp.symm

/-- Restricting the adjoint transpose of a morphism from a pullback to a section
recovers that morphism pulled back along the section. -/
@[reassoc]
theorem homEquiv_comp_pushforwardToPullback_app {p : Y ⟶ X} {s : X ⟶ Y}
    (hs : s ≫ p = 𝟙 X) {M : X.Modules} {N : Y.Modules} (f : (pullback p).obj M ⟶ N) :
    (pullbackPushforwardAdjunction p).homEquiv _ _ f ≫ (pushforwardToPullback hs).app N =
      (pullbackId X).inv.app M ≫ (pullbackCongr hs.symm).hom.app M ≫
        (pullbackComp s p).inv.app M ≫ (pullback s).map f := by
  rw [Adjunction.homEquiv_unit, Category.assoc, (pushforwardToPullback hs).naturality,
    unit_comp_pushforwardToPullback_app_assoc]

end

end AlgebraicGeometry.Scheme.Modules
