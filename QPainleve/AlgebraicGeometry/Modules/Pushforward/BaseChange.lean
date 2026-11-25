/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pushforward.BaseChange

import QPainleve.AlgebraicGeometry.Modules.Pullback.Sections

/-!
# Base change of direct image to an open subscheme

Restricting a direct image to a base open agrees with pushing forward the restriction
to its inverse image. The comparison is the canonical base change morphism.
-/

public section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The direct-image base change map along an open inclusion is an isomorphism for
every sheaf of modules. -/
theorem isIso_pushforwardBaseChange_morphismRestrict (U : Y.Opens) (M : X.Modules) :
    IsIso ((pushforwardBaseChange (isPullback_morphismRestrict f U).flip.toCommSq).app M) := by
  let w := (isPullback_morphismRestrict f U).flip.toCommSq
  apply Hom.isIso_iff_isIso_app.mpr
  intro V
  let W := U.ι ''ᵁ V
  have hW : U.ι ⁻¹ᵁ W = V := U.ι.preimage_image_eq V
  have hw : W ≤ U.ι.opensRange := U.ι.image_le_opensRange _
  rw [← hW, ConcreteCategory.isIso_iff_bijective]
  have ha := U.ι.bijective_pullbackSections_of_isOpenImmersion ((pushforward f).obj M) W hw
  have hb := (f ⁻¹ᵁ U).ι.bijective_pullbackSections_of_isOpenImmersion M (f ⁻¹ᵁ W) (by
    simpa only [Scheme.Opens.opensRange_ι] using f.preimage_mono hw)
  have he : (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ W) = (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← w.w, Scheme.Hom.comp_preimage]
  let c := ((pullback (f ⁻¹ᵁ U).ι).obj M).presheaf.map (eqToHom he).op
  have hc := ConcreteCategory.bijective_of_isIso c
  apply (Function.Bijective.of_comp_iff _ ha).mp
  have heq : (fun s ↦ ((pushforwardBaseChange w).app M).app (U.ι ⁻¹ᵁ W)
      (U.ι.pullbackSections ((pushforward f).obj M) W s)) =
      c ∘ (f ⁻¹ᵁ U).ι.pullbackSections M (f ⁻¹ᵁ W) :=
    funext (pushforwardBaseChange_app_app_pullbackSections w M W)
  have hcomp := heq.symm ▸ hc.comp hb
  exact hcomp

end AlgebraicGeometry.Scheme.Modules
