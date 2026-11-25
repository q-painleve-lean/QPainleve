/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.BaseChange

/-!
# Naturality of graded sections under pullback

The graded ring maps on sections induced by a sheaf morphism commute with
pullback to a smaller open in the inverse image. This gives naturality of the
base change of relative projective spectra on affine charts.
-/

public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CommMon

universe u

namespace TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra

/-- A morphism of graded quasicoherent algebras commutes with pulling back graded
sections to an open in the inverse image. -/
theorem pullbackGradedSectionsGradedHom_naturality {X Y : Scheme.{u}}
    (f : X ⟶ Y) {A B : GradedQuasicoherentAlgebra Y} (g : A ⟶ B)
    {U : Y.Opens} {V : X.Opens} (h : V ≤ f ⁻¹ᵁ U) :
    (gradedSectionsGradedHom ((pullback f).map g).hom V).comp
        (pullbackGradedSectionsGradedHom f A h) =
      (pullbackGradedSectionsGradedHom f B h).comp (gradedSectionsGradedHom g.hom U) := by
  have he (n : ℕ) :
      eqToHom (pullback_obj_obj_X f A n).symm ≫ (((pullback f).map g).hom).hom.hom n =
        (Scheme.Modules.pullback f).map (g.hom.hom.hom n) ≫
          eqToHom (pullback_obj_obj_X f B n).symm := by
    rw [pullback_map_hom_hom_hom]
    dsimp only [CommMon.toMon]
    simp
  have hcomp :
      (gradedSectionsMap ((pullback f).map g).hom V).toRingHom.comp
          (pullbackGradedSections f A h) =
        (pullbackGradedSections f B h).comp (gradedSectionsMap g.hom U).toRingHom := by
    apply DirectSum.ringHom_ext
    intro n x
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      pullbackGradedSections_of, gradedSectionsMap_of]
    erw [pullbackGradedSections_of]
    apply congrArg (DirectSum.of _ n)
    erw [← Scheme.Hom.pullbackSectionsLE_naturality f (A.obj.X n) U V h (g.hom.hom.hom n) x]
    let s := f.pullbackSectionsLE (A.obj.X n) U V h x
    have hn := congrArg
      (fun (a : (Scheme.Modules.pullback f).obj (A.obj.X n) ⟶ ((pullback f).obj B).obj.X n) ↦
        a.app V s) (he n)
    erw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app] at hn
    dsimp only [CommMon.toMon] at hn ⊢
    exact hn
  apply GradedRingHom.ext
  intro x
  simpa only [GradedRingHom.comp_apply, gradedSectionsGradedHom_apply,
    pullbackGradedSectionsGradedHom_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe] using DFunLike.congr_fun hcomp x

end TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra
