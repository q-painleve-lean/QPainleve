/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.DirectSum

import QPainleve.CategoryTheory.GradedObject.Total

/-!
# Detecting graded algebra isomorphisms on direct sums

An isomorphism of direct-sum algebras induced by a graded map detects an
isomorphism in each homogeneous degree and hence an isomorphism of graded
algebras.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.AlgebraicGeometry

universe u

namespace GradedQuasicoherentAlgebra

variable {X : Scheme.{u}}

/-- A map of graded quasicoherent algebras is invertible if the underlying map of
direct-sum algebras is invertible. -/
instance : (toQuasicoherentAlgebra (X := X)).ReflectsIsomorphisms where
  reflects {A B} g hg := by
    let U := (isGradedQuasicoherentAlgebra X).ι ⋙
      CommMon.forget₂Mon (GradedObject ℕ X.Modules) ⋙ Mon.forget (GradedObject ℕ X.Modules)
    let g₀ : (toQuasicoherentAlgebra.obj A).obj.X ⟶ (toQuasicoherentAlgebra.obj B).obj.X :=
      (toQuasicoherentAlgebra.map g).hom.hom.hom
    have hg₀ : IsIso g₀ :=
      inferInstanceAs (IsIso ((toQuasicoherentAlgebra.map g).hom.hom.hom))
    let l := eqToHom (toQuasicoherentAlgebra_obj_obj_X A)
    let r := eqToHom (toQuasicoherentAlgebra_obj_obj_X B)
    let t : (GradedObject.total ℕ X.Modules).obj A.obj.X ⟶
        (GradedObject.total ℕ X.Modules).obj B.obj.X :=
      (GradedObject.total ℕ X.Modules).map (U.map g)
    have hmap : l ≫ t = g₀ ≫ r := by
      apply toQuasicoherentAlgebra_hom_ext
      intro n
      let gₙ : A.obj.X n ⟶ B.obj.X n := g.hom.hom.hom n
      calc
        ιTotal A n ≫ l ≫ t = GradedObject.ιTotal A.obj.X n ≫ t := by
          simp only [ιTotal_def, l, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
            Category.id_comp]
        _ = gₙ ≫ GradedObject.ιTotal B.obj.X n :=
          GradedObject.ιTotal_total_map (U.map g) n
        _ = (gₙ ≫ ιTotal B n) ≫ r := by
          simp only [ιTotal_def, r, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
        _ = (ιTotal A n ≫ g₀) ≫ r :=
          congrArg (fun k : A.obj.X n ⟶ (toQuasicoherentAlgebra.obj B).obj.X ↦ k ≫ r)
            (ιTotal_toQuasicoherentAlgebra_map g n).symm
        _ = ιTotal A n ≫ g₀ ≫ r := Category.assoc _ _ _
    have hlt : IsIso (l ≫ t) := by
      rw [hmap]
      have : IsIso r := inferInstanceAs (IsIso (eqToHom _))
      exact IsIso.comp_isIso
    have hl : IsIso l := inferInstanceAs (IsIso (eqToHom _))
    have : IsIso ((GradedObject.total ℕ X.Modules).map (U.map g)) := IsIso.of_isIso_comp_left l t
    have : IsIso (U.map g) := isIso_of_reflects_iso (U.map g) (GradedObject.total ℕ X.Modules)
    have : U.ReflectsIsomorphisms := inferInstanceAs (Functor.ReflectsIsomorphisms
      ((isGradedQuasicoherentAlgebra X).ι ⋙
        CommMon.forget₂Mon (GradedObject ℕ X.Modules) ⋙ Mon.forget (GradedObject ℕ X.Modules)))
    exact isIso_of_reflects_iso g U

end GradedQuasicoherentAlgebra

end TauCeti.AlgebraicGeometry
