/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import TauCeti.AlgebraicGeometry.LineBundle.Dual

import TauCeti.AlgebraicGeometry.Modules.Sections

/-!
# Lifting morphisms from line bundles

In a short exact sequence of sheaves, a map from a line bundle to the quotient lifts
to the middle sheaf if first cohomology of the kernel tensored with the dual line bundle
vanishes.
-/

public section

open CategoryTheory MonoidalCategory TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Vanishing of the first cohomology of the kernel twisted by the dual of a line
bundle ensures that every map from that line bundle to the quotient lifts. -/
theorem surjective_postcomp_of_subsingleton_cohomology_tensor_dual
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (L : InvertibleSheaf X)
    (h : Subsingleton (Cohomology (S.X₁ ⊗ L.dual.obj) 1)) :
    Function.Surjective (fun f : L.obj ⟶ S.X₂ ↦ f ≫ S.g) := by
  let F := tensorRight L.dual.obj
  have : F.IsEquivalence := by
    dsimp only [F]
    rw [← L.tensorRightDualEquivalence_functor]
    infer_instance
  let e := L.evaluationDualIso
  have hF : F.PreservesZeroMorphisms := ⟨fun _ _ ↦ by
    let : MonoidalPreadditive X.Modules := TauCeti.SheafOfModules.monoidalPreadditive X.sheaf
    simp [F]⟩
  have hS' := hS.map_of_exact F
  intro g
  obtain ⟨v, hv⟩ := sections_surjective hS' h
    ((F.obj S.X₃).unitHomEquivTop (e.inv ≫ F.map g))
  let t := (F.obj S.X₂).unitHomEquivTop.symm v
  have ht : t ≫ F.map S.g = e.inv ≫ F.map g := by
    apply (F.obj S.X₃).unitHomEquivTop.injective
    rw [unitHomEquivTop_comp, Equiv.apply_symm_apply]
    exact hv
  refine ⟨F.preimage (e.hom ≫ t), F.map_injective ?_⟩
  rw [Functor.map_comp, Functor.map_preimage]
  exact (Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·) ht).trans (e.hom_inv_id_assoc _))

end AlgebraicGeometry.Scheme.Modules
