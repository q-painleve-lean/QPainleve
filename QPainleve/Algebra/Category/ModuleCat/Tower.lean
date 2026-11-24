/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.Artinian.Defs
public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import TauCeti.Algebra.Category.ModuleCat.Kernels
import TauCeti.Algebra.Category.ModuleCat.Tower.Exact
import TauCeti.Algebra.Category.ModuleCat.Tower.MittagLeffler

/-!
# Lifting in inverse systems of Artinian modules

A levelwise surjective morphism out of a tower of Artinian modules induces a
surjection on inverse limits. The kernel tower is Artinian at each level, so
Tau Ceti's Mittag–Leffler exactness theorem applies.

## References

* The Stacks Project, [Lemma 10.86.4](https://stacks.math.columbia.edu/tag/0598).
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.ModuleTower

universe u v

/-- Levelwise surjections from a tower of Artinian modules lift compatible families. -/
theorem limMap_surjective_of_isArtinian {R : Type u} [Ring R] {F G : ModuleTower.{v} R}
    [∀ n : ℕ, IsArtinian R (F.obj (op n))] (f : F ⟶ G)
    (hf : ∀ n : ℕ, Function.Surjective (f.app (op n)).hom) :
    Function.Surjective (limMap f) := by
  let K : ModuleTower.{v} R := kernel f
  let e (n : ℕ) := (evaluation ℕᵒᵖ (ModuleCat.{v} R)).obj (op n)
  have hK (n : ℕ) : IsArtinian R (K.obj (op n)) := by
    let i := PreservesKernel.iso (e n) f ≪≫ ModuleCat.kernelIsoKer (f.app (op n))
    exact isArtinian_of_injective i.hom.hom ((ConcreteCategory.bijective_of_isIso i.hom).injective)
  let : ∀ n : ℕ, IsArtinian R (K.obj (op n)) := hK
  let : Subsingleton K.limOne :=
    K.subsingleton_limOne_of_isMittagLeffler K.isMittagLeffler_of_isArtinian
  refine limMap_surjective_of_subsingleton_limOne (f := kernel.ι f) ?_ hf
  intro n
  refine Function.Exact.of_comp_of_mem_range ?_ fun y hy ↦ ?_
  · rw [← LinearMap.coe_comp, ← ModuleCat.hom_comp, ← NatTrans.comp_app, kernel.condition,
      NatTrans.app_zero, ModuleCat.hom_zero]
    rfl
  · exact (e n).exists_map_kernel_ι_eq f y hy

end TauCeti.ModuleTower
