/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.Artinian.Defs
public import TauCeti.Algebra.Category.ModuleCat.Tower.Exact

import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.RingTheory.Artinian.Module
import TauCeti.Algebra.Category.ModuleCat.Tower.MittagLeffler

/-!
# Surjective maps from towers of Artinian modules

A levelwise surjection from a tower of Artinian modules induces a surjection
on inverse limits, since the tower of kernels is Mittag–Leffler.

## References

* The Stacks Project, [Lemma 10.86.4](https://stacks.math.columbia.edu/tag/0598).
-/

public section

open CategoryTheory Opposite
open CategoryTheory.Limits

namespace TauCeti.ModuleTower

/-- A levelwise surjection from a tower with Artinian terms is surjective on inverse limits. -/
theorem limMap_surjective_of_isArtinian {R : Type*} [Ring R] {F G : ModuleTower R}
    [∀ n : ℕ, IsArtinian R (F.obj (op n))] (f : F ⟶ G)
    (hf : ∀ n : ℕ, Function.Surjective (f.app (op n)).hom) :
    Function.Surjective (limMap f) := by
  have hExact (n : ℕ) :
      Function.Exact ((kernel.ι f).app (op n)).hom (f.app (op n)).hom := by
    let ev := (evaluation ℕᵒᵖ (ModuleCat R)).obj (op n)
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      ((ShortComplex.exact_kernel f).map_of_mono_of_preservesKernel ev
        inferInstance inferInstance)
  have hArt (n : ℕ) : IsArtinian R ((kernel f).obj (op n)) := by
    have hmono := (NatTrans.mono_iff_mono_app (f := kernel.ι f)).mp inferInstance (op n)
    exact isArtinian_of_injective _ ((ModuleCat.mono_iff_injective _).mp hmono)
  have : Subsingleton (limOne (kernel f)) :=
    (kernel f).subsingleton_limOne_of_isMittagLeffler ((kernel f).isMittagLeffler_of_isArtinian)
  exact limMap_surjective_of_subsingleton_limOne hExact hf

end TauCeti.ModuleTower
