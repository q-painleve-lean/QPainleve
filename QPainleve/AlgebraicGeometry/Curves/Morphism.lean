/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint.Basic

/-!
# Morphisms of proper integral curves

A dominant morphism of proper integral curves over a field is finite.
Its generic fiber consists of the generic point and every closed fiber is a
finite closed subset of the source.

See [Stacks Project, Lemma 33.44.4](https://stacks.math.columbia.edu/tag/0AYU).
-/

public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {C D : Scheme.{u}}
  [C.Over (Spec (.of k))] [D.Over (Spec (.of k))]
  [C.IsCurveOver k] [D.IsCurveOver k]

/-- A dominant morphism of proper integral curves over a field is finite. -/
theorem isFinite_of_isDominant_of_isCurveOver (g : C ⟶ D)
    [g.IsOver (Spec (.of k))] [IsDominant g] : IsFinite g := by
  have : IsProper (g ≫ D ↘ Spec (.of k)) := by
    rw [comp_over]
    infer_instance
  have : IsProper g := .of_comp g (D ↘ Spec (.of k))
  have : IsNoetherian C := Scheme.IsCurveOver.isNoetherian k C
  have hC := (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := C) k).le
  have hD := (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := D) k).le
  have : LocallyQuasiFinite g := LocallyQuasiFinite.of_finite_preimage_singleton g fun y ↦ by
    by_cases hy : y = genericPoint D
    · subst y
      refine (Set.finite_singleton (genericPoint C)).subset fun x hx ↦ ?_
      by_contra h
      have hxclosed : IsClosed ({x} : Set C) :=
        TauCeti.AlgebraicGeometry.Scheme.isClosed_singleton_of_ne_genericPoint
          hC h
      have hyclosed := g.isClosedMap {x} hxclosed
      rw [Set.image_singleton] at hyclosed
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
      have hall (y : D) : y = genericPoint D :=
        (genericPoint_specializes y).mem_closed (hx ▸ hyclosed) rfl
      have : Subsingleton D := ⟨fun a b ↦ (hall a).trans (hall b).symm⟩
      have := TauCeti.topologicalKrullDim_eq_zero_iff_subsingleton.mpr ‹Subsingleton D›
      rw [Scheme.IsCurveOver.topologicalKrullDim_eq_one k] at this
      contradiction
    · have hyclosed : IsClosed ({y} : Set D) :=
        TauCeti.AlgebraicGeometry.Scheme.isClosed_singleton_of_ne_genericPoint
          hD hy
      exact TauCeti.AlgebraicGeometry.Scheme.finite_of_isClosed_of_genericPoint_notMem
        hC (hyclosed.preimage g.continuous)
        (fun hx ↦ hy ((Set.mem_singleton_iff.mp hx).symm.trans
          g.genericPoint_eq_of_isDominant))
  exact .of_isProper_of_locallyQuasiFinite g

end AlgebraicGeometry.Scheme.Hom
