/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Degree.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Ample

import QPainleve.AlgebraicGeometry.LineBundle.Ample
import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.Degree
import TauCeti.AlgebraicGeometry.Curves.Normalization

/-!
# Positive degree of ample classes on proper integral curves

An ample class has a positive power cut out by a nonempty effective Cartier divisor.
Its degree is the rank of the finite divisor, and degree is additive under tensor
product. This is the forward implication of
[Stacks Project, Lemma 33.44.14](https://stacks.math.columbia.edu/tag/0B5X).
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple

variable {X : Scheme.{u}} {k : Type u} [Field k]
  [X.Over (Spec (.of k))] [X.IsCurveOver k] {a : LineBundleClass X}

/-- An ample line-bundle class on a proper integral curve has strictly positive Euler degree.
The curve may be singular. -/
theorem eulerDegree_pos (ha : a.IsAmple) : 0 < a.eulerDegree k := by
  let f := X ↘ Spec (.of k)
  have hdim := Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k
  obtain ⟨n, hn, I, hI, hne, hclass⟩ :=
    ha.exists_effectiveCartier_pow_ne_top f (hdim.symm ▸ zero_lt_one)
  have : RelativeDimensionLE 1 f := (relativeDimensionLE_iff_of_field f).mpr hdim.le
  have : IsFinite (I.subschemeι ≫ f) := hI.isFinite_subschemeι_comp
  have hdegree := hI.eulerDegree_inv_mk_toInvertibleSheaf k I default
  rw [hclass] at hdegree
  have hnonempty : Nonempty I.subscheme := by
    by_contra! hempty
    exact hne (I.ker_subschemeι ▸ (Scheme.Hom.ker_eq_top_iff_isEmpty I.subschemeι).mpr hempty)
  have hpos : 0 < (I.subschemeι ≫ f).finrank default := by
    obtain ⟨x⟩ := hnonempty
    exact Nat.pos_of_ne_zero fun hz ↦
      ((Scheme.Hom.finrank_eq_zero_iff_notMem_range _ _).mp hz)
        ⟨x, Subsingleton.elim _ _⟩
  rw [← zpow_natCast, eulerDegree_zpow_of_isCurveOver] at hdegree
  exact pos_of_mul_pos_right (hdegree.symm ▸ Int.natCast_pos.mpr hpos) (Int.natCast_nonneg n)

end TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple
