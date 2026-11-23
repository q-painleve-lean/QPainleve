/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Degree.Criterion
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over

import Mathlib.AlgebraicGeometry.Artinian
import QPainleve.AlgebraicGeometry.Cohomology.ClosedCover
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension

/-!
# The degree criterion on projective schemes of dimension at most one

Positive degree on integral curves characterizes ampleness on projective schemes of dimension
at most one, including reducible and nonreduced schemes. In particular, positivity on the curves
of a projective surface gives ampleness on any effective Cartier divisor in the surface.

See the [Stacks Project, Lemma 33.44.15](https://stacks.math.columbia.edu/tag/0B5Y) for the
componentwise degree criterion and [Debarre, *Introduction to Mori Theory*, Theorem 4.1]
(https://perso.imj-prg.fr/wp-content/uploads/debarre-pub/M22.pdf) for its use in Nakai–Moishezon.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.LineBundleClass

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- On a projective scheme of dimension at most one, a line bundle is ample exactly when
it has positive degree on each integral closed curve. -/
theorem isAmple_iff_intersectionNumber_pos_of_dim_le_one [X.IsProjectiveOver k]
    (a : LineBundleClass X) (hX : topologicalKrullDim X ≤ 1) :
    a.IsAmple ↔ ∀ {C : Scheme.{u}} [C.Over (Spec (.of k))] [C.IsCurveOver k]
      (i : C ⟶ X) [IsClosedImmersion i], C ↘ Spec (.of k) = i ≫ X ↘ Spec (.of k) →
        0 < intersectionNumber k i a := by
  refine ⟨fun ha _ _ _ i _ _ ↦ ha.intersectionNumber_pos i, fun ha ↦ ?_⟩
  apply (isAmple_iff_restrict_irreducibleComponents (R := k) a).mpr
  intro Z
  let J := Scheme.IdealSheafData.vanishingIdeal
    (⟨Z.val, isClosed_of_mem_irreducibleComponents _ Z.property⟩ : Closeds X)
  have hdim : topologicalKrullDim J.subscheme ≤ 1 :=
    J.subschemeι.isEmbedding.isInducing.topologicalKrullDim_le.trans hX
  have : J.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k J.subschemeι
  by_cases hZ : 1 ≤ topologicalKrullDim J.subscheme
  · have : IsIntegral J.subscheme :=
      Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal Z.property.1
    have : J.subscheme.IsCurveOver k := ⟨hdim.antisymm hZ⟩
    apply (isAmple_iff_eulerDegree_pos (k := k) (pullback J.subschemeι a)).mpr
    rw [← intersectionNumber_def]
    exact ha J.subschemeι (J.over_eq_subschemeι_comp (S := Spec (.of k)))
  · have hzero : topologicalKrullDim J.subscheme ≤ 0 := Order.le_of_lt_succ (lt_of_not_ge hZ)
    have : IsLocallyNoetherian J.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (J.subscheme ↘ Spec (.of k))
    have : IsLocallyArtinian J.subscheme := .of_topologicalKrullDim_le_zero hzero
    have : CompactSpace J.subscheme :=
      QuasiCompact.compactSpace_of_compactSpace (J.subscheme ↘ Spec (.of k))
    have : Finite J.subscheme := finite_of_compact_of_discrete
    exact isAmple_of_isAffine _

end TauCeti.AlgebraicGeometry.LineBundleClass

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

/-- A class positive on every integral closed curve of a projective scheme of dimension at
most two restricts to an ample class on every effective Cartier divisor. -/
theorem isAmple_pullback_of_intersectionNumber_pos
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
    {I : X.IdealSheafData} (hI : I.IsEffectiveCartier) (hX : topologicalKrullDim X ≤ 2)
    (a : LineBundleClass X)
    (ha : ∀ {C : Scheme.{u}} [C.Over (Spec (.of k))] [C.IsCurveOver k]
      (i : C ⟶ X) [IsClosedImmersion i], C ↘ Spec (.of k) = i ≫ X ↘ Spec (.of k) →
        0 < LineBundleClass.intersectionNumber k i a) :
    (LineBundleClass.pullback I.subschemeι a).IsAmple := by
  have : I.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  apply (LineBundleClass.isAmple_iff_intersectionNumber_pos_of_dim_le_one (k := k)
    (LineBundleClass.pullback I.subschemeι a) (hI.topologicalKrullDim_subscheme_le (d := 1) hX)).mpr
  intro C _ _ i _ hi
  rw [LineBundleClass.intersectionNumber_pullback]
  exact ha (i ≫ I.subschemeι) (by
    simpa only [Category.assoc, ← I.over_eq_subschemeι_comp] using hi)

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
