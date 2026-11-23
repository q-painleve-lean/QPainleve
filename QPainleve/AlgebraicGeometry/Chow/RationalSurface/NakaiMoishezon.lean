/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Effectivity
public import TauCeti.AlgebraicGeometry.LineBundle.Ample

import QPainleve.AlgebraicGeometry.Chow.Ample
import QPainleve.AlgebraicGeometry.Curves.Degree.Components
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.GlobalGeneration
import QPainleve.AlgebraicGeometry.IntersectionNumber.Ample

/-!
# Nakai–Moishezon for smooth projective rational surfaces

Positive self-intersection and positive degree on every integral closed curve characterize
ample line bundles. A positive power of the class gives an effective Cartier divisor.
The restriction to this divisor is ample by the degree criterion in dimension at most one.
Global generation of a further power gives a finite morphism to projective space.

See [Debarre, *Introduction to Mori Theory*, Theorem 4.1]
(https://perso.imj-prg.fr/wp-content/uploads/debarre-pub/M22.pdf).
-/

public section

open AlgebraicGeometry CategoryTheory Filter
open TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.LineBundleClass

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [rational : Scheme.IsRationalOver (X ↘ Spec (.of k))]

/-- The Nakai–Moishezon criterion for a smooth projective rational surface over an
algebraically closed field. Curve degrees are tested on all integral closed curves,
including singular curves. -/
theorem isAmple_iff_self_pos_and_intersectionNumber_pos (a : LineBundleClass X) :
    a.IsAmple ↔ 0 < Chow.classIntersectionNumber k X a a ∧
      ∀ {C : Scheme.{u}} [C.Over (Spec (.of k))] [C.IsCurveOver k]
        (i : C ⟶ X) [IsClosedImmersion i], C ↘ Spec (.of k) = i ≫ X ↘ Spec (.of k) →
          0 < intersectionNumber k i a := by
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := rational.isIntegral_of_smooth
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)
  constructor
  · intro ha
    have (x : X) : UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two x
    refine ⟨Chow.classIntersectionNumber_pos_of_isAmple k hX ha ha, ?_⟩
    intro C _ _ i _ _
    exact ha.intersectionNumber_pos i
  · rintro ⟨hself, hpos⟩
    have hnef : IsNef k (X ↘ Spec (.of k)) a :=
      (isNef_iff k (X ↘ Spec (.of k)) a).mpr fun _ _ _ i _ hi ↦ (hpos i hi).le
    obtain ⟨m, hm, I, hI, _, hclass⟩ :=
      exists_effectiveCartier_pow_of_isNef_of_self_pos k a hnef hself
    have hdual : mk hI.toInvertibleSheaf.dual = a ^ m := by
      rwa [← inv_mk]
    have hpower {C : Scheme.{u}} [C.Over (Spec (.of k))] [C.IsCurveOver k]
        (i : C ⟶ X) [IsClosedImmersion i] (hi : C ↘ Spec (.of k) = i ≫ X ↘ Spec (.of k)) :
        0 < intersectionNumber k i (mk hI.toInvertibleSheaf.dual) := by
      have hC := Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := C) k
      have : RelativeDimensionLE 1 (C ↘ Spec (.of k)) :=
        (relativeDimensionLE_iff_of_field _).mpr hC.le
      rw [hdual, intersectionNumber_pow_of_isIntegral]
      exact mul_pos (Int.natCast_pos.mpr hm) (hpos i hi)
    have hrestriction := hI.isAmple_pullback_of_intersectionNumber_pos hX.le _ hpower
    obtain ⟨n, hgen, hn⟩ := ((hI.eventually_isGloballyGenerated_of_isAmple k hrestriction).and
      (eventually_gt_atTop (0 : ℕ))).exists
    have hAmple :=
      InvertibleSheaf.isAmple_of_isGloballyGenerated_tensorPow_of_intersectionNumber_pos
        hn hgen hpower
    rw [hdual] at hAmple
    exact hAmple.of_pow hm

end TauCeti.AlgebraicGeometry.LineBundleClass
