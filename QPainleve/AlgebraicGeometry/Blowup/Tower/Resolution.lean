/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.Resolution

import QPainleve.AlgebraicGeometry.Blowup.Tower.BaseIdeal
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Resolving rational maps by closed point blowups

A rational map from a smooth integral projective surface over an algebraically
closed field to a projective scheme becomes a morphism after a finite tower of
closed point blowups. Principalizing the base ideal of a projective section
presentation gives a morphism that represents the pullback of the specified map.
This is the source-side construction for a common resolution of a birational map,
as in [Stacks Project, Lemma 54.17.2](https://stacks.math.columbia.edu/tag/0C5S).
-/

public section

open CategoryTheory
open QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.RationalMap

universe u

/-- A rational map over an algebraically closed field from a smooth integral projective
surface to a projective scheme extends uniquely over the base on some tower of closed
point blowups. The equality of rational maps uses the projection of that tower. -/
theorem exists_isClosedPointTower_resolving {k : Type u} [Field k] [IsAlgClosed k]
    {X Z : Scheme.{u}} [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [X.IsProjectiveOver k] [Z.IsProjectiveOver k] [IsIntegral X]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    (q : X ⤏ Z) [q.IsOver (X ↘ Spec (.of k)) (Z ↘ Spec (.of k))] :
    ∃ (n : ℕ) (Y : Scheme.{u}) (T : BlowupTower X n Y)
      (_ : IsIntegral Y) (_ : IsDominant T.toBase),
      IsClosedPointTower X T ∧
        ∃! g : Y ⟶ Z, g ≫ (Z ↘ Spec (.of k)) = T.toBase ≫ (X ↘ Spec (.of k)) ∧
          g.toRationalMap = T.toBase.toRationalMap.comp q := by
  let f := X ↘ Spec (.of k)
  have : IsNoetherian X := isNoetherian_of_finiteType f
  obtain ⟨A, hA⟩ := X.exists_isAmple_of_isProjectiveOver k
  obtain ⟨ι, _, L, s, hs, hres⟩ := q.exists_section_family_for_resolution f hA
  obtain ⟨n, Y, T, hT, hI⟩ :=
    L.exists_isClosedPointTower_isEffectiveCartier_comap_iSup_zeroIdeal k s hs
  have : IsIntegral Y := hT.isIntegral f
  have : Surjective T.toBase := hT.surjective f
  exact ⟨n, Y, T, inferInstance, inferInstance, hT, (hres T.toBase).mp hI⟩

end AlgebraicGeometry.Scheme.RationalMap
