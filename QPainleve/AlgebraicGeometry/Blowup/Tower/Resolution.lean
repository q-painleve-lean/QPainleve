/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
public import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.Resolution

import QPainleve.AlgebraicGeometry.Blowup.Tower.BaseIdeal
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.RationalMap.Restriction
import TauCeti.AlgebraicGeometry.Birational.RationalMap.ValuationRing
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Resolving rational maps by closed point blowups

A rational map from a smooth integral projective surface over an algebraically
closed field to a projective scheme becomes a morphism after a finite tower of
closed point blowups. Principalizing the base ideal of a projective section
presentation gives a morphism that represents the pullback of the specified map.
The tower is an isomorphism exactly over the original domain of definition.
This is the source-side construction for a common resolution of a birational map,
as in [Stacks Project, Lemma 54.4.3](https://stacks.math.columbia.edu/tag/0C5H)
and [Lemma 54.17.2](https://stacks.math.columbia.edu/tag/0C5S).
-/

public section

open CategoryTheory TopologicalSpace
open QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.RationalMap

universe u

/-- A rational map over an algebraically closed field from a smooth integral projective
surface to a projective scheme extends uniquely over the base on some tower of closed
point blowups. The isomorphism locus of the tower projection is exactly the domain of
definition of the specified rational map. -/
theorem exists_isClosedPointTower_resolving {k : Type u} [Field k] [IsAlgClosed k]
    {X Z : Scheme.{u}} [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [X.IsProjectiveOver k] [Z.IsProjectiveOver k] [IsIntegral X]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    (q : X ⤏ Z) [q.IsOver (X ↘ Spec (.of k)) (Z ↘ Spec (.of k))] :
    ∃ (n : ℕ) (Y : Scheme.{u}) (T : BlowupTower X n Y)
      (_ : IsIntegral Y) (_ : IsDominant T.toBase),
      IsClosedPointTower X T ∧ T.toBase.isoLocus = q.domain ∧
        ∃! g : Y ⟶ Z, g ≫ (Z ↘ Spec (.of k)) = T.toBase ≫ (X ↘ Spec (.of k)) ∧
          g.toRationalMap = T.toBase.toRationalMap.comp q := by
  let f := X ↘ Spec (.of k)
  have : IsNoetherian X := isNoetherian_of_finiteType f
  obtain ⟨A, hA⟩ := X.exists_isAmple_of_isProjectiveOver k
  obtain ⟨ι, _, L, s, hs, hres⟩ := q.exists_section_family_for_resolution f hA
  obtain ⟨n, Y, T, hT, hI, hrestrict⟩ :=
    L.exists_isClosedPointTower_principalizing_iSup_zeroIdeal k s hs
  have : IsIntegral Y := hT.isIntegral f
  have : Surjective T.toBase := hT.surjective f
  have : Z.IsSeparated := Scheme.IsSeparated.of_isSeparated (Z ↘ Spec (.of k))
  let p := q.toPartialMap
  have : Nonempty p.domain := Set.nonempty_coe_sort.mpr p.dense_domain.nonempty
  have : IsDominant p.domain.ι := Opens.isDominant_ι p.dense_domain
  have hp : p.hom.toRationalMap = p.domain.ι.toRationalMap.comp q := by
    simpa only [p, toRationalMap_toPartialMap] using p.hom_toRationalMap_eq_comp
  -- On the original domain the partial representative is already a resolving morphism.
  have hcart := (hres p.domain.ι).mpr
    ⟨p.hom, ⟨p.over f (Z ↘ Spec (.of k)), hp⟩,
      fun g hg ↦ Scheme.Hom.toRationalMap_injective (hg.2.trans hp.symm)⟩
  have hle : q.domain ≤ T.toBase.isoLocus := q.toPartialMap_domain ▸
    T.toBase.le_isoLocus_iff.mpr ((hrestrict p.domain).mpr hcart)
  have hresolve := (hres T.toBase).mp hI
  obtain ⟨g, hg⟩ := hresolve.exists
  have hback := q.le_domain_of_isIso_morphismRestrict T.toBase g hg.2 T.toBase.isoLocus
  exact ⟨n, Y, T, inferInstance, inferInstance, hT, le_antisymm hback hle, hresolve⟩

end AlgebraicGeometry.Scheme.RationalMap
