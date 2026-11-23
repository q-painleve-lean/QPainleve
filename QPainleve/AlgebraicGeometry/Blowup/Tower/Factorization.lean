/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Resolution
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic

import QPainleve.AlgebraicGeometry.Blowup.Modification
import QPainleve.AlgebraicGeometry.Blowup.Point.Contraction
import QPainleve.AlgebraicGeometry.Blowup.Point.Factorization
import QPainleve.AlgebraicGeometry.Blowup.Projective.Global
import QPainleve.AlgebraicGeometry.Blowup.Tower.Lift
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Factorization and common resolutions of projective surfaces

A proper birational morphism of smooth integral projective surfaces factors into
closed point blowups. Resolving a prescribed birational map and factoring the resulting
morphism then gives a common resolution by point blowups on both sides.

The argument follows the Stacks Project, [Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R)
and [Lemma 54.17.2](https://stacks.math.columbia.edu/tag/0C5S).
-/

public section

open CategoryTheory TopologicalSpace
open QPainleve QPainleve.BlowupTower
open TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

open Scheme.IdealSheafData

local notation "I[" X ", " p "]" =>
  vanishingIdeal (Closeds.mk (closure (Set.singleton (p : X))) isClosed_closure)

attribute [local instance] specializationOrder

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
variable [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
variable [X.IsProjectiveOver k] [Y.IsProjectiveOver k] [IsIntegral X] [IsIntegral Y]
variable [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
variable [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]

/-- A modification of smooth integral projective surfaces factors through the blowup of
any closed point of its centre. The lift composes with the blowup projection to the
specified modification and is itself a modification. -/
theorem exists_comp_pointBlowup_eq_of_mem_centre (f : X ⟶ Y) [IsModification f]
    [f.IsOver (Spec (.of k))] {q : Y} (hq : IsClosed ({q} : Set Y)) (hqf : q ∈ f.centre) :
    ∃ g : X ⟶ (I[Y, q]).blowup, IsModification g ∧ g ≫ (I[Y, q]).blowupToBase = f := by
  let sX := X ↘ Spec (.of k)
  let sY := Y ↘ Spec (.of k)
  let J := I[Y, q]
  let b := J.blowupToBase
  rcases f.exists_lift_pointBlowup_or_nonconstant_exceptional (k := k) hq with
    ⟨g, hg⟩ | ⟨n, W, T, p, g, hp, hT, _, hg, hpq, hnc⟩
  · have hs : (J.support : Set Y) = {q} := (coe_support_vanishingIdeal _).trans hq.closure_eq
    have hqIso : q ∉ (f.isoLocus : Set Y) := by
      simpa only [centre_def, Set.mem_compl_iff] using hqf
    have hdense : Dense (J.support.compl : Set Y) := by
      rw [Closeds.coe_compl, hs]
      exact (IsModification.dense_isoLocus f).mono (Set.subset_compl_singleton_iff.mpr hqIso)
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    have : IsModification b := J.isModification_blowupToBase hdense
    have : IsModification (g ≫ b) := hg.symm ▸ ‹IsModification f›
    exact ⟨g, IsModification.of_comp_right g b, hg⟩
  · -- The target point stays in the centre after precomposing with the source tower.
    let sW := T.toBase ≫ sX
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    have : Nontrivial X := by
      rw [← not_subsingleton_iff_nontrivial, ← topologicalKrullDim_eq_zero_iff_subsingleton,
        topologicalKrullDim_eq_of_smoothOfRelativeDimension sX (n := 2)]
      norm_num
    have : IsModification T.toBase := hT.isModification
    have : IsModification (T.toBase ≫ f) := inferInstance
    have hcentre : q ∈ (T.toBase ≫ f).centre := by
      rw [centre_comp]
      exact Or.inl hqf
    have : SmoothOfRelativeDimension 2 sW := hT.smoothOfRelativeDimension sX
    have : Smooth sW := SmoothOfRelativeDimension.smooth 2 sW
    have : Smooth sY := SmoothOfRelativeDimension.smooth 2 sY
    have : IsRegular W := IsRegular.of_smooth sW
    have : IsRegular Y := IsRegular.of_smooth sY
    have hdp := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq sW 2).mp inferInstance).2 p hp
    have hdq := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq sY 2).mp inferInstance).2 q hq
    exact (hnc ((T.toBase ≫ f).range_exceptional_subsingleton_of_mem_centre
      hp hq hdp hdq g hg hpq hcentre)).elim

private theorem exists_isClosedPointTower_factorization_of_ncard_le
    (bound : ℕ) (f : X ⟶ Y) [IsModification f] [f.IsOver (Spec (.of k))]
    (hf : {x : X | f x ∈ f.centre ∧ Order.coheight x = 1}.ncard ≤ bound) :
    ∃ (n : ℕ) (Z : Scheme.{u}) (T : BlowupTower Y n Z) (e : X ≅ Z),
      IsClosedPointTower Y T ∧ e.hom ≫ T.toBase = f := by
  induction bound using Nat.strong_induction_on generalizing Y with
  | ind bound ih =>
    let sY := Y ↘ Spec (.of k)
    have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
    have : IsNoetherian Y := isNoetherian_of_finiteType sY
    have : Smooth sY := SmoothOfRelativeDimension.smooth 2 sY
    have : IsRegular Y := IsRegular.of_smooth sY
    have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension sY (n := 2)
    by_cases hc : f.centre = ∅
    · have : IsIso f := f.centre_eq_empty_iff.mp hc
      exact ⟨0, Y, .nil, asIso f, .nil, by simp⟩
    obtain ⟨q, hqf⟩ := Set.ne_empty_iff_nonempty.mp hc
    have hq : IsClosed ({q} : Set Y) := mem_closedPoints_iff.mp
      (f.centre_subset_closedPoints hdim.le hqf)
    obtain ⟨g, hgMod, hg⟩ := f.exists_comp_pointBlowup_eq_of_mem_centre (k := k) hq hqf
    let J := I[Y, q]
    let V := J.blowup
    let b := J.blowupToBase
    let first : BlowupTower Y 1 V := BlowupTower.nil.snoc J
    have hfirst : IsClosedPointTower Y first :=
      IsClosedPointTower.nil.snoc q hq (Scheme.ker_fromSpecResidueField_eq_vanishingIdeal q).symm
    let : V.Over (Spec (.of k)) := ⟨b ≫ sY⟩
    have hsV : (V ↘ Spec (.of k)) = b ≫ sY := rfl
    have : V.IsProjectiveOver k := J.isProjectiveOver_blowup_of_isNoetherianRing k
    have : SmoothOfRelativeDimension 2 (V ↘ Spec (.of k)) := by
      simpa only [hsV, first, toBase_snoc, toBase_nil, Category.comp_id] using
        hfirst.smoothOfRelativeDimension sY
    have : Smooth (V ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
    have : IsRegular V := IsRegular.of_smooth (V ↘ Spec (.of k))
    have : IsIntegral V := hfirst.isIntegral sY
    have : IsModification (g ≫ b) := hg.symm ▸ ‹IsModification f›
    have : g.IsOver (Spec (.of k)) := ⟨by
      rw [hsV, ← Category.assoc, hg, comp_over]⟩
    -- The exceptional-divisor estimate uses the ideal of the closed singleton.
    have hclosed :
        (⟨closure (Set.singleton q), isClosed_closure⟩ : Closeds Y) = ⟨Set.singleton q, hq⟩ :=
      SetLike.coe_injective hq.closure_eq
    have hlt := ncard_exceptional_divisors_lt_comp_pointBlowup (X := X) (p := q) hq sY
    rw [← hclosed] at hlt
    have hdecrease := hlt g fun z hz ↦ g.mem_isoLocus_of_coheight_eq_one hz
    rw [hg] at hdecrease
    obtain ⟨n, Z, T, e, hT, he⟩ :=
      ih _ (hdecrease.trans_le hf) g le_rfl
    refine ⟨1 + n, Z, first.append T, e, hfirst.append hT, ?_⟩
    simpa only [toBase_append, first, toBase_snoc, toBase_nil, Category.comp_id,
      ← Category.assoc, he] using hg

/-- A proper birational morphism of smooth integral projective surfaces over an algebraically
closed field is a composition of closed point blowups, up to a source isomorphism over the
target. -/
theorem exists_isClosedPointTower_factorization (f : X ⟶ Y)
    [f.IsOver (Spec (.of k))] (hf : Scheme.BirationalOver f (𝟙 Y)) :
    ∃ (n : ℕ) (Z : Scheme.{u}) (T : BlowupTower Y n Z) (e : X ≅ Z),
      IsClosedPointTower Y T ∧ e.hom ≫ T.toBase = f := by
  obtain ⟨a, ha⟩ := hf
  have hcomp : a.iso.hom ≫ a.target.ι = a.source.ι ≫ f := by
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using ha
  have : IsDominant a.source.ι := Opens.isDominant_ι a.dense_source
  have : IsDominant a.target.ι := Opens.isDominant_ι a.dense_target
  have : IsDominant (a.source.ι ≫ f) := hcomp ▸
    inferInstanceAs (IsDominant (a.iso.hom ≫ a.target.ι))
  have : IsOpenImmersion (a.source.ι ≫ f) := hcomp ▸
    inferInstanceAs (IsOpenImmersion (a.iso.hom ≫ a.target.ι))
  have : IsProper (f ≫ (Y ↘ Spec (.of k))) := by
    rw [comp_over f (Spec (.of k))]
    infer_instance
  have : IsProper f := IsProper.of_comp f (Y ↘ Spec (.of k))
  have : IsModification f := IsModification.of_isOpenImmersion_comp f a.source.ι
  exact exists_isClosedPointTower_factorization_of_ncard_le (k := k) _ f le_rfl

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.PartialIso

/-- A specified birational map between smooth integral projective surfaces over an
algebraically closed field admits a common resolution by closed point blowup towers.
The isomorphism of the final schemes commutes with the structure maps and its composite
with the target projection represents the given rational map on the source tower. -/
theorem exists_common_pointBlowup_resolution
    {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X.IsProjectiveOver k] [Y.IsProjectiveOver k] [IsIntegral X] [IsIntegral Y]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
    (a : X.PartialIso Y) (ha : a.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))) :
    ∃ (m n : ℕ) (V W : Scheme.{u}) (T : BlowupTower X m V) (U : BlowupTower Y n W)
      (e : V ≅ W) (_ : IsIntegral V) (_ : IsDominant T.toBase),
      IsClosedPointTower X T ∧ IsClosedPointTower Y U ∧
      e.hom ≫ U.toBase ≫ (Y ↘ Spec (.of k)) = T.toBase ≫ (X ↘ Spec (.of k)) ∧
      (e.hom ≫ U.toBase).toRationalMap = T.toBase.toRationalMap.comp a.toRationalMap := by
  let sX := X ↘ Spec (.of k)
  let sY := Y ↘ Spec (.of k)
  have : a.toPartialMap.IsOver sX sY :=
    ⟨(Category.assoc a.iso.hom a.target.ι sY).trans ha⟩
  have : a.toRationalMap.IsOver sX sY := inferInstance
  obtain ⟨m, V, T, _, _, hT, g, ⟨hg, hga⟩, _⟩ :=
    a.toRationalMap.exists_isClosedPointTower_resolving (k := k)
  have : Nontrivial X := by
    rw [← not_subsingleton_iff_nontrivial, ← topologicalKrullDim_eq_zero_iff_subsingleton,
      topologicalKrullDim_eq_of_smoothOfRelativeDimension sX (n := 2)]
    norm_num
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsModification g := hT.isModification_of_resolved_partialIso sX sY a g hg hga.symm
  let : V.Over (Spec (.of k)) := ⟨T.toBase ≫ sX⟩
  have : SmoothOfRelativeDimension 2 (V ↘ Spec (.of k)) := hT.smoothOfRelativeDimension sX
  have : V.IsProjectiveOver k := T.isProjectiveOver k
  have : g.IsOver (Spec (.of k)) := ⟨hg⟩
  obtain ⟨n, W, U, e, hU, he⟩ :=
    g.exists_isClosedPointTower_factorization (k := k) (IsModification.birationalOver g)
  exact ⟨m, n, V, W, T, U, e, inferInstance, inferInstance, hT, hU,
    by rw [← Category.assoc, he, hg], by rw [he, hga]⟩

end AlgebraicGeometry.Scheme.PartialIso
