/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
public import TauCeti.AlgebraicGeometry.Blowup.UniversalProperty

import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Rational lifts to blowups

A morphism that avoids the blowup center on a dense open has a unique rational lift.
For an integral source and separated base, the domain of this lift is the locus where the
inverse image of the center is effective Cartier. A lift constructed after a dominant change
of source represents the pullback of the specified rational map. This lets one use rational
map resolution to obtain the commuting square in
[Stacks Project, Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R).

Existence and uniqueness of the lift use Tau Ceti's blowup universal property. For the converse,
the exceptional Cartier divisor pulls back along the lift because the generic point of the
source lies away from the center.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X T : Scheme.{u}} (I : X.IdealSheafData)

/-- If an integral scheme maps generically off the center and its map lifts to the blowup,
the inverse image of the center is effective Cartier. -/
theorem isEffectiveCartier_comap_of_comp_blowupToBase_eq [IsIntegral T] {f : T ⟶ X}
    (h : Dense (f ⁻¹ᵁ I.support.compl : Set T)) (g : T ⟶ I.blowup)
    (hg : g ≫ I.blowupToBase = f) : (I.comap f).IsEffectiveCartier := by
  have hη := (genericPoint_spec T).mem_open_set_iff (f ⁻¹ᵁ I.support.compl).isOpen |>.mpr
    (by obtain ⟨t, ht⟩ := h.nonempty; exact ⟨t, trivial, ht⟩)
  rw [← hg, comap_comp]
  apply I.isEffectiveCartier_comap_blowupToBase.comap_of_isIntegral g
  rw [support_comap, ← SetLike.mem_coe, TopologicalSpace.Closeds.coe_preimage,
    Set.mem_preimage, ← Scheme.Hom.comp_apply, hg]
  exact (f.mem_preimage.mp hη : f (genericPoint T) ∉ I.support)

/-- A morphism mapping a dense open off the center has a unique rational lift to the blowup. -/
theorem existsUnique_rationalMap_compHom_blowupToBase_eq (f : T ⟶ X)
    (h : Dense (f ⁻¹ᵁ I.support.compl : Set T)) :
    ∃! g : T ⤏ I.blowup, g.compHom I.blowupToBase = f.toRationalMap := by
  let U := f ⁻¹ᵁ I.support.compl
  have hc {W : T.Opens} (hW : W ≤ U) : (I.comap (W.ι ≫ f)).IsEffectiveCartier := by
    have htop : I.comap (W.ι ≫ f) = ⊤ := by
      rw [comap_eq_top_iff, Scheme.Hom.comp_preimage, eq_top_iff]
      exact fun x _ ↦ hW x.property
    rw [htop]
    exact isEffectiveCartier_top _
  let p : T.PartialMap I.blowup := ⟨U, h, I.blowupLift (U.ι ≫ f) (hc le_rfl)⟩
  have hp : p.IsOver f I.blowupToBase := ⟨I.blowupLift_blowupToBase _ _⟩
  refine ⟨p.toRationalMap, RationalMap.isOver_iff.mp inferInstance, ?_⟩
  intro g hg
  have : g.IsOver f I.blowupToBase := RationalMap.isOver_iff.mpr hg
  obtain ⟨q, hq, rfl⟩ := g.exists_partialMap_over f I.blowupToBase
  let W := q.domain ⊓ U
  refine PartialMap.toRationalMap_eq_iff.mpr
    ⟨W, q.dense_domain.inter_of_isOpen_left h q.domain.isOpen, inf_le_left, inf_le_right, ?_⟩
  have hqW : (T.homOfLE (inf_le_left : W ≤ q.domain) ≫ q.hom) ≫ I.blowupToBase = W.ι ≫ f := by
    rw [Category.assoc, hq.over, Scheme.homOfLE_ι_assoc]
  have hpW : (T.homOfLE (inf_le_right : W ≤ U) ≫ p.hom) ≫ I.blowupToBase = W.ι ≫ f := by
    have hpU : p.hom ≫ I.blowupToBase = U.ι ≫ f := hp.over
    rw [Category.assoc, hpU, Scheme.homOfLE_ι_assoc]
  exact (I.eq_blowupLift (hc inf_le_right) hqW).trans (I.eq_blowupLift (hc inf_le_right) hpW).symm

/-- The domain of the rational lift consists of the points where the inverse image of the
blowup center is effective Cartier on an open neighborhood. -/
theorem mem_domain_rationalMap_iff_isEffectiveCartier_comap [IsIntegral T] [X.IsSeparated]
    {f : T ⟶ X} (h : Dense (f ⁻¹ᵁ I.support.compl : Set T)) {g : T ⤏ I.blowup}
    (hg : g.compHom I.blowupToBase = f.toRationalMap) {x : T} :
    x ∈ g.domain ↔ ∃ U : T.Opens, x ∈ U ∧ ((I.comap f).comap U.ι).IsEffectiveCartier := by
  constructor
  · intro hx
    obtain ⟨q, hxq, hq⟩ := RationalMap.mem_domain.mp hx
    have : q.toRationalMap.IsOver f I.blowupToBase := RationalMap.isOver_iff.mpr (hq ▸ hg)
    have hqOver := (PartialMap.isOver_toRationalMap_iff_of_isSeparated).mp
      (‹q.toRationalMap.IsOver f I.blowupToBase›)
    have : Nonempty q.domain := ⟨⟨x, hxq⟩⟩
    have : IsIntegral q.domain.toScheme := isIntegral_of_isOpenImmersion q.domain.ι
    refine ⟨q.domain, hxq, ?_⟩
    rw [← comap_comp]
    apply I.isEffectiveCartier_comap_of_comp_blowupToBase_eq _ q.hom hqOver.over
    rw [Scheme.Hom.comp_preimage]
    exact h.preimage q.domain.ι.isOpenEmbedding.isOpenMap
  · rintro ⟨U, hxU, hU⟩
    rw [← comap_comp] at hU
    let q : T.PartialMap I.blowup :=
      ⟨U, U.isOpen.dense ⟨x, hxU⟩, I.blowupLift (U.ι ≫ f) hU⟩
    have : q.IsOver f I.blowupToBase := ⟨I.blowupLift_blowupToBase _ _⟩
    have hqg := (I.existsUnique_rationalMap_compHom_blowupToBase_eq f h).unique
      (RationalMap.isOver_iff.mp (inferInstance : q.toRationalMap.IsOver f I.blowupToBase)) hg
    exact RationalMap.mem_domain.mpr ⟨q, hxU, hqg⟩

/-- A morphism resolves the specified rational lift after a dominant change of source exactly
when it makes the square with the blowup projection commute. -/
theorem toRationalMap_eq_comp_iff_comp_blowupToBase_eq {S : Scheme.{u}}
    [PreirreducibleSpace S] [IsReduced S] [Nonempty T] [X.IsSeparated]
    {a : S ⟶ T} [IsDominant a]
    {f : T ⟶ X} (h : Dense (f ⁻¹ᵁ I.support.compl : Set T)) {g : T ⤏ I.blowup}
    (hg : g.compHom I.blowupToBase = f.toRationalMap) (l : S ⟶ I.blowup) :
    l.toRationalMap = a.toRationalMap.comp g ↔ l ≫ I.blowupToBase = a ≫ f := by
  have hcomp : (a.toRationalMap.comp g).compHom I.blowupToBase = (a ≫ f).toRationalMap := by
    rw [← RationalMap.comp_compHom, hg, RationalMap.comp_toRationalMap, Hom.toRationalMap_compHom]
  constructor
  · intro he
    exact Hom.toRationalMap_injective <|
      (l.toRationalMap_compHom I.blowupToBase).symm.trans
        ((congrArg (·.compHom I.blowupToBase) he).trans hcomp)
  · intro hl
    have ha : Dense ((a ≫ f) ⁻¹ᵁ I.support.compl : Set S) := by
      rw [Scheme.Hom.comp_preimage]
      apply (a ⁻¹ᵁ (f ⁻¹ᵁ I.support.compl)).isOpen.dense
      simpa [← Set.nonempty_preimage_iff] using
        a.denseRange.inter_open_nonempty _ (f ⁻¹ᵁ I.support.compl).isOpen h.nonempty
    have hlOver : l.toRationalMap.compHom I.blowupToBase = (a ≫ f).toRationalMap := by
      rw [Hom.toRationalMap_compHom, hl]
    exact (I.existsUnique_rationalMap_compHom_blowupToBase_eq (a ≫ f) ha).unique hlOver hcomp

/-- The specified rational lift has a unique global lift over the base exactly when the inverse
image of the center is effective Cartier. -/
theorem isEffectiveCartier_comap_iff_existsUnique_hom_of_rationalLift [IsIntegral T]
    {f : T ⟶ X} (h : Dense (f ⁻¹ᵁ I.support.compl : Set T)) {g : T ⤏ I.blowup}
    (hg : g.compHom I.blowupToBase = f.toRationalMap) :
    (I.comap f).IsEffectiveCartier ↔
      ∃! l : T ⟶ I.blowup, l ≫ I.blowupToBase = f ∧ l.toRationalMap = g := by
  constructor
  · intro hf
    obtain ⟨l, hl, hu⟩ := I.existsUnique_comp_blowupToBase_eq_of_isEffectiveCartier hf
    have hlOver : l.toRationalMap.compHom I.blowupToBase = f.toRationalMap := by
      rw [Hom.toRationalMap_compHom, hl]
    exact ⟨l, ⟨hl, (I.existsUnique_rationalMap_compHom_blowupToBase_eq f h).unique hlOver hg⟩,
      fun l' hl' ↦ hu l' hl'.1⟩
  · rintro ⟨l, ⟨hl, _⟩, _⟩
    exact I.isEffectiveCartier_comap_of_comp_blowupToBase_eq h l hl

end AlgebraicGeometry.Scheme.IdealSheafData
