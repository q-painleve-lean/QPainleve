/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Lift
import QPainleve.AlgebraicGeometry.Blowup.Modification
import QPainleve.AlgebraicGeometry.Blowup.Projective.Global
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Blowup.Tower.Resolution
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Centre
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition
import TauCeti.AlgebraicGeometry.Morphisms.Separated
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.Topology.KrullDimension.Irreducible

/-!
# Resolving lifts to blowups of projective schemes

A morphism from a smooth projective surface that generically avoids a blowup center
lifts to the blowup after a tower of closed point blowups of the source. For a
modification and a closed point center, a shortest such tower is either empty or
ends at a point over the target center whose exceptional fiber is not contracted
by the lift.

This reduction uses the descent along the terminal point blowup in the proof of
[Stacks Project, Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R).
-/

public section

open CategoryTheory TopologicalSpace
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
variable [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
variable [X.IsProjectiveOver k] [Y.IsProjectiveOver k] [IsIntegral X]
variable [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

open IdealSheafData

/-- A morphism of projective schemes from a smooth integral surface that avoids a
center on a dense open lifts to the blowup after a tower of closed point blowups. -/
theorem exists_isClosedPointTower_lifting_blowup (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (I : Y.IdealSheafData) (h : Dense (f ⁻¹ᵁ I.support.compl : Set X)) :
    ∃ (n : ℕ) (Z : Scheme.{u}) (T : BlowupTower X n Z) (g : Z ⟶ I.blowup),
      IsClosedPointTower X T ∧ g ≫ I.blowupToBase = T.toBase ≫ f := by
  let s := X ↘ Spec (.of k)
  let : I.blowup.Over (Spec (.of k)) := ⟨I.blowupToBase ≫ (Y ↘ Spec (.of k))⟩
  let : I.blowup.IsProjectiveOver k := I.isProjectiveOver_blowup_of_isNoetherianRing k
  obtain ⟨r, hr, _⟩ := I.existsUnique_rationalMap_compHom_blowupToBase_eq f h
  have : r.IsOver f I.blowupToBase := RationalMap.isOver_iff.mpr hr
  have : r.IsOver s (I.blowup ↘ Spec (.of k)) := by
    obtain ⟨a, ha, har⟩ := r.exists_partialMap_over f I.blowupToBase
    refine ⟨a, ⟨?_⟩, har⟩
    -- The chosen structure map is the blowup projection followed by the structure map of Y.
    change a.hom ≫ I.blowupToBase ≫ (Y ↘ Spec (.of k)) = a.domain.ι ≫ s
    rw [← Category.assoc, a.over f I.blowupToBase, Category.assoc,
      HomIsOver.comp_over (f := f) (S := Spec (.of k))]
  obtain ⟨n, Z, T, _, _, hT, _, g, ⟨_, hg⟩, _⟩ := r.exists_isClosedPointTower_resolving (k := k)
  have : Y.IsSeparated := Scheme.IsSeparated.of_isSeparated (Y ↘ Spec (.of k))
  exact ⟨n, Z, T, g, hT, (I.toRationalMap_eq_comp_iff_comp_blowupToBase_eq h hr g).mp hg⟩

variable {W : Scheme.{u}} {p : W} {q : Y}

local notation "𝔪[" x "]" =>
  vanishingIdeal (Closeds.mk (closure (Set.singleton x)) isClosed_closure)

private theorem subsingleton_range_exceptional_of_ne (hp : IsClosed ({p} : Set W))
    (hq : IsClosed ({q} : Set Y)) (f : W ⟶ Y) (g : 𝔪[p].blowup ⟶ 𝔪[q].blowup)
    (hg : g ≫ 𝔪[q].blowupToBase = 𝔪[p].blowupToBase ≫ f) (hne : f p ≠ q) :
    Set.Subsingleton (Set.range ((𝔪[p].comap 𝔪[p].blowupToBase).subschemeι ≫ g)) := by
  let e := (𝔪[p].comap 𝔪[p].blowupToBase).subschemeι
  have himage (x : (𝔪[p].comap 𝔪[p].blowupToBase).subscheme) :
      𝔪[q].blowupToBase (g (e x)) = f p := by
    have hx : e x ∈ 𝔪[p].blowupToBase ⁻¹' {p} :=
      range_subschemeι_comap_pointBlowup hp ▸ Set.mem_range_self x
    have hx' : 𝔪[p].blowupToBase (e x) = p := hx
    simpa only [Scheme.Hom.comp_apply, hx'] using congrArg (fun a : 𝔪[p].blowup ⟶ Y ↦ a (e x)) hg
  have hmem (x : (𝔪[p].comap 𝔪[p].blowupToBase).subscheme) :
      g (e x) ∈ 𝔪[q].blowupToBase ⁻¹' (𝔪[q].support : Set Y)ᶜ := by
    have hs : (𝔪[q].support : Set Y) = {q} := (coe_support_vanishingIdeal _).trans hq.closure_eq
    rw [Set.mem_preimage, himage, hs, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact hne
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  simp only [Scheme.Hom.comp_apply]
  exact 𝔪[q].injOn_blowupToBase_compl_support (hmem x) (hmem y) ((himage x).trans (himage y).symm)

private theorem exists_descended_lift
    {K : Type u} [Field K] (s : W ⟶ Spec (.of K)) [SmoothOfRelativeDimension 2 s]
    (f : W ⟶ Y) (hp : IsClosed ({p} : Set W)) (g : 𝔪[p].blowup ⟶ 𝔪[q].blowup)
    (hg : g ≫ 𝔪[q].blowupToBase = 𝔪[p].blowupToBase ≫ f)
    (h : Set.Subsingleton (Set.range ((𝔪[p].comap 𝔪[p].blowupToBase).subschemeι ≫ g))) :
    ∃ g' : W ⟶ 𝔪[q].blowup, g' ≫ 𝔪[q].blowupToBase = f := by
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 s
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsRegularLocalRing (W.presheaf.stalk p) := isRegularLocalRing_stalk_of_smooth s p
  have hd := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq s 2).mp inferInstance).2 p hp
  let : W.Over Y := ⟨f⟩
  let : (𝔪[q].blowup).Over Y := ⟨𝔪[q].blowupToBase⟩
  obtain ⟨g', ⟨_, hg'⟩, _⟩ := existsUnique_comp_eq_pointBlowup_over hp hd g hg h
  exact ⟨g', hg'.comp_over⟩

/-- For a modification from a smooth integral projective surface, either it lifts to
the blowup of the specified closed point or a resolving tower has a lift that maps
its last exceptional fiber nonconstantly. In the latter case the last center lies
over the specified point, and the lift itself is a modification. -/
theorem exists_lift_pointBlowup_or_nonconstant_exceptional
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsModification f] (hq : IsClosed ({q} : Set Y)) :
    (∃ g : X ⟶ 𝔪[q].blowup, g ≫ 𝔪[q].blowupToBase = f) ∨
      ∃ (n : ℕ) (W : Scheme.{u}) (T : BlowupTower X n W) (p : W)
        (g : 𝔪[p].blowup ⟶ 𝔪[q].blowup),
        IsClosed ({p} : Set W) ∧ IsClosedPointTower X T ∧ IsModification g ∧
          g ≫ 𝔪[q].blowupToBase = 𝔪[p].blowupToBase ≫ T.toBase ≫ f ∧ f (T.toBase p) = q ∧
          ¬ Set.Subsingleton (Set.range ((𝔪[p].comap 𝔪[p].blowupToBase).subschemeι ≫ g)) := by
  have : Nontrivial X := by
    rw [← not_subsingleton_iff_nontrivial, ← TauCeti.topologicalKrullDim_eq_zero_iff_subsingleton,
      topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)]
    norm_num
  have : IrreducibleSpace Y := f.surjective.irreducibleSpace f.continuous
  have : Nontrivial Y := not_subsingleton_iff_nontrivial.mp fun h ↦ by
    have hU : f.isoLocus = ⊤ := by
      obtain ⟨y, hy⟩ := (IsModification.dense_isoLocus f).nonempty
      exact top_unique fun z _ ↦ (h.elim y z) ▸ hy
    have := f.isoLocus_eq_top_iff.mp hU
    exact not_nontrivial_iff_subsingleton.mpr f.isOpenEmbedding.injective.subsingleton ‹_›
  have hs : (𝔪[q].support : Set Y) = {q} := (coe_support_vanishingIdeal _).trans hq.closure_eq
  have hI : Dense (𝔪[q].support.compl : Set Y) := 𝔪[q].support.compl.isOpen.dense (by
    rw [Closeds.coe_compl, hs]
    exact exists_ne q)
  have h := f.exists_isClosedPointTower_lifting_blowup (k := k) 𝔪[q]
    ((inferInstance : IsModification f).dense_preimage hI)
  classical
  obtain ⟨Z, T, g, hT, hg⟩ := Nat.find_spec h
  have hmin {m : ℕ} (hm : m < Nat.find h) :
      ¬ ∃ (Z : Scheme.{u}) (T : BlowupTower X m Z) (g : Z ⟶ 𝔪[q].blowup),
        IsClosedPointTower X T ∧ g ≫ 𝔪[q].blowupToBase = T.toBase ≫ f :=
    Nat.find_min h hm
  -- Abstract the minimum length so that the tower can be split into its two constructors.
  generalize Nat.find h = m at T hT hg hmin
  cases T with
  | nil =>
    exact Or.inl ⟨g, by simpa only [toBase_nil, Category.id_comp] using hg⟩
  | @snoc n W T K =>
    obtain ⟨hprefix, p, hp, hK⟩ := IsClosedPointTower.snoc_iff.mp hT
    rw [Scheme.ker_fromSpecResidueField_eq_vanishingIdeal] at hK
    subst K
    rw [toBase_snoc, Category.assoc] at hg
    have hnonconstant :
        ¬ Set.Subsingleton (Set.range ((𝔪[p].comap 𝔪[p].blowupToBase).subschemeι ≫ g)) := by
      intro hc
      let s := T.toBase ≫ (X ↘ Spec (.of k))
      have : SmoothOfRelativeDimension 2 s := hprefix.smoothOfRelativeDimension (X ↘ Spec (.of k))
      obtain ⟨g', hg'⟩ := exists_descended_lift s (T.toBase ≫ f) hp g hg hc
      exact hmin (Nat.lt_succ_self n) ⟨W, T, g', hprefix, hg'⟩
    have hcenter : f (T.toBase p) = q := not_not.mp fun hne ↦
      hnonconstant (subsingleton_range_exceptional_of_ne hp hq (T.toBase ≫ f) g hg hne)
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
    have : IsModification 𝔪[q].blowupToBase := 𝔪[q].isModification_blowupToBase hI
    have : IsModification (T.snoc 𝔪[p]).toBase := hT.isModification
    have : IsModification (g ≫ 𝔪[q].blowupToBase) := by
      rw [hg, ← Category.assoc, ← toBase_snoc]
      infer_instance
    exact Or.inr ⟨n, W, T, p, g, hp, hprefix, IsModification.of_comp_right g 𝔪[q].blowupToBase,
      hg, hcenter, hnonconstant⟩

end AlgebraicGeometry.Scheme.Hom
