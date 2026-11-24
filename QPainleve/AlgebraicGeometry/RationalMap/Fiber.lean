/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.Composition.Defined
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsSepClosed

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Restriction
import TauCeti.AlgebraicGeometry.Morphisms.Separated
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RationalPoint

/-!
# Comparing morphisms on rational fibers

Two morphisms from a smooth scheme over a separably closed field to a separated
scheme agree if their restrictions to each rational fiber agree as rational maps.
Reducedness extends the equality over each fiber, and the density of rational
sections extends it over the whole source. A dominant evaluation then detects
equality of rational maps from their generically defined composites on the fibers.
The proof uses Tau Ceti's
`Scheme.Hom.denseRange_rationalSections` and
`AlgebraicGeometry.ext_of_dense_iUnion_range_of_isSeparated`.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {k : Type u} [Field k] [IsSepClosed k] {X C Y : Scheme.{u}}

local notation "S" => Spec (CommRingCat.of k)

/-- Morphisms over a separably closed field, with smooth source and separated target,
are determined by their rational maps on the fibers over rational points of any
parameter scheme when those fibers are reduced. -/
theorem eq_iff_toRationalMap_eq_on_rationalFibers
    (π : X ⟶ C) (sC : C ⟶ S) (sY : Y ⟶ S)
    [Smooth (π ≫ sC)] [IsSeparated sY]
    (hred : ∀ c : S ⟶ C, c ≫ sC = 𝟙 S → IsReduced (pullback π c))
    {f g : X ⟶ Y} (hf : f ≫ sY = π ≫ sC) (hg : g ≫ sY = π ≫ sC) :
    f = g ↔ ∀ c : S ⟶ C, c ≫ sC = 𝟙 S →
      (pullback.fst π c ≫ f).toRationalMap = (pullback.fst π c ≫ g).toRationalMap := by
  refine ⟨fun h c _ ↦ by rw [h], fun h ↦ ?_⟩
  have : IsReduced X := (π ≫ sC).isReduced_of_smooth
  let P := {p : S ⟶ X // p ≫ π ≫ sC = 𝟙 S}
  apply ext_of_dense_iUnion_range_of_isSeparated sY (hf.trans hg.symm) (fun p : P ↦ p.val)
  · apply (π ≫ sC).denseRange_rationalSections.mono
    rintro _ ⟨p, rfl⟩
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_range_self default⟩
  · intro p
    let c := p.val ≫ π
    have hc : c ≫ sC = 𝟙 S := by simpa only [c, Category.assoc] using p.property
    let j := pullback.fst π c
    have := hred c hc
    have hbase (q : X ⟶ Y) (hq : q ≫ sY = π ≫ sC) :
        (j ≫ q) ≫ sY = pullback.snd π c := by
      simp only [Category.assoc, hq, j, pullback.condition_assoc, hc, Category.comp_id]
    have := isOver_toPartialMap (hbase f hf)
    have he := (PartialMap.equiv_toPartialMap_iff_of_isSeparated _ sY (hbase g hg)).mp
      (PartialMap.toRationalMap_eq_iff.mp (h c hc))
    have hfg : j ≫ f = j ≫ g := by
      apply (cancel_epi (pullback π c : Scheme).topIso.hom).mp
      simpa only [toPartialMap, Scheme.topIso_hom, Category.assoc] using he
    -- The rational point of the source lifts to the fiber over its image in the parameter scheme.
    let t := pullback.lift (f := π) (g := c) p.val (𝟙 S) (Category.id_comp c).symm
    simpa only [← Category.assoc, j, t, pullback.lift_fst] using congrArg (t ≫ ·) hfg

/-- If two rational composites agree on an integral fiber, their regular
representatives agree on the fiber of any open where both representatives apply. -/
theorem comp_eq_on_fiber_of_compOfDefined_eq
    {T B : Scheme.{u}} [IsReduced T] [T.IsSeparated] [Y.IsSeparated]
    (π : X ⟶ C) (c : B ⟶ C) [IsIntegral (pullback π c : Scheme)]
    [(pullback π c : Scheme).IsSeparated]
    (e : X ⟶ T) (W : X.Opens) (p q : T.PartialMap Y)
    (l : W.toScheme ⟶ p.domain.toScheme) (m : W.toScheme ⟶ q.domain.toScheme)
    (hl : l ≫ p.domain.ι = W.ι ≫ e) (hm : m ≫ q.domain.ι = W.ι ≫ e)
    (he : let j := (pullback.fst π c ≫ e).toRationalMap
      let x := j.fromFunctionField (IsLocalRing.closedPoint _)
      ∃ (hp : x ∈ p.toRationalMap.domain) (hq : x ∈ q.toRationalMap.domain),
        j.compOfDefined p.toRationalMap hp =
          j.compOfDefined q.toRationalMap hq) :
    pullback.fst (W.ι ≫ π) c ≫ l ≫ p.hom =
      pullback.fst (W.ι ≫ π) c ≫ m ≫ q.hom := by
  by_cases hne : Nonempty (pullback (W.ι ≫ π) c : Scheme)
  · let i := pullback.map (W.ι ≫ π) c π c W.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
    have : IsOpenImmersion i := Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _
    have : IsIntegral (pullback (W.ι ≫ π) c : Scheme) := isIntegral_of_isOpenImmersion i
    have hi : i ≫ pullback.fst π c = pullback.fst (W.ι ≫ π) c ≫ W.ι := by
      simp only [i, pullback.map, pullback.lift_fst]
    obtain ⟨hp, hq, hpq⟩ := he
    have ep := i.comp_compOfDefined_eq_of_lift _ p hp (pullback.fst (W.ι ≫ π) c ≫ l)
      (by rw [Category.assoc, hl, ← reassoc_of% hi])
    have eq := i.comp_compOfDefined_eq_of_lift _ q hq (pullback.fst (W.ι ≫ π) c ≫ m)
      (by rw [Category.assoc, hm, ← reassoc_of% hi])
    apply toRationalMap_injective
    simpa only [Category.assoc] using
      ep.symm.trans ((congrArg (i.toRationalMap.comp ·) hpq).trans eq)
  · let : IsEmpty (pullback (W.ι ≫ π) c : Scheme) := not_nonempty_iff.mp hne
    exact isInitialOfIsEmpty.hom_ext _ _

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.RationalMap

universe u

/-- A dominant evaluation on a smooth family detects rational maps by their generically
defined composites on the fibers over rational points of the parameter scheme. -/
theorem eq_of_compOfDefined_eq_on_rationalFibers
    {k : Type u} [Field k] [IsSepClosed k] {X C T Y : Scheme.{u}}
    [IsIntegral X] [X.IsSeparated] [IsIntegral T] [T.IsSeparated] [Y.IsSeparated]
    (π : X ⟶ C) (sC : C ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [Smooth π] [Smooth sC]
    (e : X ⟶ T) [IsDominant e] (he : e ≫ sT = π ≫ sC)
    {f g : T ⤏ Y} [f.IsOver sT sY] [g.IsOver sT sY]
    (hF : ∀ (c : Spec (.of k) ⟶ C), c ≫ sC = 𝟙 _ →
      IsIntegral (pullback π c : Scheme))
    (hfg : ∀ (c : Spec (.of k) ⟶ C) (hc : c ≫ sC = 𝟙 _),
      letI := hF c hc
      let j := (pullback.fst π c ≫ e).toRationalMap
      let x := j.fromFunctionField (IsLocalRing.closedPoint _)
      ∃ (hf : x ∈ f.domain) (hg : x ∈ g.domain),
        j.compOfDefined f hf = j.compOfDefined g hg) :
    f = g := by
  let p := f.toPartialMap
  let q := g.toPartialMap
  let V := p.domain ⊓ q.domain
  let : Nonempty V := Set.nonempty_coe_sort.mpr (p.dense_domain.inter_of_isOpen_left
    q.dense_domain p.domain.isOpen).nonempty
  let W := e ⁻¹ᵁ V
  have hW : Dense (W : Set X) := W.isOpen.dense (Set.nonempty_coe_sort.mp
    (inferInstanceAs (Nonempty (e ⁻¹ᵁ V))))
  let l := (e ∣_ V) ≫ T.homOfLE (show V ≤ p.domain from inf_le_left)
  let m := (e ∣_ V) ≫ T.homOfLE (show V ≤ q.domain from inf_le_right)
  have hl : l ≫ p.domain.ι = W.ι ≫ e := by simp [l, W]
  have hm : m ≫ q.domain.ι = W.ι ≫ e := by simp [m, W]
  have hp : (l ≫ p.hom) ≫ sY = (W.ι ≫ π) ≫ sC := by
    rw [Category.assoc, p.over sT sY, ← Category.assoc, hl, Category.assoc, he, Category.assoc]
  have hq : (m ≫ q.hom) ≫ sY = (W.ι ≫ π) ≫ sC := by
    rw [Category.assoc, q.over sT sY, ← Category.assoc, hm, Category.assoc, he, Category.assoc]
  have hred (c : Spec (.of k) ⟶ C) : IsReduced (pullback (W.ι ≫ π) c) :=
    GeometricallyReduced.geometrically_isReduced c _ _ (IsPullback.of_hasPullback (W.ι ≫ π) c)
  have h : l ≫ p.hom = m ≫ q.hom := by
    apply (Hom.eq_iff_toRationalMap_eq_on_rationalFibers (W.ι ≫ π) sC sY
      (fun c _ ↦ hred c) hp hq).mpr
    intro c hc
    let := hF c hc
    have : (pullback π c : Scheme).IsSeparated := Scheme.IsSeparated.of_isSeparated
      (pullback.snd π c)
    apply congrArg Hom.toRationalMap
    apply Hom.comp_eq_on_fiber_of_compOfDefined_eq π c e W p q l m hl hm
    simpa only [p, q, toRationalMap_toPartialMap] using hfg c hc
  apply comp_left_injective e.toRationalMap
  have hf := e.comp_eq_toRationalMap_of_lift p W hW l hl
  have hg := e.comp_eq_toRationalMap_of_lift q W hW m hm
  rw [h] at hf
  simpa only [p, q, toRationalMap_toPartialMap] using hf.trans hg.symm

end AlgebraicGeometry.Scheme.RationalMap
