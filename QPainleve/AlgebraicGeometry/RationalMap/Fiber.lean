/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsSepClosed

import TauCeti.AlgebraicGeometry.Morphisms.Separated
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RationalPoint

/-!
# Comparing morphisms on rational fibers

Two morphisms from a smooth scheme over a separably closed field to a separated
scheme agree if their restrictions to each rational fiber agree as rational maps.
Reducedness extends the equality over each fiber, and the density of rational
sections extends it over the whole source. The proof uses Tau Ceti's
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

end AlgebraicGeometry.Scheme.Hom
