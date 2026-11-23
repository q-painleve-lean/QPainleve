/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
public import QPainleve.AlgebraicGeometry.Morphisms.Modification.Fiber

import QPainleve.AlgebraicGeometry.Blowup.Point.Fiber
import QPainleve.AlgebraicGeometry.Blowup.Tower.Descent
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
import Mathlib.Topology.Connected.Clopen

/-!
# Uniqueness of a contraction from its exceptional curves

Closed point blowup towers of smooth surfaces have connected fibers over closed
points. A second modification contracting every curve exceptional for such a tower
is constant on its fibers and therefore descends. Two towers on the same source
that contract the same prime divisors consequently have canonically isomorphic targets.

The descent applies Tau Ceti's `Scheme.Hom.existsUnique_comp_eq_of_universallyClosed`
through the closed point tower descent theorem.
-/

public section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [PerfectField k]
  {X Y V : Scheme.{u}} {m n : ℕ} {T : BlowupTower X m V} {U : BlowupTower Y n V}

local notation "base" => Spec (CommRingCat.of k)

/-- A closed point blowup tower of a smooth surface has connected fibers over the closed
points of its base, including fibers meeting infinitely near exceptional curves. -/
theorem isConnected_preimage_singleton (hT : IsClosedPointTower X T)
    (f : X ⟶ base) [SmoothOfRelativeDimension 2 f] (x : X) (hx : IsClosed {x}) :
    _root_.IsConnected (T.toBase ⁻¹' {x}) := by
  induction hT with
  | nil =>
    rw [toBase_nil]
    exact isConnected_singleton
  | @snoc _ W R I hR p hp hI ih =>
    subst I
    rw [toBase_snoc, Scheme.ker_fromSpecResidueField_eq_vanishingIdeal]
    let J := Scheme.IdealSheafData.vanishingIdeal
      (X := W) ⟨closure ({p} : Set W), isClosed_closure⟩
    let π := J.blowupToBase
    have hD := hR.smoothOfRelativeDimension f
    have : Smooth (R.toBase ≫ f) := hD.smooth 2 _
    have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (R.toBase ≫ f)
    have := isRegularLocalRing_stalk_of_smooth (R.toBase ≫ f) p
    have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
      (R.toBase ≫ f) 2).mp hD).2 p hp
    have hconn := Scheme.IdealSheafData.isConnected_preimage_singleton_blowup_closed_point hp hdim
    have : Surjective π := Scheme.IdealSheafData.surjective_blowupToBase_point hp hdim
    have hq := (π.isClosedMap.isQuotientMap π.continuous π.surjective).isCoinducing
    have hpre : (π ≫ R.toBase) ⁻¹' {x} = π ⁻¹' (R.toBase ⁻¹' {x}) :=
      Set.ext fun _ ↦ by simp only [Set.mem_preimage, Scheme.Hom.comp_apply]
    rw [hpre]
    exact hq.isConnected_preimage_of_isClosed hconn (hx.preimage R.toBase.continuous) ih

variable [IsIntegral X]

/-- A surface modification that contracts all the prime divisors contracted by a closed
point blowup tower descends uniquely to the base of the tower. -/
theorem existsUnique_comp_eq_toBase_of_exceptional_divisors_subset
    (hT : IsClosedPointTower X T) (f : X ⟶ base) [SmoothOfRelativeDimension 2 f]
    [QuasiCompact f] (g : V ⟶ Y)
    [IsIntegral Y] [IsNormalScheme Y] [IsNoetherian Y] [IsModification g]
    (hY : topologicalKrullDim Y ≤ 2)
    (hsub : {z : V | T.toBase z ∈ T.toBase.centre ∧ coheight z = 1} ⊆
      {z : V | g z ∈ g.centre ∧ coheight z = 1}) :
    ∃! a : X ⟶ Y, T.toBase ≫ a = g := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have : IsNoetherian X := isNoetherian_of_finiteType f
  have : IsRegular X := IsRegular.of_smooth f
  have : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f
  have : IsIntegral V := hT.isIntegral f
  have : IsNoetherian V := T.isNoetherian
  have := hT.smoothOfRelativeDimension f
  have hV := topologicalKrullDim_eq_of_smoothOfRelativeDimension (T.toBase ≫ f) (n := 2)
  refine hT.existsUnique_comp_eq_toBase f g
    (T.toBase.factorsThrough_of_exceptional_divisors_subset g hV.le hY hsub fun x hx ↦ ?_)
  exact (hT.isConnected_preimage_singleton f x
    (mem_closedPoints_iff.mp (T.toBase.centre_subset_closedPoints hX.le hx))).isPreconnected

variable [IsIntegral Y]

/-- If two projections by closed point blowup towers from a common smooth surface contract
the same prime divisors, their bases are uniquely isomorphic compatibly with the projections. -/
theorem existsUnique_iso_of_eq_exceptional_divisors
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Y U)
    (f : X ⟶ base) (g : Y ⟶ base)
    [SmoothOfRelativeDimension 2 f] [SmoothOfRelativeDimension 2 g]
    [QuasiCompact f] [QuasiCompact g]
    (hE : {z : V | T.toBase z ∈ T.toBase.centre ∧ coheight z = 1} =
      {z : V | U.toBase z ∈ U.toBase.centre ∧ coheight z = 1}) :
    ∃! e : X ≅ Y, T.toBase ≫ e.hom = U.toBase := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : Smooth g := SmoothOfRelativeDimension.smooth 2 g
  have : IsNoetherian X := isNoetherian_of_finiteType f
  have : IsNoetherian Y := isNoetherian_of_finiteType g
  have : IsRegular X := IsRegular.of_smooth f
  have : IsRegular Y := IsRegular.of_smooth g
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have hY := topologicalKrullDim_eq_of_smoothOfRelativeDimension g (n := 2)
  have : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f
  have : IsModification U.toBase := hU.isModification_of_smoothOfRelativeDimension_two g
  obtain ⟨a, ha, huniq⟩ :=
    hT.existsUnique_comp_eq_toBase_of_exceptional_divisors_subset f U.toBase hY.le hE.le
  obtain ⟨b, hb, _⟩ :=
    hU.existsUnique_comp_eq_toBase_of_exceptional_divisors_subset g T.toBase hX.le hE.ge
  have := hT.epi_toBase f
  have := hU.epi_toBase g
  refine ⟨⟨a, b, ?_, ?_⟩, ha, fun e he ↦ Iso.ext (huniq e.hom he)⟩
  · apply (cancel_epi T.toBase).mp
    rw [← Category.assoc, ha, hb, Category.comp_id]
  · apply (cancel_epi U.toBase).mp
    rw [← Category.assoc, hb, ha, Category.comp_id]

/-- If the projections to the two bases commute with the maps to the coefficient field,
the canonical isomorphism between those bases does as well. -/
theorem existsUnique_iso_over_of_eq_exceptional_divisors
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Y U)
    (f : X ⟶ base) (g : Y ⟶ base)
    [SmoothOfRelativeDimension 2 f] [SmoothOfRelativeDimension 2 g]
    [QuasiCompact f] [QuasiCompact g]
    (hE : {z : V | T.toBase z ∈ T.toBase.centre ∧ coheight z = 1} =
      {z : V | U.toBase z ∈ U.toBase.centre ∧ coheight z = 1})
    (hcomp : T.toBase ≫ f = U.toBase ≫ g) :
    ∃! e : X ≅ Y, T.toBase ≫ e.hom = U.toBase ∧ e.hom ≫ g = f := by
  obtain ⟨e, he, huniq⟩ := hT.existsUnique_iso_of_eq_exceptional_divisors hU f g hE
  have := hT.epi_toBase f
  refine ⟨e, ⟨he, (cancel_epi T.toBase).mp ?_⟩, fun a ha ↦ huniq a ha.1⟩
  rw [← Category.assoc, he, hcomp]

end QPainleve.BlowupTower.IsClosedPointTower
