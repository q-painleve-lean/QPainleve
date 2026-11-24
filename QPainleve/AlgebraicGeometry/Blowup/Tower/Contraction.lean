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
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition
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
  {X Y V W : Scheme.{u}} {m n : ℕ} {T : BlowupTower X m V} {U : BlowupTower Y n W}

local notation "base" => Spec (CommRingCat.of k)

/-- The inverse image of a closed connected subset under a closed point blowup tower
of a smooth surface is connected. -/
theorem isConnected_preimage_of_isClosed (hT : IsClosedPointTower X T)
    (f : X ⟶ base) [SmoothOfRelativeDimension 2 f] {S : Set X}
    (hS : IsClosed S) (hconn : _root_.IsConnected S) :
    _root_.IsConnected (T.toBase ⁻¹' S) := by
  induction hT with
  | nil =>
    rw [toBase_nil]
    exact hconn
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
    have hfib := Scheme.IdealSheafData.isConnected_preimage_singleton_blowup_closed_point hp hdim
    have : Surjective π := Scheme.IdealSheafData.surjective_blowupToBase_point hp hdim
    have hq := (π.isClosedMap.isQuotientMap π.continuous π.surjective).isCoinducing
    rw [funext (Scheme.Hom.comp_apply _ _)]
    exact hq.isConnected_preimage_of_isClosed hfib (hS.preimage R.toBase.continuous) ih

/-- A closed point blowup tower of a smooth surface has connected fibers over the closed
points of its base, including fibers meeting infinitely near exceptional curves. -/
theorem isConnected_preimage_singleton (hT : IsClosedPointTower X T)
    (f : X ⟶ base) [SmoothOfRelativeDimension 2 f] (x : X) (hx : IsClosed {x}) :
    _root_.IsConnected (T.toBase ⁻¹' {x}) :=
  hT.isConnected_preimage_of_isClosed f hx isConnected_singleton

variable [IsIntegral X]

/-- Over an open of the base of a closed point blowup tower, a surface modification
descends if it contracts the exceptional fibers lying over that open. -/
theorem existsUnique_comp_eq_morphismRestrict_of_preimage_centre_subset
    (hT : IsClosedPointTower X T) (f : X ⟶ base) [SmoothOfRelativeDimension 2 f]
    (g : V ⟶ Y) [IsIntegral Y] [IsNormalScheme Y] [IsNoetherian Y] [IsModification g]
    (hY : topologicalKrullDim Y ≤ 2) (U : X.Opens)
    (hsub : ∀ z : V, T.toBase z ∈ U → T.toBase z ∈ T.toBase.centre → g z ∈ g.centre) :
    ∃! a : U.toScheme ⟶ Y, (T.toBase ∣_ U) ≫ a = (T.toBase ⁻¹ᵁ U).ι ≫ g := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have : IsRegular X := IsRegular.of_smooth f
  have : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f
  have : Smooth (T.toBase ≫ f) := (hT.smoothOfRelativeDimension f).smooth
  have : IsRegular V := IsRegular.of_smooth (T.toBase ≫ f)
  apply hT.existsUnique_comp_eq_morphismRestrict f U g
  intro x y hxy
  have he : T.toBase x.val = T.toBase y.val := by
    simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hxy
  have hconn (hx : T.toBase x.val ∈ T.toBase.centre) :
      _root_.IsPreconnected (T.toBase ⁻¹' {T.toBase x.val}) :=
    (hT.isConnected_preimage_singleton f _ (mem_closedPoints_iff.mp
      (T.toBase.centre_subset_closedPoints hX.le hx))).isPreconnected
  simp only [Scheme.Hom.comp_apply]
  apply T.toBase.eq_of_apply_eq_of_fiber_mapsTo_centre g hY he hconn
  intro hx z hz
  have hz' : T.toBase z = T.toBase x.val := hz
  exact hsub z (hz'.symm ▸ T.toBase.mem_preimage.mp x.property) (hz'.symm ▸ hx)

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

/-- If two closed point blowup towers contract the same prime divisors under an
isomorphism of their top surfaces, their bases are uniquely isomorphic compatibly
with the projections. -/
theorem existsUnique_iso_of_eq_exceptional_divisors
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Y U) (e : V ≅ W)
    (f : X ⟶ base) (g : Y ⟶ base)
    [SmoothOfRelativeDimension 2 f] [SmoothOfRelativeDimension 2 g]
    [QuasiCompact f] [QuasiCompact g]
    (hE : ∀ x : V, coheight x = 1 →
      (T.toBase x ∈ T.toBase.centre ↔ U.toBase (e.hom x) ∈ U.toBase.centre)) :
    ∃! a : X ≅ Y, T.toBase ≫ a.hom = e.hom ≫ U.toBase := by
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
  have : IsIntegral V := hT.isIntegral f
  have : IsIntegral W := hU.isIntegral g
  have hcentreT : (e.inv ≫ T.toBase).centre = T.toBase.centre := by
    rw [Scheme.Hom.centre_comp, e.inv.centre_eq_empty_iff.mpr inferInstance, Set.image_empty,
      Set.union_empty]
  have hcentreU : (e.hom ≫ U.toBase).centre = U.toBase.centre := by
    rw [Scheme.Hom.centre_comp, e.hom.centre_eq_empty_iff.mpr inferInstance, Set.image_empty,
      Set.union_empty]
  obtain ⟨a, ha, huniq⟩ :=
    hT.existsUnique_comp_eq_toBase_of_exceptional_divisors_subset f (e.hom ≫ U.toBase) hY.le
      (fun x hx ↦ ⟨hcentreU ▸ (hE x hx.2).mp hx.1, hx.2⟩)
  obtain ⟨b, hb, _⟩ :=
    hU.existsUnique_comp_eq_toBase_of_exceptional_divisors_subset g (e.inv ≫ T.toBase) hX.le
      (fun y hy ↦ by
        have htop := e.inv.isoLocus_eq_top_iff.mpr inferInstance
        have hy' := (e.inv.coheight_eq_of_apply_mem_isoLocus (x := y)
          (by simp [htop])).trans hy.2
        refine ⟨hcentreT ▸ (hE (e.inv y) hy').mpr ?_, hy.2⟩
        simpa only [← Scheme.Hom.comp_apply, Iso.inv_hom_id, Category.id_comp] using hy.1)
  have := hT.epi_toBase f
  have := hU.epi_toBase g
  refine ⟨⟨a, b, ?_, ?_⟩, ha, fun a' ha' ↦ Iso.ext (huniq a'.hom ha')⟩
  · apply (cancel_epi T.toBase).mp
    rw [← Category.assoc, ha, Category.assoc, hb, Iso.hom_inv_id_assoc, Category.comp_id]
  · apply (cancel_epi U.toBase).mp
    rw [← Category.assoc, hb, Category.assoc, ha, Iso.inv_hom_id_assoc, Category.comp_id]

/-- If the projections from isomorphic top surfaces commute over the coefficient field,
the canonical isomorphism between their bases does as well. -/
theorem existsUnique_iso_over_of_eq_exceptional_divisors
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Y U) (e : V ≅ W)
    (f : X ⟶ base) (g : Y ⟶ base)
    [SmoothOfRelativeDimension 2 f] [SmoothOfRelativeDimension 2 g]
    [QuasiCompact f] [QuasiCompact g]
    (hE : ∀ x : V, coheight x = 1 →
      (T.toBase x ∈ T.toBase.centre ↔ U.toBase (e.hom x) ∈ U.toBase.centre))
    (hcomp : T.toBase ≫ f = e.hom ≫ U.toBase ≫ g) :
    ∃! a : X ≅ Y, T.toBase ≫ a.hom = e.hom ≫ U.toBase ∧ a.hom ≫ g = f := by
  obtain ⟨a, ha, huniq⟩ := hT.existsUnique_iso_of_eq_exceptional_divisors hU e f g hE
  have := hT.epi_toBase f
  refine ⟨a, ⟨ha, (cancel_epi T.toBase).mp ?_⟩, fun b hb ↦ huniq b hb.1⟩
  rw [← Category.assoc, ha, Category.assoc, hcomp]

end QPainleve.BlowupTower.IsClosedPointTower
