/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import QPainleve.Topology.NoetherianSpace
import TauCeti.AlgebraicGeometry.Fibers.Composition
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.AlgebraicGeometry.Scheme.LocalDimension

/-!
# Curves in fibers of proper morphisms

A proper morphism to a quasi-compact scheme is finite if its fibers over closed points
are finite. If it is not finite, a reduced point closure in one of these fibers
gives a closed integral curve contracted by the morphism.
-/

public section

open CategoryTheory TopologicalSpace TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A proper morphism is quasi-finite at a point if that point lies over an
affine open with affine preimage. -/
theorem quasiFiniteAt_of_isAffineOpen {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {U : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen (f ⁻¹ᵁ U)) {x : X}
    (hx : f x ∈ U) : f.QuasiFiniteAt x := by
  let : IsAffine U.toScheme := hU
  let : IsAffine (f ⁻¹ᵁ U).toScheme := hV
  have : IsFinite (f ∣_ U) := IsFinite.iff_isProper_and_isAffineHom.mpr
    ⟨inferInstance, inferInstance⟩
  let z : (f ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
  have h := (Scheme.Hom.quasiFiniteAt_comp_iff (g := U.ι)).mpr ((f ∣_ U).quasiFiniteAt z)
  rw [morphismRestrict_ι] at h
  exact (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion
    (f := (f ⁻¹ᵁ U).ι) (g := f) (x := z)).mp h

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [CompactSpace Y]

/-- A proper morphism to a quasi-compact scheme is finite exactly when its fibers
over closed points are finite. -/
theorem isFinite_iff_forall_isClosed_finite_preimage_singleton :
    IsFinite f ↔ ∀ y : Y, IsClosed ({y} : Set Y) → (f ⁻¹' {y}).Finite := by
  refine ⟨fun _ y _ ↦ f.finite_preimage_singleton y, fun h ↦ ?_⟩
  choose V hyV hV using fun y : closedPoints Y ↦
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton f y.val (h y.val y.property)
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite) V ?_ hV
  refine top_unique fun x _ ↦ Opens.mem_iSup.mpr ?_
  obtain ⟨y, hy, hyClosed⟩ := isClosed_closure.exists_closed_singleton
    ⟨x, subset_closure (Set.mem_singleton x)⟩
  let y' : closedPoints Y := ⟨y, hyClosed⟩
  exact ⟨y', (specializes_iff_mem_closure.mpr hy).mem_open (V y').isOpen (hyV y')⟩

attribute [local instance] specializationOrder

open Scheme.IdealSheafData

/-- A nonfinite proper morphism to a quasi-compact scheme has a closed integral
curve in a fiber over a closed point. -/
theorem exists_closed_curve_in_fiber_of_not_isFinite (hf : ¬ IsFinite f) :
    ∃ y : Y, IsClosed ({y} : Set Y) ∧ ∃ (C : Scheme.{u}) (i : C ⟶ f.fiber y),
      IsClosedImmersion i ∧ IsIntegral C ∧ topologicalKrullDim C = 1 := by
  have h := mt f.isFinite_iff_forall_isClosed_finite_preimage_singleton.mpr hf
  push Not at h
  obtain ⟨y, hy, hyinf⟩ := h
  let F := f.fiber y
  let : F.Over (Spec (Y.residueField y)) := f.fiberOverSpecResidueField y
  have : LocallyOfFiniteType (F ↘ Spec (Y.residueField y)) :=
    inferInstanceAs (LocallyOfFiniteType (f.fiberToSpecResidueField y))
  have : IsNoetherian F := isNoetherian_of_finiteType (f.fiberToSpecResidueField y)
  have hz : ∃ z : F, ¬ IsClosed ({z} : Set F) := by
    by_contra! hall
    have hs := (isClosed_univ : IsClosed (Set.univ : Set F)).finite_of_subset_closedPoints
      (fun z _ ↦ mem_closedPoints_iff.mpr (hall z))
    exact hyinf ((f.fiberHomeo y).finite_iff.mp (Set.finite_univ_iff.mp hs))
  obtain ⟨z, hz⟩ := hz
  have hzpos : 0 < Order.height z := by
    rw [Order.height_pos]
    intro hmin
    apply hz
    rw [← closure_eq_iff_isClosed]
    refine Set.Subset.antisymm (fun w hw ↦ ?_) subset_closure
    have hwz : w ≤ z := specializes_iff_mem_closure.mpr hw
    exact Set.mem_singleton_iff.mpr (le_antisymm hwz (hmin hwz))
  have hfin : Order.height z < ⊤ := by
    rw [height_eq_toNat_trdeg_residueField (Y.residueField y) z]
    exact ENat.natCast_lt_top _
  have hcurve : ∃ w : F, Order.height w = 1 := by
    by_cases hw : Order.height z ≤ 1
    · exact ⟨z, le_antisymm hw (Order.one_le_iff_pos.mpr hzpos)⟩
    · obtain ⟨w, -, hw⟩ := (Order.coe_lt_height_iff (n := 1) hfin).mp
        (by simpa using lt_of_not_ge hw)
      exact ⟨w, hw⟩
  obtain ⟨w, hw⟩ := hcurve
  let I := vanishingIdeal (X := F) ⟨closure {w}, isClosed_closure⟩
  refine ⟨y, hy, I.subscheme, I.subschemeι, inferInstance,
    isIntegral_subscheme_vanishingIdeal isIrreducible_singleton.closure, ?_⟩
  rw [← topologicalKrullDim_range_of_isPreimmersion I.subschemeι, I.range_subschemeι,
    coe_support_vanishingIdeal, Closeds.coe_mk,
    ← height_eq_topologicalKrullDim_closure_singleton, hw]
  rfl

end AlgebraicGeometry.Scheme.Hom
