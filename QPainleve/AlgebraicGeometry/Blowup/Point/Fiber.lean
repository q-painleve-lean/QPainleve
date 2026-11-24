/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Descent
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.AlgebraicGeometry.Blowup.Smooth
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.Blowup.Restriction

/-!
# Connected fibers of a point blowup

At a regular closed point of local dimension two, the exceptional fiber is integral.
Every other fiber of the blowup projection is a singleton.
-/

public section

open CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {p : X} [IsLocallyNoetherian X]
  [IsRegularLocalRing (X.presheaf.stalk p)]

local notation "Iₚ" =>
  vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)
local notation "πₚ" => blowupToBase Iₚ
local notation "Eₚ" => comap Iₚ πₚ

/-- The blowup of a regular closed point of local dimension two is an isomorphism
precisely away from that point. -/
theorem centre_blowupToBase_closed_point (hp : IsClosed ({p} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) : (πₚ).centre = {p} := by
  have hs : ((Iₚ).support : Set X) = {p} :=
    (coe_support_vanishingIdeal _).trans hp.closure_eq
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxp
    rw [Hom.centre_def, Set.mem_compl_iff] at hx
    apply hx
    apply (πₚ).le_isoLocus_iff.mpr (Iₚ).isIso_blowupToBase_restrict_compl_support
    simpa only [← SetLike.mem_coe, Closeds.coe_compl, hs, Set.mem_compl_iff] using hxp
  · rw [Set.singleton_subset_iff, Hom.centre_def, Set.mem_compl_iff]
    intro hi
    have : Surjective πₚ := surjective_blowupToBase_point hp hdim
    obtain ⟨x, hx⟩ := (πₚ).surjective p
    have hE : ((Eₚ).support : Set (Iₚ).blowup) = πₚ ⁻¹' {p} := by
      rw [← range_subschemeι, range_subschemeι_comap_pointBlowup hp]
    have hmem : x ∈ (Eₚ).support := by
      rw [← SetLike.mem_coe, hE]
      exact hx
    have : IsLocallyNoetherian (Iₚ).blowup :=
      LocallyOfFiniteType.isLocallyNoetherian πₚ
    obtain ⟨q, hq, _⟩ :=
      (Iₚ).isEffectiveCartier_comap_blowupToBase.mem_support_iff_exists_codimensionOnePoint.mp hmem
    have heq : πₚ (q : (Iₚ).blowup) = p := by
      rw [← SetLike.mem_coe, hE] at hq
      exact hq
    have hc := (πₚ).coheight_eq_of_apply_mem_isoLocus (x := q) (heq.symm ▸ hi)
    rw [heq, q.property] at hc
    rw [ringKrullDim_stalk_eq_coheight, hc] at hdim
    norm_num at hdim

/-- Blowing up a regular closed point of local dimension two has connected fibers. -/
theorem isConnected_preimage_singleton_blowup_closed_point (hp : IsClosed ({p} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (y : X) :
    _root_.IsConnected (πₚ ⁻¹' {y}) := by
  by_cases hy : y = p
  · subst y
    have : IsIntegral (Eₚ).subscheme := isIntegral_exceptional_blowup_closed_point hdim hp
    rw [← range_subschemeι_comap_pointBlowup hp, ← Set.image_univ]
    exact isConnected_univ.image _ (Eₚ).subschemeι.continuous.continuousOn
  · have : Surjective πₚ := surjective_blowupToBase_point hp hdim
    obtain ⟨x, hx⟩ := (πₚ).surjective y
    have hs : ((Iₚ).support : Set X) = {p} :=
      (coe_support_vanishingIdeal _).trans hp.closure_eq
    have hinj := (Iₚ).injOn_blowupToBase_compl_support
    rw [hs] at hinj
    have hsub : πₚ ⁻¹' {y} ⊆ πₚ ⁻¹' {p}ᶜ := Set.preimage_mono
      (Set.singleton_subset_iff.mpr hy)
    have h : (πₚ ⁻¹' {y}).Subsingleton := fun a ha b hb ↦
      hinj (hsub ha) (hsub hb)
        ((Set.mem_singleton_iff.mp ha).trans (Set.mem_singleton_iff.mp hb).symm)
    rw [h.eq_singleton_of_mem hx]
    exact isConnected_singleton

end AlgebraicGeometry.Scheme.IdealSheafData
