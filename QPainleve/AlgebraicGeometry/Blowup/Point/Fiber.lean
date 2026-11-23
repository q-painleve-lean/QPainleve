/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Smooth

/-!
# Connected fibers of a point blowup

At a regular closed point of local dimension two, the exceptional fiber is integral.
Every other fiber of the blowup projection is a singleton.
-/

public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {p : X} [IsLocallyNoetherian X]
  [IsRegularLocalRing (X.presheaf.stalk p)]

local notation "Iₚ" =>
  vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)
local notation "πₚ" => blowupToBase Iₚ
local notation "Eₚ" => comap Iₚ πₚ

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
