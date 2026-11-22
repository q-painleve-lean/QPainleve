/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs
import QPainleve.RingTheory.Ideal.Localization.RegularPair
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine

/-!
# Regular pairs for point ideals

A point whose local ring is regular of dimension two has a basis of affine neighborhoods
on which its reduced closure is cut out by a regular pair. This supplies the center
equations used in the affine charts of its blowup.
-/

public section

open RingTheory.Sequence TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {p : X}

local notation "Iₚ" =>
  vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)

/-- Every open neighborhood of a point with a two-dimensional regular local ring contains
an affine neighborhood on which the reduced closure of that point has a weakly regular
generating pair. -/
theorem exists_mem_le_span_pair_vanishingIdeal_closure_singleton
    [IsLocallyNoetherian X] [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) {W : X.Opens} (hp : p ∈ W) :
    ∃ (U : X.affineOpens), p ∈ U.val ∧ U.val ≤ W ∧ ∃ a b : Γ(X, U),
      Ideal.span {a, b} = (Iₚ).ideal U ∧ IsWeaklyRegular Γ(X, U) [a, b] := by
  obtain ⟨U, hU, hpU, hUW⟩ := exists_isAffineOpen_mem_and_subset hp
  let P := (hU.primeIdealOf ⟨p, hpU⟩).asIdeal
  let _ := X.presheaf.algebra_section_stalk ⟨p, hpU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk p) P := hU.isLocalization_stalk ⟨p, hpU⟩
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨r, hr, hparams⟩ := Ideal.exists_notMem_span_pair_of_isRegularLocalRing P
    (X.presheaf.stalk p) hdim
  let V := X.affineBasicOpen (U := ⟨U, hU⟩) r
  have := hU.isLocalization_basicOpen r
  have hpV : p ∈ X.basicOpen r := (X.mem_basicOpen r p hpU).mpr
    ((IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk p) P r).mpr hr)
  obtain ⟨a, b, hspan, hab⟩ := hparams Γ(X, X.basicOpen r)
  refine ⟨V, hpV, (X.basicOpen_le r).trans hUW, a, b, hspan.trans ?_, hab⟩
  have hP : (Iₚ).ideal ⟨U, hU⟩ = P :=
    vanishingIdeal_closure_singleton_ideal p ⟨U, hU⟩ hpU
  rw [← (Iₚ).map_ideal_basicOpen ⟨U, hU⟩ r, hP]
  rfl

end AlgebraicGeometry.Scheme.IdealSheafData
