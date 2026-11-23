/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# The reduced closure of a point

The kernel of the residue-field morphism is the vanishing ideal of the
topological closure of its point. This identifies the two descriptions of the
reduced ideal used to blow up a closed point.
-/

public section

open TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- The residue-field morphism has kernel the ideal of the reduced closure of the point. -/
theorem ker_fromSpecResidueField_eq_vanishingIdeal (X : Scheme.{u}) (p : X) :
    (X.fromSpecResidueField p).ker =
      IdealSheafData.vanishingIdeal (Closeds.mk (closure ({p} : Set X)) isClosed_closure) := by
  let f := X.fromSpecResidueField p
  have : Finite (Spec (X.residueField p)) :=
    inferInstanceAs (Finite (PrimeSpectrum (X.residueField p)))
  have : QuasiCompact f := ⟨fun U _ _ ↦ (Set.toFinite (f ⁻¹' U)).isCompact⟩
  have hs : f.ker.support = Closeds.mk (closure ({p} : Set X)) isClosed_closure := by
    ext x
    simp only [f, Hom.support_ker, range_fromSpecResidueField]
    rfl
  rw [← hs]
  refine le_antisymm ?_ (IdealSheafData.vanishingIdeal_le_ker_of_range_subset _
    f.range_subset_ker_support)
  rw [IdealSheafData.vanishingIdeal_support]
  exact IdealSheafData.le_radical _

end AlgebraicGeometry.Scheme
