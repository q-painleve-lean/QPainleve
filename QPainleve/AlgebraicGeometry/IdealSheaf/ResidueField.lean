/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.ResidueField
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# The ideal sheaf of the closure of a point

The kernel of the morphism from a residue field defines the reduced closure of the point.
At a closed point this identifies the reduced-center and residue-field descriptions of point
blowups.
-/

public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The kernel of a residue-field morphism is the vanishing ideal of the closure of its point. -/
theorem ker_fromSpecResidueField_eq_vanishingIdeal {X : Scheme} (p : X) :
    (X.fromSpecResidueField p).ker =
      IdealSheafData.vanishingIdeal ⟨closure {p}, isClosed_closure⟩ := by
  let i := X.fromSpecResidueField p
  have : QuasiCompact i := ⟨fun U _ _ ↦ (Set.toFinite (i ⁻¹' U)).isCompact⟩
  have hs : i.ker.support = ⟨closure {p}, isClosed_closure⟩ := by
    apply SetLike.coe_injective
    rw [i.support_ker, range_fromSpecResidueField]
    rfl
  rw [← hs]
  exact le_antisymm (by rw [IdealSheafData.vanishingIdeal_support]; exact i.ker.le_radical)
    (IdealSheafData.vanishingIdeal_le_ker_of_range_subset i i.range_subset_ker_support)

end AlgebraicGeometry.Scheme
