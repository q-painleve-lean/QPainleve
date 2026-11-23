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

A morphism from a reduced scheme gives its schematic image the reduced structure.
The kernel of a field-valued point thus defines the reduced closure of the point.
This identifies the reduced-center and residue-field descriptions of point blowups.
-/

public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- A reduced source determines the reduced scheme structure on its schematic image. -/
theorem Hom.ker_eq_vanishingIdeal_support {X Y : Scheme} (f : X ⟶ Y) [IsReduced X] :
    f.ker = IdealSheafData.vanishingIdeal f.ker.support :=
  le_antisymm (by rw [IdealSheafData.vanishingIdeal_support]; exact f.ker.le_radical)
    (IdealSheafData.vanishingIdeal_le_ker_of_range_subset f f.range_subset_ker_support)

/-- The kernel of a residue-field morphism is the vanishing ideal of the closure of its point. -/
theorem ker_fromSpecResidueField_eq_vanishingIdeal {X : Scheme} (p : X) :
    (X.fromSpecResidueField p).ker =
      IdealSheafData.vanishingIdeal ⟨closure {p}, isClosed_closure⟩ := by
  have : QuasiCompact (X.fromSpecResidueField p) :=
    ⟨fun U _ _ ↦ (Set.toFinite ((X.fromSpecResidueField p) ⁻¹' U)).isCompact⟩
  rw [Hom.ker_eq_vanishingIdeal_support]
  congr 1
  apply SetLike.coe_injective
  rw [Hom.support_ker, range_fromSpecResidueField]
  rfl

/-- A field-valued point has the same kernel ideal as the map from its residue field. -/
theorem Hom.ker_eq_ker_fromSpecResidueField {k : Type*} [Field k]
    {X : Scheme} (s : Spec (.of k) ⟶ X) :
    s.ker = (X.fromSpecResidueField (s (IsLocalRing.closedPoint k))).ker := by
  have : QuasiCompact s := ⟨fun U _ _ ↦ (Set.toFinite (s ⁻¹' U)).isCompact⟩
  have hrange : Set.range s = {s (IsLocalRing.closedPoint k)} :=
    Set.range_eq_singleton fun z ↦ congrArg s (Subsingleton.elim z _)
  rw [s.ker_eq_vanishingIdeal_support, ker_fromSpecResidueField_eq_vanishingIdeal]
  congr 1
  apply SetLike.coe_injective
  rw [s.support_ker, hrange]
  rfl

end AlgebraicGeometry.Scheme
