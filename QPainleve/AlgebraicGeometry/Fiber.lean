/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Fibers under base change without residue field extension

A cartesian square induces an isomorphism on the fibers at a point where the base
change induces an isomorphism on residue fields. The isomorphism of fibers
commutes with that specified isomorphism of residue spectra.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- The fibers in a cartesian square are isomorphic over the induced residue field
isomorphism, after composing the changed fiber map with the specified map of residue spectra. -/
theorem CategoryTheory.IsPullback.nonempty_iso_fiberToSpecResidueField
    {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (H : IsPullback fst snd f g) (y : Y) [IsIso (g.residueFieldMap y)] :
    Nonempty (Over.mk (snd.fiberToSpecResidueField y ≫ Spec.map (g.residueFieldMap y)) ≅
      Over.mk (f.fiberToSpecResidueField (g y))) := by
  have h := isPullback_fiberToSpecResidueField_of_isPullback H y
  have hbase : IsIso (Spec.map (g.residueFieldMap y)) := inferInstance
  exact ⟨Over.isoMk (@asIso _ _ _ _ _ (h.isIso_fst_of_isIso hbase)) h.w⟩
