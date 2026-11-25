/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Ideals of closed fibers

The scheme-theoretic fiber over a closed point is the closed subscheme defined
by the pullback of the ideal of the point.
-/

public section

open CategoryTheory AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Over a closed point, the fiber identifies over the total space with the
subscheme defined by the pulled-back residue-field ideal. -/
theorem exists_fiberIso_subscheme_of_isClosed {X C : Scheme.{u}} (f : X ⟶ C) {z : C}
    (hz : IsClosed ({z} : Set C)) :
    let F := (C.fromSpecResidueField z).ker.comap f
    ∃ e : f.fiber z ≅ F.subscheme, e.hom ≫ F.subschemeι = f.fiberι z := by
  intro F
  have : IsClosedImmersion (C.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.mp hz
  have hker : (f.fiberι z).ker = F := ker_fst_of_isClosedImmersion (C.fromSpecResidueField z) f
  have : IsClosedImmersion (f.fiberι z) :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback f (C.fromSpecResidueField z)).flip inferInstance
  obtain ⟨e, he⟩ := F.exists_iso_of_comap_eq_ker (Iso.refl X) (f.fiberι z) (by
    simpa only [Iso.refl_hom, comap_id] using hker.symm)
  exact ⟨e, by simpa only [Iso.refl_hom, Category.comp_id] using he⟩

end AlgebraicGeometry.Scheme.Hom
