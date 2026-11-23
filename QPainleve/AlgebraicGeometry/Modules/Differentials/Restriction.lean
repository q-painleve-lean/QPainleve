/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical

import Mathlib.CategoryTheory.EqToHom
import TauCeti.AlgebraicGeometry.Modules.Differentials.Pullback
import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Restriction

/-!
# Restriction of canonical bundles

Along an open immersion over the base, the map on top forms is an isomorphism.
In particular, an isomorphism over the base identifies the canonical classes.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

universe u

namespace QPainleve

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of R))] [IsOpenImmersion f] (n : ℕ)
  [SmoothOfRelativeDimension n (X ↘ Spec (.of R))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (.of R))]

/-- For an open immersion the map on canonical bundles is invertible. -/
instance isIso_topDifferentialFormsMap_of_isOpenImmersion :
    IsIso (topDifferentialFormsMap R f n) := by
  have hCotangent := isIso_cotangentMap_of_isOpenImmersion R f
  have hExterior := @Functor.map_isIso _ _ _ _ _ _
    (SheafOfModules.exteriorPower X.sheaf n) (cotangentMap R f) hCotangent
  have hComparison := isIso_pullbackExteriorPowerComparison_app_of_isOpenImmersion f n
    (Y.relativeDifferentials R)
  rw [topDifferentialFormsMap_def]
  -- The end factors are the transports between top forms and the underlying canonical sheaves.
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ ?_ ?_
  · exact (eqToIso (by rw [InvertibleSheaf.pullback_obj_obj, canonicalBundle_obj,
      differentialForms_def]; rfl)).isIso_hom
  · exact @IsIso.comp_isIso _ _ _ _ _ _ _ hComparison
      (@IsIso.comp_isIso _ _ _ _ _ _ _ hExterior
        (eqToIso (by rw [canonicalBundle_obj, differentialForms_def])).isIso_hom)

/-- The canonical class restricts to the canonical class under an open immersion over the base. -/
@[simp]
theorem _root_.TauCeti.AlgebraicGeometry.LineBundleClass.mk_pullback_canonicalBundle :
    LineBundleClass.mk ((InvertibleSheaf.pullback f).obj (canonicalBundle R Y n)) =
      LineBundleClass.mk (canonicalBundle R X n) := by
  rw [LineBundleClass.mk_eq_mk_iff]
  exact ⟨@asIso _ _ _ _ _ (isIso_topDifferentialFormsMap_of_isOpenImmersion R f n)⟩

end QPainleve
