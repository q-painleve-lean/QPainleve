/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Pullback

/-!
# Isomorphisms of blowups

Tau Ceti constructs the lift of an isomorphism that identifies two center ideals.
We record its specialization to an inverse-image center, uniqueness as an isomorphism,
and compatibility with exceptional ideals.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- Over the inverse-image center, the lift is the native map of blowups. -/
@[simp]
theorem blowupIso_hom_comap (J : Y.IdealSheafData) (e : X ≅ Y) :
    (blowupIso e (J := J) rfl).hom = J.blowupMap e.hom :=
  (eq_blowupIso_hom e rfl (J.blowupMap_blowupToBase e.hom)).symm

/-- The projection square determines the isomorphism of blowups. -/
theorem blowupIso_unique (J : Y.IdealSheafData) (e : X ≅ Y) {I : X.IdealSheafData}
    (h : J.comap e.hom = I) (g : I.blowup ≅ J.blowup)
    (hg : g.hom ≫ J.blowupToBase = I.blowupToBase ≫ e.hom) :
    g = blowupIso e h.symm :=
  Iso.ext (eq_blowupIso_hom e h.symm hg)

/-- The lifted isomorphism pulls back the target exceptional ideal to the source exceptional
ideal. -/
@[simp]
theorem comap_blowupIso_hom (J : Y.IdealSheafData) (e : X ≅ Y) {I : X.IdealSheafData}
    (h : J.comap e.hom = I) :
    (J.comap J.blowupToBase).comap (blowupIso e h.symm).hom = I.comap I.blowupToBase := by
  subst I
  simpa only [blowupIso_hom_comap] using J.comap_comap_blowupMap e.hom

end AlgebraicGeometry.Scheme.IdealSheafData
