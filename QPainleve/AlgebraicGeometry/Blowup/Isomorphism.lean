/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Pullback

/-!
# Isomorphisms of blowups

An isomorphism that identifies two center ideals lifts to their blowups. The lift is
characterized by the square with the blowup projections, and preserves the exceptional
ideals. The construction uses Tau Ceti's `blowupMap` and its flat base change theorem.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y Z : Scheme.{u}}

/-- The lift of an isomorphism that pulls the target center ideal back to the source center
ideal. -/
def blowupIso (J : Y.IdealSheafData) (e : X ≅ Y) {I : X.IdealSheafData}
    (h : J.comap e.hom = I) : I.blowup ≅ J.blowup :=
  letI := (J.isPullback_blowupMap_of_flat e.hom).isIso_snd_of_isIso
  eqToIso (congrArg blowup h.symm) ≪≫ asIso (J.blowupMap e.hom)

/-- The lifted isomorphism lies over the given base isomorphism. -/
@[reassoc (attr := simp)]
theorem blowupIso_hom_blowupToBase (J : Y.IdealSheafData) (e : X ≅ Y)
    {I : X.IdealSheafData} (h : J.comap e.hom = I) :
    (J.blowupIso e h).hom ≫ J.blowupToBase = I.blowupToBase ≫ e.hom := by
  subst I
  simp [blowupIso]

/-- The projection square determines the isomorphism of blowups. -/
theorem blowupIso_unique (J : Y.IdealSheafData) (e : X ≅ Y)
    {I : X.IdealSheafData} (h : J.comap e.hom = I) (g : I.blowup ≅ J.blowup)
    (hg : g.hom ≫ J.blowupToBase = I.blowupToBase ≫ e.hom) :
    g = J.blowupIso e h := by
  apply Iso.ext
  subst I
  simpa [blowupIso] using J.eq_blowupMap e.hom hg

/-- The lifted isomorphism pulls back the target exceptional ideal to the source exceptional
ideal. -/
@[simp]
theorem comap_blowupIso_hom (J : Y.IdealSheafData) (e : X ≅ Y)
    {I : X.IdealSheafData} (h : J.comap e.hom = I) :
    (J.comap J.blowupToBase).comap (J.blowupIso e h).hom = I.comap I.blowupToBase := by
  subst I
  simpa [blowupIso] using J.comap_comap_blowupMap e.hom

/-- The identity lifts to the identity. -/
@[simp]
theorem blowupIso_refl (I : X.IdealSheafData) :
    I.blowupIso (Iso.refl X) (I.comap_id) = Iso.refl I.blowup := by
  symm
  apply I.blowupIso_unique
  simp

/-- Lifting two composable center-preserving isomorphisms commutes with composition. -/
@[simp]
theorem blowupIso_trans (K : Z.IdealSheafData) (e : X ≅ Y) (f : Y ≅ Z)
    {I : X.IdealSheafData} {J : Y.IdealSheafData}
    (he : J.comap e.hom = I) (hf : K.comap f.hom = J) :
    J.blowupIso e he ≪≫ K.blowupIso f hf =
      K.blowupIso (e ≪≫ f) (by rw [Iso.trans_hom, comap_comp, hf, he]) := by
  apply K.blowupIso_unique
  simp [Category.assoc]

/-- The inverse of a lift is the lift of the inverse. -/
@[simp]
theorem blowupIso_symm (J : Y.IdealSheafData) (e : X ≅ Y)
    {I : X.IdealSheafData} (h : J.comap e.hom = I) :
    (J.blowupIso e h).symm =
      I.blowupIso e.symm (by rw [← h, ← comap_comp, Iso.symm_hom, e.inv_hom_id, comap_id]) := by
  apply I.blowupIso_unique
  rw [← cancel_epi (J.blowupIso e h).hom]
  simp

end AlgebraicGeometry.Scheme.IdealSheafData
