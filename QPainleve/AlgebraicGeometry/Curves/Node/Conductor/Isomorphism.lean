/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Blowup

import QPainleve.AlgebraicGeometry.Blowup.Isomorphism
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Etale

/-!
# Isomorphisms of nodal conductor squares

An isomorphism of relative curves carries the singular subscheme, the blowup along it,
and the two projections of the branch scheme to their counterparts. The induced maps
record the two branches even when they are on the same component.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TauCeti.AlgebraicGeometry

universe u

namespace CategoryTheory.Iso

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}} [X.Over (Spec (.of R))]
  [Y.Over (Spec (.of R))]
  [Flat (X ↘ Spec (.of R))] [LocallyOfFinitePresentation (X ↘ Spec (.of R))]
  [PureRelativeDimension 1 (X ↘ Spec (.of R))]
  [Flat (Y ↘ Spec (.of R))] [LocallyOfFinitePresentation (Y ↘ Spec (.of R))]
  [PureRelativeDimension 1 (Y ↘ Spec (.of R))]
  (e : X ≅ Y) [e.hom.IsOver (Spec (.of R))]

/-- An isomorphism of relative curves identifies their singular subschemes. -/
def singularLocusIso : (X.singularLocus R).subscheme ≅ (Y.singularLocus R).subscheme :=
  let h := Scheme.isPullback_singularLocus_subschemeι_of_etale (R := R) e.hom
  letI := h.isIso_snd_of_isIso
  asIso ((X.singularLocus R).subschemeMap (Y.singularLocus R) e.hom
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (Scheme.singularLocus_eq_comap_of_etale (R := R) e.hom).ge))

/-- The isomorphism of singular subschemes lies over the original curve isomorphism. -/
@[reassoc (attr := simp)]
theorem singularLocusIso_hom_subschemeι :
    (e.singularLocusIso (R := R)).hom ≫ (Y.singularLocus R).subschemeι =
      (X.singularLocus R).subschemeι ≫ e.hom := by
  simp [singularLocusIso]

/-- An isomorphism of relative curves identifies their blowups along the singular locus. -/
def singularLocusBlowupIso : (X.singularLocus R).blowup ≅ (Y.singularLocus R).blowup :=
  Scheme.IdealSheafData.blowupIso e (Scheme.singularLocus_eq_comap_of_etale (R := R) e.hom)

/-- The isomorphism of blowups lies over the original curve isomorphism. -/
@[reassoc (attr := simp)]
theorem singularLocusBlowupIso_hom_blowupToBase :
    (e.singularLocusBlowupIso (R := R)).hom ≫ (Y.singularLocus R).blowupToBase =
      (X.singularLocus R).blowupToBase ≫ e.hom := by
  simp [singularLocusBlowupIso]

/-- An isomorphism of relative curves identifies their branch schemes. -/
def branchSchemeIso : X.branchScheme R ≅ Y.branchScheme R :=
  (X.isPullback_branchScheme R).isoPullback ≪≫
    asIso (pullback.map _ _ _ _
      (e.singularLocusIso (R := R)).hom (e.singularLocusBlowupIso (R := R)).hom e.hom
      (e.singularLocusIso_hom_subschemeι (R := R)).symm
      (e.singularLocusBlowupIso_hom_blowupToBase (R := R)).symm) ≪≫
    (Y.isPullback_branchScheme R).isoPullback.symm

/-- The isomorphism of branch schemes covers the isomorphism of singular subschemes. -/
@[reassoc (attr := simp)]
theorem branchSchemeIso_hom_branchSchemeToSingularLocus :
    (e.branchSchemeIso (R := R)).hom ≫ Y.branchSchemeToSingularLocus R =
      X.branchSchemeToSingularLocus R ≫ (e.singularLocusIso (R := R)).hom := by
  simp [branchSchemeIso]

/-- The isomorphism of branch schemes covers the isomorphism of blowups. -/
@[reassoc (attr := simp)]
theorem branchSchemeIso_hom_branchSchemeToBlowup :
    (e.branchSchemeIso (R := R)).hom ≫ Y.branchSchemeToBlowup R =
      X.branchSchemeToBlowup R ≫ (e.singularLocusBlowupIso (R := R)).hom := by
  simp [branchSchemeIso]

local instance : (Iso.refl X).hom.IsOver (Spec (.of R)) := by
  rw [Iso.refl_hom]
  infer_instance

/-- The identity curve isomorphism induces the identity on the singular subscheme. -/
@[simp]
theorem singularLocusIso_refl :
    (Iso.refl X).singularLocusIso (R := R) = Iso.refl (X.singularLocus R).subscheme := by
  apply Iso.ext
  rw [← cancel_mono (X.singularLocus R).subschemeι]
  simp

/-- The identity curve isomorphism induces the identity on the blowup of the singular locus. -/
@[simp]
theorem singularLocusBlowupIso_refl :
    (Iso.refl X).singularLocusBlowupIso (R := R) = Iso.refl (X.singularLocus R).blowup := by
  simp [singularLocusBlowupIso]

/-- The identity curve isomorphism induces the identity on the branch scheme. -/
@[simp]
theorem branchSchemeIso_refl :
    (Iso.refl X).branchSchemeIso (R := R) = Iso.refl (X.branchScheme R) := by
  apply Iso.ext
  apply (X.isPullback_branchScheme R).hom_ext <;> simp

variable {Z : Scheme.{u}} [Z.Over (Spec (.of R))]
  [Flat (Z ↘ Spec (.of R))] [LocallyOfFinitePresentation (Z ↘ Spec (.of R))]
  [PureRelativeDimension 1 (Z ↘ Spec (.of R))] (f : Y ≅ Z) [f.hom.IsOver (Spec (.of R))]

local instance : (e ≪≫ f).hom.IsOver (Spec (.of R)) := by
  rw [Iso.trans_hom]
  infer_instance

/-- Induced isomorphisms of singular subschemes compose. -/
@[simp]
theorem singularLocusIso_trans :
    (e ≪≫ f).singularLocusIso (R := R) =
      e.singularLocusIso (R := R) ≪≫ f.singularLocusIso := by
  apply Iso.ext
  rw [← cancel_mono (Z.singularLocus R).subschemeι]
  simp

/-- Induced isomorphisms of blowups of singular subschemes compose. -/
@[simp]
theorem singularLocusBlowupIso_trans :
    (e ≪≫ f).singularLocusBlowupIso (R := R) =
      e.singularLocusBlowupIso (R := R) ≪≫ f.singularLocusBlowupIso := by
  unfold singularLocusBlowupIso
  rw [← Scheme.IdealSheafData.blowupIso_trans]

/-- Induced branch isomorphisms compose. -/
@[simp]
theorem branchSchemeIso_trans :
    (e ≪≫ f).branchSchemeIso (R := R) =
      e.branchSchemeIso (R := R) ≪≫ f.branchSchemeIso := by
  apply Iso.ext
  apply (Z.isPullback_branchScheme R).hom_ext <;> simp

end CategoryTheory.Iso
