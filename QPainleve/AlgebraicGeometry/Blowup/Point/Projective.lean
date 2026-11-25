/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Smooth
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.Point.Picard
import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.SmoothProjective

/-!
# Projectivity descends from a smooth point blowup

Castelnuovo contraction gives a projective target for the exceptional curve
of a projective point blowup. The uniqueness of the contraction identifies that
target with the specified base surface.
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry LineBundleClass QPainleve.BlowupTower

namespace AlgebraicGeometry.Scheme.IsProjectiveOver

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X] [IsNoetherian X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "I[" p "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ p)

/-- A smooth integral surface over an algebraically closed field is projective
if its blowup at a closed point is projective. -/
theorem of_pointBlowup (p : X) (hp : IsClosed ({p} : Set X)) :
    let : (I[p]).blowup.Over S := ⟨(I[p]).blowupToBase ≫ (X ↘ S)⟩
    (I[p]).blowup.IsProjectiveOver k → X.IsProjectiveOver k := by
  intro hOver hproj
  let := hOver
  let := hproj
  let B := (I[p]).blowup
  let E := (I[p]).comap (I[p]).blowupToBase
  let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsRegular X := IsRegular.of_smooth (X ↘ S)
  have hT : IsClosedPointTower X (.snoc .nil (I[p])) := .snoc .nil p hp rfl
  let : IsIntegral B := hT.isIntegral (X ↘ S)
  let : Smooth (B ↘ S) := by
    have hd := hT.smoothOfRelativeDimension (X ↘ S)
    rw [toBase_snoc, toBase_nil, Category.comp_id] at hd
    exact hd.smooth
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (X ↘ S) 2).mp
    inferInstance).2 p hp
  have hE : E.IsExceptionalCurveOfFirstKind :=
    IdealSheafData.isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hdim
  obtain ⟨Z, t, f, q, -, hZproj, hZdim, hfover, -, hq, -, hfiber, -, a, ha⟩ :=
    hE.exists_smooth_projective_contraction (k := k)
  let : Z.Over S := ⟨t⟩
  let := hZproj
  let : Smooth t := hZdim.smooth
  let : IsRegular Z := IsRegular.of_smooth t
  have hdim' := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq t 2).mp hZdim).2 q hq
  have hmatch : ((I[q]).comap (I[q]).blowupToBase).comap a.hom = E := by
    rw [← IdealSheafData.comap_comp, ha, hfiber]
  have hclass : pullback a.hom (I[q]).blowupExceptionalClass = (I[p]).blowupExceptionalClass := by
    rw [IdealSheafData.blowupExceptionalClass_def, IdealSheafData.blowupExceptionalClass_def,
      pullback_inv,
      (I[q]).isEffectiveCartier_comap_blowupToBase.pullback_mk_toInvertibleSheaf
        (hmatch.symm ▸ hE.isEffectiveCartier)]
    exact congrArg Inv.inv (mk_toInvertibleSheaf_congr _ hE.isEffectiveCartier hmatch)
  obtain ⟨g, ⟨hI, rfl⟩, -⟩ :=
    IdealSheafData.existsUnique_baseIso_of_pullback_blowupExceptionalClass_eq
      hp hq hdim hdim' a hclass
  have hg : (I[p]).blowupToBase ≫ g.hom = f :=
    (IdealSheafData.blowupIso_hom_blowupToBase g hI.symm).symm.trans ha
  have : Epi (I[p]).blowupToBase := by
    rw [X.ker_fromSpecResidueField_eq_vanishingIdeal p]
    exact IdealSheafData.epi_blowupToBase_point hp hdim
  have : g.hom.IsOver S := by
    constructor
    exact (cancel_epi (I[p]).blowupToBase).mp
      (by rw [← Category.assoc, hg]; exact hfover.comp_over)
  exact of_isClosedImmersion k g.hom

end AlgebraicGeometry.Scheme.IsProjectiveOver
