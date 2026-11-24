/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Blowup
public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.NormalModel
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.CompletedStalk
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Numerical
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Smooth projective contractions of exceptional curves

An exceptional curve of the first kind on a smooth integral projective surface over
an algebraically closed field can be contracted to a point on a smooth projective
surface. The contraction exhibits the original surface as the blowup of that point.

The argument uses the completed-local-ring and blowup comparisons in the
[Stacks Project, Lemma 54.16.4](https://stacks.math.columbia.edu/tag/0C2L).
The projective case is [Lemma 54.16.9(1)](https://stacks.math.columbia.edu/tag/0C2N).
-/

public section

open CategoryTheory Limits TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

variable {k : Type u} [Field k] {X : Scheme.{u}} {E : X.IdealSheafData}

attribute [local instance] MvPolynomial.gradedAlgebra

variable [IsAlgClosed k] [X.Over (Spec (.of k))] [IsIntegral X]
  [X.IsProjectiveOver k] [Smooth (X ↘ Spec (.of k))]

/-- Castelnuovo contraction of an exceptional curve on a smooth integral projective scheme
over an algebraically closed field. The target is a smooth integral projective surface.
Pullback identifies functions on every target open with those on its inverse image. The
exceptional curve is the scheme-theoretic fiber, and the contraction is the blowup of the point. -/
theorem exists_smooth_projective_contraction (hE : E.IsExceptionalCurveOfFirstKind) :
    ∃ (Z : Scheme.{u}) (t : Z ⟶ Spec (.of k)) (f : X ⟶ Z) (p : Z),
      letI : Z.Over (Spec (.of k)) := ⟨t⟩
      IsIntegral Z ∧ Z.IsProjectiveOver k ∧ SmoothOfRelativeDimension 2 t ∧
        f.IsOver (Spec (.of k)) ∧ IsModification f ∧ IsClosed ({p} : Set Z) ∧ f.centre = {p} ∧
        (Z.fromSpecResidueField p).ker.comap f = E ∧ (∀ U : Z.Opens, IsIso (f.app U)) ∧
        ∃ e : X ≅ (Z.fromSpecResidueField p).ker.blowup,
          e.hom ≫ (Z.fromSpecResidueField p).ker.blowupToBase = f := by
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  obtain ⟨ι, _, Z, j, f, p, hZ, _, _, hs, hmod, hp, _, hF, hc, hΓ, hproj⟩ :=
    hE.exists_normal_model_collapsing_exceptional_curve k
  let t := j ≫ Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule ι k)
  let : Z.Over (Spec (.of k)) := ⟨t⟩
  have : f.IsOver (Spec (.of k)) := ⟨hs⟩
  have : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ Spec (.of k))
  have : LocallyOfFiniteType t := inferInstanceAs (LocallyOfFiniteType (Z ↘ Spec (.of k)))
  have hU : ((Z.fromSpecResidueField p).ker.support).compl ≤ f.isoLocus := by
    rw [← SetLike.coe_subset_coe, Closeds.coe_compl,
      support_ker_fromSpecResidueField_of_isClosed hp, ← hc, Scheme.Hom.compl_centre]
  obtain ⟨e, he⟩ := hE.exists_iso_projectiveLine_over (k := k)
  obtain ⟨hr, hd⟩ := hE.isRegularLocalRing_and_ringKrullDim_eq_of_contraction e f hp hF hU
    (fun V ↦ hΓ V.val)
  have : IsRegular Z := f.isRegular_of_isRegularLocalRing_of_mem_centre fun y hy ↦ by
    rw [hc, Set.mem_singleton_iff] at hy
    exact hy ▸ hr
  have : Smooth t := t.smooth_of_isRegularLocalRing_stalk
  have hdim : SmoothOfRelativeDimension 2 t := smoothOfRelativeDimension_of_topologicalKrullDim_eq t
    ((ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed t hp).symm.trans hd)
  let I := (Z.fromSpecResidueField p).ker
  have := hE.isIso_blowupLift_of_regular_contraction_point f hc hd hF
  exact ⟨Z, t, f, p, hZ, hproj, hdim, inferInstance, hmod, hp, hc, hF, hΓ,
    asIso (I.blowupLift f (hF.symm ▸ hE.isEffectiveCartier)),
    I.blowupLift_blowupToBase f _⟩

end AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
