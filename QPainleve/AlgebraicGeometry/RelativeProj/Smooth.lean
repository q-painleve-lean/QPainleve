/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import QPainleve.AlgebraicGeometry.RelativeProj.ProjectiveBundle

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Smooth

/-!
# Smoothness of projective bundles

The relative projective spectrum of the symmetric algebra of a rank-`d + 1`
vector bundle is smooth of relative dimension `d` over the base.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projective bundle of a rank-`d + 1` vector bundle is smooth of relative dimension
`d` over its base. -/
theorem smoothOfRelativeDimension_relativeProjToBase {S : Scheme.{u}} {d : ℕ}
    (E : FixedRank S (d + 1)) :
    let F := (FiniteLocallyFreeSheaf.toQuasicoherent S).obj E.obj
    let A := ((gradedSymmetricAlgebra S).obj F).obj
    SmoothOfRelativeDimension d A.relativeProjToBase := by
  let F := (FiniteLocallyFreeSheaf.toQuasicoherent S).obj E.obj
  let A := ((gradedSymmetricAlgebra S).obj F).obj
  let hlocal : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{u} d) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @SmoothOfRelativeDimension.{u} d)
      (Q := RingHom.Locally (@RingHom.IsStandardSmoothOfRelativeDimension d))
  let := hlocal
  let : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{u} d) :=
    hlocal.toRespects
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := @SmoothOfRelativeDimension d) ?_
  intro x
  obtain ⟨U, hx, _, j, hj, _⟩ :=
    E.exists_relativeProjPolynomialChart (W := ⊤) (x := x) trivial
  let R := Γ(S, U.toOpens)
  let b := Pi.basisFun R (Fin (d + 1))
  let c := b.reindex (Equiv.ulift.symm : Fin (d + 1) ≃ ULift.{u} (Fin (d + 1)))
  let P := MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (d + 1))) R
  let p := A.relativeProjToBase
  let e := hj.isoIsPullback _ _ (isPullback_morphismRestrict p U.toOpens)
  refine ⟨U.toOpens, hx, ?_⟩
  have hπ : SmoothOfRelativeDimension (0 + d)
      (c.polynomialProjIso.hom ≫ SymmetricAlgebra.projToSpec R (Fin (d + 1) → R)) := by
    let := b.smoothOfRelativeDimension_projToSpec
    infer_instance
  rw [c.polynomialProjIso_hom_over, Nat.zero_add] at hπ
  let : SmoothOfRelativeDimension d (Proj.toSpecCoeff P) := hπ
  have hchart : SmoothOfRelativeDimension (d + 0)
      (Proj.toSpecCoeff P ≫ U.property.isoSpec.inv) := inferInstance
  rw [Nat.add_zero, ← hj.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict p U.toOpens)]
    at hchart
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension d) e.hom
    (p ∣_ U.toOpens)).mp hchart

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank
