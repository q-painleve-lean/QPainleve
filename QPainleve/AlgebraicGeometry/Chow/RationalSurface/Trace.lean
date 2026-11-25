/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Canonical.Cohomology
public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Trace

import QPainleve.AlgebraicGeometry.Modules.Differentials.Cohomology

/-!
# Top traces on smooth projective rational surfaces

A common resolution with the projective plane transports its coordinate residue
to a trace on the second cohomology of the canonical bundle. The trace is a
linear equivalence. Its normalization uses the given resolution and the
standard coordinates of the plane.

The transport uses `IsClosedPointTower.cohomologyCanonicalBundleLinearEquiv`
and the normalization uses `Proj.polynomialPlaneCanonicalTrace`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules TauCeti.SymmetricAlgebra

universe u

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 3) k
local notation "Ppoly" => Proj 𝒜
local notation "ω[" X "]" => canonicalBundle k X 2
local notation "Ω₂" => Functor.obj (SheafOfModules.exteriorPower (Scheme.sheaf Ppoly) 2)
  (Scheme.relativeDifferentials k Ppoly)

attribute [local instance] MvPolynomial.gradedAlgebra Proj.planeOver Proj.planeSmooth

variable {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

section CommonResolution

variable [PerfectField k]
  {m n : ℕ} {V W : Scheme.{u}} {T : BlowupTower X m V}
  {U : BlowupTower (Proj (homogeneousSubmodule k (Fin 3 → k))) n W}
  (hT : IsClosedPointTower X T) (hU : IsClosedPointTower _ U) (e : W ≅ V)
  (he : e.hom ≫ T.toBase ≫ X ↘ Spec (.of k) =
    U.toBase ≫ Proj (homogeneousSubmodule k (Fin 3 → k)) ↘ Spec (.of k))

/-- Compare canonical cohomology with the polynomial projective plane through a
specified common resolution and the standard basis of the plane. -/
def cohomologyCanonicalBundleLinearEquivPolynomialPlane (q : ℕ) :
    Cohomology ω[X].obj q ≃ₗ[k] Cohomology Ω₂ q := by
  let b := Pi.basisFun k (Fin 3)
  let eP := b.polynomialProjIso
  let : eP.hom.IsOver S := ⟨b.polynomialProjIso_hom_over⟩
  let eω : ω[Ppoly].obj ≅ Ω₂ := eqToIso (by rw [canonicalBundle_obj, differentialForms_def])
  exact (hT.cohomologyCanonicalBundleLinearEquivOfCommonResolution k hU e he q).trans
    ((eP.hom.cohomologyCanonicalBundleLinearEquivOfIsIso k 2 q).trans
      (Scheme.Modules.cohomologyBaseLinearEquivOfIso k eω q))

/-- A common resolution with the standard projective plane transports its coordinate
trace to the second cohomology of the canonical bundle of the other surface. -/
def canonicalTraceOfCommonResolution : Cohomology ω[X].obj 2 ≃ₗ[k] k :=
  (cohomologyCanonicalBundleLinearEquivPolynomialPlane k hT hU e he 2).trans
    (Proj.polynomialPlaneCanonicalTrace k)

/-- The trace of a canonical class is its coordinate residue after transport to the plane. -/
theorem canonicalTraceOfCommonResolution_apply (x : Cohomology ω[X].obj 2) :
    canonicalTraceOfCommonResolution k hT hU e he x =
      Proj.polynomialPlaneCanonicalTrace k
        (cohomologyCanonicalBundleLinearEquivPolynomialPlane k hT hU e he 2 x) :=
  (rfl)

/-- The transported class of the reciprocal coordinate product is normalized to trace one. -/
theorem canonicalTraceOfCommonResolution_inverseCoordinateProduct :
    let x := Proj.polynomialPlaneCechClass k (Proj.twistingSheaf 𝒜 (-3))
      (Proj.polynomialPlaneInverseCoordinateProduct k)
    let y := (Scheme.Modules.cohomologyBaseLinearEquivOfIso k
      (Proj.differentialFormsTwoIsoTwistingSheaf k) 2).symm x
    canonicalTraceOfCommonResolution k hT hU e he
      ((cohomologyCanonicalBundleLinearEquivPolynomialPlane k hT hU e he 2).symm y) = 1 := by
  simp only [canonicalTraceOfCommonResolution_apply, LinearEquiv.apply_symm_apply,
    Proj.polynomialPlaneCanonicalTrace_inverseCoordinateProduct]

end CommonResolution

variable (X) [IsAlgClosed k] [X.IsProjectiveOver k] [Scheme.IsRationalOver (X ↘ Spec (.of k))]

/-- A smooth projective rational surface over an algebraically closed field has a
top-degree trace obtained from the residue trace on the projective plane. -/
theorem nonempty_canonicalTrace_of_isRationalOver : Nonempty (Cohomology ω[X].obj 2 ≃ₗ[k] k) := by
  obtain ⟨_, _, _, _, _, _, e, hT, hU, he⟩ :=
    X.exists_common_pointBlowup_resolution_projectivePlane k
  exact ⟨canonicalTraceOfCommonResolution k hT hU e he⟩

/-- The second cohomology of the canonical bundle on a smooth projective rational
surface over an algebraically closed field is one-dimensional. -/
theorem finrank_cohomology_two_canonicalBundle_of_isRationalOver :
    Module.finrank k (Cohomology ω[X].obj 2) = 1 := by
  obtain ⟨tr⟩ := X.nonempty_canonicalTrace_of_isRationalOver k
  exact tr.finrank_eq.trans (Module.finrank_self k)

end AlgebraicGeometry.Scheme
