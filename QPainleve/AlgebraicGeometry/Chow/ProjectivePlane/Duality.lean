/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Duality

import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.AlgebraicGeometry.Cohomology.TracePairing.Isomorphism
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-!
# Top-degree trace duality on the symmetric-algebra projective plane

The coordinate isomorphism with polynomial Proj carries its normalized trace
pairing to a perfect pairing on the projective plane defined by the symmetric
algebra. This is the plane used as the base of point-blowup markings and
common resolutions. Perfection holds for every nonzero canonical trace.

The comparison uses `Module.Basis.polynomialProjIso` and
`AlgebraicGeometry.Proj.isPerfPair_polynomialPlaneCanonicalPairing`.
-/

public noncomputable section

open CategoryTheory TauCeti TauCeti.SymmetricAlgebra QPainleve
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra planeOver planeSmooth

variable (k : Type u) [Field k] [Infinite k]

local notation "P" => Proj (homogeneousSubmodule k (Fin 3 → k))
local notation "P₀" => Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)
local notation "Ω₂" => Functor.obj (SheafOfModules.exteriorPower (Scheme.sheaf P₀) 2)
  (Scheme.relativeDifferentials k P₀)

/-- The second cohomology of every line bundle on the symmetric-algebra projective
plane pairs perfectly with its dual canonical sections for any nonzero trace. -/
theorem isPerfPair_cohomologyTracePairing_projectivePlane (L : InvertibleSheaf P)
    (tr : Cohomology (canonicalBundle k P 2).obj 2 →ₗ[k] k) (htr : tr ≠ 0) :
    (cohomologyTracePairing (M := L.obj) k 2 tr).IsPerfPair := by
  let K := canonicalBundle k P 2
  let b := Pi.basisFun k (Fin 3)
  let e := b.polynomialProjIso
  have : e.hom.IsOver (Spec (.of k)) := ⟨by
    rw [SymmetricAlgebra.over_eq_projToSpec]
    exact b.polynomialProjIso_hom_over⟩
  let M := (InvertibleSheaf.pullback e.hom).obj L
  let a : (Scheme.Modules.pullback e.hom).obj L.obj ≅ M.obj :=
    eqToIso (InvertibleSheaf.pullback_obj_obj e.hom L).symm
  let c : (Scheme.Modules.pullback e.hom).obj K.obj ≅ Ω₂ :=
    (eqToIso (InvertibleSheaf.pullback_obj_obj e.hom K).symm) ≪≫
      asIso (topDifferentialFormsMap k e.hom 2) ≪≫
      eqToIso (by rw [canonicalBundle_obj, differentialForms_def])
  let E := e.hom.cohomologyBaseLinearEquivOfPullbackIso k c 2
  let t := (E.symm.trans (polynomialPlaneCanonicalTrace k)).toLinearMap
  have hp : (cohomologyTracePairing (M := M.obj) k 2 (t.comp E.toLinearMap)).IsPerfPair := by
    have h : t.comp E.toLinearMap = (polynomialPlaneCanonicalTrace k).toLinearMap := by
      ext x
      simp [t]
    have heq : cohomologyTracePairing (M := M.obj) k 2 (t.comp E.toLinearMap) =
        polynomialPlaneCanonicalPairing k M := by
      ext x s
      simp only [h, cohomologyTracePairing_apply, polynomialPlaneCanonicalPairing_apply,
        LinearEquiv.coe_coe]
    exact heq.symm ▸ isPerfPair_polynomialPlaneCanonicalPairing k M
  have := (e.hom.isPerfPair_cohomologyTracePairing_iff_of_isIso k (a := a) c 2 t).mp hp
  have := moduleFinite_cohomology_of_isProjectiveOver k L.obj 2
  have hdim : topologicalKrullDim P ≤ (2 : ℕ) :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension
      (P ↘ Spec (.of k)) (n := 2)).le
  exact (L.isPerfPair_cohomologyTracePairing_iff_finrank k K hdim tr htr).mpr
    (Module.finrank_of_isPerfPair (cohomologyTracePairing (M := L.obj) k 2 t))

end AlgebraicGeometry.Proj
