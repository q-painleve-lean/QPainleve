/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Scaling

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.GlobalSections
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.CoordinateMap

/-!
# Polynomial comparison for the projective line

The standard basis compares the two-variable polynomial Proj with the native
projective line. A graded map rescaling the variables corresponds to projective
scaling and base change under this comparison.
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Proj CategoryTheory Limits
open TauCeti.AlgebraicGeometry.projectiveLine

universe u

namespace QPainleve

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

private abbrev CoordinateIndex := ULift.{u} (Fin 2)

local notation "𝒫[" A "]" => MvPolynomial.homogeneousSubmodule CoordinateIndex A

/-- The standard basis for the homogeneous coordinates of the projective line,
with the variable indices lifted to the coefficient ring's universe. -/
abbrev projectiveLineCoordinateBasis (A : Type u) [CommRing A] :=
  (Pi.basisFun A (Fin 2)).reindex (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2))

private theorem fromPolynomialGradedHom_X (i : ULift.{u} (Fin 2)) :
    (projectiveLineCoordinateBasis R).fromPolynomialGradedHom (MvPolynomial.X i) =
      coord R i.down := by
  simp only [Module.Basis.fromPolynomialGradedHom_apply, SymmetricAlgebra.equivMvPolynomial_symm_X,
    projectiveLineCoordinateBasis, Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.ulift_apply,
    Pi.basisFun_apply]
  have hrev : i.down.rev ≠ i.down := by
    rcases i with ⟨i⟩
    fin_cases i <;> decide
  rw [ι_eq_smul_coord_add_smul_coord R i.down]
  simp [Pi.single_eq_of_ne hrev]

private theorem fromPolynomialGradedHom_C (r : R) :
    (projectiveLineCoordinateBasis R).fromPolynomialGradedHom (MvPolynomial.C r) =
      algebraMap R (SymmetricAlgebra R (Fin 2 → R)) r := by
  rw [Module.Basis.fromPolynomialGradedHom_apply, ← MvPolynomial.algebraMap_eq,
    AlgEquiv.commutes]

/-- Under the polynomial presentation of the projective line, a graded map
scaling the first coordinate by a unit induces projective scaling followed by
base change. The common unit factor on both coordinates cancels in Proj. -/
theorem map_comp_coordinateComparison {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B]
    (f : MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) A →+*ᵍ
      MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) B)
    (hf : HomogeneousIdeal.irrelevant _ ≤ (HomogeneousIdeal.irrelevant _).map f)
    (v w : Bˣ)
    (hC : ∀ r, f (MvPolynomial.C r) = MvPolynomial.C (algebraMap A B r))
    (hX : ∀ i, f (MvPolynomial.X i) =
      (w : B) • (if i.down = 0 then (v : B) else 1) • MvPolynomial.X i) :
    (projectiveLineCoordinateBasis B).polynomialProjIso.inv ≫ Proj.map f hf =
      (scalingBy B v).hom ≫ baseChangeProjection A B ≫
        (projectiveLineCoordinateBasis A).polynomialProjIso.inv := by
  have : IsSeparated (terminal.from (Proj 𝒫[A])) := by
    rw [← terminal.comp_from (toSpecCoeff 𝒫[A])]
    infer_instance
  refine TauCeti.ext_of_isSchemeTheoreticallyDominant (polynomialChartι B 1)
    (terminal.from _) (terminal.hom_ext _ _) ?_
  rw [← polynomialPoint_X]
  simp only [← Category.assoc, polynomialPoint_comp_scalingBy,
    polynomialPoint_comp_baseChangeProjection]
  rw [polynomialPoint_eq_fromGlobalSections, polynomialPoint_eq_fromGlobalSections,
    Module.Basis.polynomialProjIso_inv, Module.Basis.polynomialProjIso_inv,
    fromOfGlobalSections_map, fromOfGlobalSections_map, fromOfGlobalSections_map]
  let e := (Scheme.ΓSpecIso (.of (Polynomial B))).inv.hom
  let w' := w.map (e.comp Polynomial.C).toMonoidHom
  let p := e.comp (pointCoordinates A (Polynomial.C.comp (algebraMap A B)) 1
    (Polynomial.C (v : B) * Polynomial.X))
  let q := e.comp (pointCoordinates B Polynomial.C 1 Polynomial.X)
  let P := p.comp (projectiveLineCoordinateBasis A).fromPolynomialGradedHom.toRingHom
  let Q := (q.comp (projectiveLineCoordinateBasis B).fromPolynomialGradedHom.toRingHom).comp
    f.toRingHom
  apply (fromOfGlobalSections_eq_of_X_unit_rescaling P Q w' ?_ ?_ _ _).symm
  · apply RingHom.ext
    intro r
    simp only [P, Q, p, q, RingHom.comp_apply, GradedRingHom.coe_toRingHom, hC,
      fromPolynomialGradedHom_C, pointCoordinates_algebraMap]
  · intro i
    simp only [P, Q, p, q, RingHom.comp_apply, GradedRingHom.coe_toRingHom, hX,
      Algebra.smul_def, MvPolynomial.algebraMap_eq, map_mul, fromPolynomialGradedHom_C,
      pointCoordinates_algebraMap, fromPolynomialGradedHom_X, w', Units.coe_map]
    obtain ⟨i⟩ := i
    have hA := pointCoordinates_coord_rev A (Polynomial.C.comp (algebraMap A B)) 1
      (Polynomial.C (v : B) * Polynomial.X)
    have hB := pointCoordinates_coord_rev B Polynomial.C 1 Polynomial.X
    have hrev : (1 : Fin 2).rev = 0 := rfl
    rw [hrev] at hA hB
    fin_cases i <;> simp [hA, hB, map_mul]

end QPainleve
