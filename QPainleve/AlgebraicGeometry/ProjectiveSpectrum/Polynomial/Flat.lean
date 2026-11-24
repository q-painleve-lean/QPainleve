/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.Scheme.Normal

import QPainleve.AlgebraicGeometry.Morphisms.Finite
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Chart.Sections
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Integral
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Normal
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Flatness of finite morphisms to the projective plane

A finite morphism from a normal integral surface to the projective plane is flat.
The proof uses the surface case of miracle flatness, supplied by Tau Ceti's
`Scheme.Hom.flat_of_isDominant_of_locallyQuasiFinite_of_ringKrullDim_le_two`.
See [Stacks Project, Lemma 10.128.1](https://stacks.math.columbia.edu/tag/00R4).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open TauCeti TauCeti.AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "P[" k "]" => Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)
local notation "Q[" k ", " ι "]" => Proj (MvPolynomial.homogeneousSubmodule ι k)

namespace QPainleve

/-- An equivalence of coordinate indices with `Fin 3` identifies the corresponding
polynomial projective spectrum with the standard projective plane. -/
@[expose]
def polynomialPlaneIso {k ι : Type u} [Field k] (ε : ι ≃ Fin 3) : Q[k, ι] ≅ P[k] :=
  let b := Pi.basisFun k (Fin 3)
  (b.reindex ε.symm).polynomialProjIso ≪≫ b.polynomialProjIso.symm

end QPainleve

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X]

private theorem flat_of_isFinite_to_polynomialPlane (f : X ⟶ P[k]) [IsFinite f]
    (hX : 2 ≤ topologicalKrullDim X) : Flat f := by
  have : IsIntegral P[k] := Proj.isIntegral_polynomialProj
  let s := Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule (Fin 3) k)
  have : SmoothOfRelativeDimension 2 s := Proj.smoothOfRelativeDimension_polynomial k
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 s
  have hP := topologicalKrullDim_eq_of_smoothOfRelativeDimension s (n := 2)
  have : IsDominant f := f.isDominant_of_isFinite_of_topologicalKrullDim_le
    (hP ▸ WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top 2)) (hP.symm ▸ hX)
  have : IsRegular P[k] := IsRegular.of_smooth s
  have : IsLocallyNoetherian P[k] := LocallyOfFiniteType.isLocallyNoetherian s
  refine f.flat_of_isDominant_of_locallyQuasiFinite_of_ringKrullDim_le_two fun y ↦ ?_
  rw [ringKrullDim_stalk_eq_coheight]
  exact (coheight_le_topologicalKrullDim y).trans_eq hP

/-- A finite morphism from a normal integral surface to the projective plane is flat. -/
theorem flat_of_isFinite_to_projectivePlane {ι : Type u} (f : X ⟶ Q[k, ι]) [IsFinite f]
    (hX : 2 ≤ topologicalKrullDim X) (ε : ι ≃ Fin 3) : Flat f := by
  let e := QPainleve.polynomialPlaneIso (k := k) ε
  have : Flat (f ≫ e.hom) := flat_of_isFinite_to_polynomialPlane _ hX
  have hf : f = (f ≫ e.hom) ≫ e.inv := by simp
  exact hf ▸ inferInstance

end AlgebraicGeometry.Scheme.Hom
