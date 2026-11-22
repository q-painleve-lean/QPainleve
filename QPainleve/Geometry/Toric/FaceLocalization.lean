/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import TauCeti.Geometry.Toric.Algebraic.FaceLocalization
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Dominance of affine toric face morphisms

The face restriction on coordinate rings sends each monomial to the same integral
character in the larger dual semigroup. This makes Tau Ceti's face morphism dominant
and supplies the affine step in showing that the torus is dense in a toric scheme.
-/

public section

open AlgebraicGeometry Multiplicative

namespace TauCeti.Toric

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The affine toric scheme of a face maps dominantly to that of the ambient cone. -/
theorem isDominant_faceAffineToricSchemeMap (hi : IsIntegralLattice i)
    {τ σ : PointedCone ℝ V} (h : τ.IsFaceOf σ) :
    IsDominant (faceAffineToricSchemeMap hi h) := by
  rw [faceAffineToricSchemeMap_def]
  refine ⟨RingHom.denseRange_comap_of_injective _ ?_⟩
  let inclusion := AddSubmonoid.inclusion (dualSemigroup_anti hi h.le)
  have he :
      faceAffineCoordinateRingMap hi h =
        MonoidAlgebra.mapDomainAlgHom ℂ ℂ inclusion.toMultiplicative := by
    apply MonoidAlgebra.algHom_ext
    · intro m
      rw [← ofAdd_toAdd m, faceAffineCoordinateRingMap_single]
      simp [inclusion, AddSubmonoid.inclusion]
    · ext
  rw [he]
  apply MonoidAlgebra.mapDomain_injective
  exact ofAdd.injective.comp <| (AddSubmonoid.inclusion_injective _).comp toAdd.injective

end TauCeti.Toric
