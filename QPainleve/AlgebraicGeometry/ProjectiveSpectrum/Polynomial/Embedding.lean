/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Basic
import TauCeti.Algebra.MvPolynomial.Eval
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Polynomial embeddings of projective schemes

A finite module is a quotient of a finite free module. On symmetric algebras
and their projective spectra, the quotient gives a closed immersion, which
allows a projective scheme to be embedded into polynomial projective space.
-/

public section

open CategoryTheory
open TauCeti.SymmetricAlgebra

namespace AlgebraicGeometry.Scheme

universe u

variable (R : Type u) [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A scheme projective over a ring admits a closed immersion over that ring into the
projective spectrum of a polynomial ring on finitely many variables. -/
theorem exists_isClosedImmersion_polynomial_of_isProjectiveOver
    (X : Scheme.{u}) [X.Over (Spec (.of R))] [X.IsProjectiveOver R] :
    ∃ (ι : Type u) (_ : Finite ι)
      (j : X ⟶ Proj (MvPolynomial.homogeneousSubmodule ι R)),
      IsClosedImmersion j ∧ j ≫ Proj.toSpecCoeff _ = X ↘ Spec (.of R) := by
  obtain ⟨M, _, _, _, i, hi, hiR⟩ := IsProjectiveOver.exists_isClosedImmersion (R := R) (X := X)
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let ι := ULift.{u} (Fin n)
  let t : ι → M := s ∘ ULift.down
  have ht : Submodule.span R (Set.range t) = ⊤ := by
    dsimp only [t]
    rw [Set.range_comp, ULift.down_surjective.range_eq, Set.image_univ]
    exact hs
  let a := _root_.SymmetricAlgebra.ι R M ∘ t
  let φ : MvPolynomial.homogeneousSubmodule ι R →ₐᵍ[R] homogeneousSubmodule R M :=
    ⟨MvPolynomial.aeval a, fun hp ↦
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp).aeval_mem
        (fun k ↦ ι_mem_homogeneousSubmodule R M (t k))⟩
  have hφ : Function.Surjective φ.toGradedRingHom := by
    -- Surjectivity is computed in the underlying algebra via the generating subalgebra.
    change Function.Surjective (MvPolynomial.aeval a)
    exact MvPolynomial.aeval_surjective_iff_adjoin_range_eq_top.mpr
      (_root_.SymmetricAlgebra.adjoin_range_ι_comp_eq_top_of_span_eq_top t ht)
  let hφirr := HomogeneousIdeal.irrelevant_le_map_of_surjective _ hφ
  let j := Proj.map φ.toGradedRingHom hφirr
  have : IsClosedImmersion j := Proj.isClosedImmersion_map _ _ hφ
  have hj : j ≫ Proj.toSpecCoeff _ = projToSpec R M := by
    rw [projToSpec_def, ← Proj.toSpecCoeff_def]
    apply Proj.map_toSpecCoeff
    intro r
    apply Subtype.ext
    simp [φ, SetLike.GradeZero.coe_algebraMap]
  refine ⟨ι, inferInstance, i ≫ j, inferInstance, ?_⟩
  rw [Category.assoc, hj]
  exact hiR.comp_over

end AlgebraicGeometry.Scheme
