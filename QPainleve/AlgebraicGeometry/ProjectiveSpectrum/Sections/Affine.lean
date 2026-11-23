/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# Affineness of projective morphisms defined by sections

The morphism to projective space defined by a covering family of line bundle
sections is affine exactly when their nonvanishing opens are affine.
-/

public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A morphism to projective space defined by covering sections is affine exactly when
the nonvanishing open of each section is affine. -/
theorem isAffineHom_toProjectiveSpace_iff {ι : Type u}
    (M : X.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]
    (f : X ⟶ Spec (.of R)) (s : ι → Γ(M, ⊤))
    (h : (⨆ i, M.nonvanishingLocus (s i)) = ⊤) :
    IsAffineHom (M.toProjectiveSpace f s h) ↔
      ∀ i, IsAffineOpen (M.nonvanishingLocus (s i)) := by
  let U (i : ι) := Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)
  have hU : (⨆ i, U i) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _ (MvPolynomial.irrelevant_eq_span_X ι R).le
  have hAffine (i : ι) : IsAffineOpen (U i) :=
    Proj.isAffineOpen_basicOpen _ _
      ((MvPolynomial.mem_homogeneousSubmodule ..).mpr (MvPolynomial.isHomogeneous_X R i)) one_pos
  have hpre (i : ι) : (M.toProjectiveSpace f s h) ⁻¹ᵁ U i = M.nonvanishingLocus (s i) :=
    M.toProjectiveSpace_preimage_basicOpen f s h i
  constructor
  · intro _ i
    rw [← hpre i]
    exact (hAffine i).preimage _
  · intro ha
    apply isAffineHom_of_forall_exists_isAffineOpen
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU.symm ▸ Opens.mem_top x)
    exact ⟨U i, hi, hAffine i, (hpre i).symm ▸ ha i⟩

end AlgebraicGeometry.Scheme.Modules
