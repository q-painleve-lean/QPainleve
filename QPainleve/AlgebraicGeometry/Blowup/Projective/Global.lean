/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Projective.TwistedIdeal
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.LineBundle.GlobalGeneration
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Embedding
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.FiniteType
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample

/-!
# Projectivity of blowups of projective schemes

A blowup of a projective scheme in a center of finite type is projective over the
same coefficient ring. An ample twist of the ideal sheaf admits finite global
generators, giving a closed graph in the product of the base with projective space.
Noetherian coefficient rings make the finite-type hypothesis on the ideal automatic.
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.SymmetricAlgebra

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} (I : X.IdealSheafData) (R : Type u) [CommRing R]
  [X.Over (Spec (.of R))] [X.IsProjectiveOver R]

/-- The blowup of a projective scheme in an ideal sheaf of finite type is projective
over the original coefficient ring. -/
theorem isProjectiveOver_blowup [I.sheaf.IsFiniteType] :
    let : I.blowup.Over (Spec (.of R)) := ⟨I.blowupToBase ≫ (X ↘ Spec (.of R))⟩
    I.blowup.IsProjectiveOver R := by
  obtain ⟨ι, hι, j, hj, hjR⟩ := X.exists_isClosedImmersion_polynomial_of_isProjectiveOver R
  let j' := j ≫ Proj.polynomialProjectiveEmbedding R ι
  have : IsAffineHom j' :=
    inferInstanceAs (IsAffineHom (j ≫ Proj.polynomialProjectiveEmbedding R ι))
  have : Module.Finite R (ι →₀ R) := Module.Finite.finsupp
  let 𝒜 := homogeneousSubmodule R (ι →₀ R)
  let H : InvertibleSheaf (Proj 𝒜) := ⟨Proj.twistingSheaf 𝒜 1, inferInstance⟩
  have hH : (LineBundleClass.mk H).IsAmple :=
    TauCeti.SymmetricAlgebra.isAmple_twistingSheaf R (ι →₀ R) Nat.one_pos
  let L := (InvertibleSheaf.pullback j').obj H
  have hL : (LineBundleClass.mk L).IsAmple := LineBundleClass.pullback_mk j' H ▸
    hH.pullback_of_isAffineHom j'
  have hgen := Scheme.Modules.eventually_exists_generatingSections_tensor_tensorPow_of_isAmple
    I.sheaf L hL
  obtain ⟨n, G, hG⟩ := hgen.exists
  have : Finite G.I := hG.finite
  obtain ⟨m, hm, hclosed⟩ := I.exists_blowupToProjectiveSpace_of_generatingSections
    (X ↘ Spec (.of R)) (L.tensorPow n) G
  exact I.isProjectiveOver_blowup_of_closed_graph _ j hjR m hm hclosed

/-- Over a Noetherian coefficient ring, every blowup of a projective scheme is projective. -/
theorem isProjectiveOver_blowup_of_isNoetherianRing [IsNoetherianRing R] :
    let : I.blowup.Over (Spec (.of R)) := ⟨I.blowupToBase ≫ (X ↘ Spec (.of R))⟩
    I.blowup.IsProjectiveOver R := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of R))
  have : I.sheaf.IsFiniteType := Scheme.Modules.isFiniteType_of_finite_sections I.sheaf
    fun U hU ↦ by
      have := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
      let φ : Γ(I.sheaf, U) →ₗ[Γ(X, U)] Γ(X, U) :=
        ((Scheme.Modules.sectionsFunctor U).map I.sheafι).hom
      exact Module.Finite.of_injective φ (I.sheafι_app_injective U)
  exact I.isProjectiveOver_blowup R

end AlgebraicGeometry.Scheme.IdealSheafData
