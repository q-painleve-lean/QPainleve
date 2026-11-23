/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.ZeroDivisor
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.RationalMap
import QPainleve.AlgebraicGeometry.CartierDivisor.Nonvanishing
import QPainleve.AlgebraicGeometry.CartierDivisor.SectionDivision
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.Comparison
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Extending projective presentations with Cartier base ideals

When the coordinate sections of a rational map to projective space have an effective
Cartier base ideal, dividing them by this ideal gives a generating family in the
Cartier twist. Its projective morphism extends the original presentation. This is
the fixed-factor cancellation used in elimination of indeterminacy, as in
[Hacking, §7.2 and Proposition 7.3](https://paulhacking.github.io/surfaces.pdf#page=37).
-/

public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

variable {X : Scheme.{u}} [IsIntegral X] (L : InvertibleSheaf X)

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R ι : Type u} [CommRing R]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R

/-- A rational projective presentation with effective Cartier base ideal extends to a
unique morphism over the coefficient ring. -/
theorem exists_toProjectiveSpace_of_isEffectiveCartier_iSup_zeroIdeal
    (f : X ⟶ Spec (.of R)) (s : ι → Γ(L.obj, ⊤))
    (i : ι) (hi : Dense (L.obj.nonvanishingLocus (s i) : Set X))
    (hI : (⨆ j, L.zeroIdeal (s j)).IsEffectiveCartier) :
    ∃! g : X ⟶ Proj 𝒜, g ≫ Proj.toSpecCoeff 𝒜 = f ∧
      g.toRationalMap = (L.obj.partialMapToProjectiveSpace f s i hi).toRationalMap := by
  let K := hI.toInvertibleSheaf.tensorProduct L
  obtain ⟨t, ht, htbase⟩ := L.exists_idealTwist_sections_iSup_zeroIdeal_eq_top s hI rfl
  have hcover : (⨆ j, K.obj.nonvanishingLocus (t j)) = ⊤ :=
    (K.iSup_zeroIdeal_eq_top_iff t).mp htbase
  have hsupp : (L.zeroIdeal (s i)).support = (K.zeroIdeal (t i)).support ⊔
      (⨆ j, L.zeroIdeal (s j)).support := by
    rw [← ht i, zeroIdeal_idealTwistInclusion, Scheme.IdealSheafData.support_mul]
  have hd : Dense (K.obj.nonvanishingLocus (t i) : Set X) := hi.mono (by
    rw [← L.compl_support_zeroIdeal, ← K.compl_support_zeroIdeal, hsupp]
    exact (Closeds.complOrderIso X).monotone le_sup_left)
  let g := K.obj.toProjectiveSpace f t hcover
  have hg : g ≫ Proj.toSpecCoeff 𝒜 = f := K.obj.toProjectiveSpace_toSpecCoeff f t hcover
  have he : g.toRationalMap = (L.obj.partialMapToProjectiveSpace f s i hi).toRationalMap :=
    (K.obj.toRationalMap_partialMapToProjectiveSpace f t hcover i hd).symm.trans
      (toRationalMap_partialMapToProjectiveSpace_eq_of_hom f t s
        (L.idealTwistInclusion hI) ht i hd hi)
  refine ⟨g, ⟨hg, he⟩, fun g' ⟨hg', he'⟩ ↦ ?_⟩
  have hr := Scheme.PartialMap.toRationalMap_eq_iff.mp (he'.trans he.symm)
  obtain ⟨U, hU, _, _, hcomp⟩ := hr
  have := AlgebraicGeometry.Opens.isDominant_ι (X := X) (U := U) hU
  apply ext_of_isDominant_of_isSeparated (Proj.toSpecCoeff 𝒜) (hg'.trans hg.symm) U.ι
  simp only [Scheme.PartialMap.restrict_hom, Scheme.Hom.toPartialMap_hom] at hcomp
  calc
    U.ι ≫ g' = X.homOfLE (le_top : U ≤ ⊤) ≫ X.topIso.hom ≫ g' := by
      rw [Scheme.topIso_hom, Scheme.homOfLE_ι_assoc]
    _ = X.homOfLE (le_top : U ≤ ⊤) ≫ X.topIso.hom ≫ g := hcomp
    _ = _ := by rw [Scheme.topIso_hom, Scheme.homOfLE_ι_assoc]

end TauCeti.AlgebraicGeometry.InvertibleSheaf
