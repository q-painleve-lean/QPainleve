/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.LineBundle.Basic
public import QPainleve.AlgebraicGeometry.RelativeProj.TwistingSheaf.GradedMap

/-!
# Tautological evaluation of a line quotient

A line quotient induces a map from the projectivization of the quotient
line bundle to the original projective bundle. Under the identification of
the pushforward of the first twist with the quotient line bundle, the map
on degree-one sections is the original quotient.

See [Stacks Project, Section 27.21](https://stacks.math.columbia.edu/tag/01OA).
-/

public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CommMon

universe u

namespace TauCeti.AlgebraicGeometry

open GradedQuasicoherentAlgebra

variable {X : Scheme.{u}}

local notation "𝒜[" F "]" =>
  ObjectProperty.FullSubcategory.obj (Functor.obj (gradedSymmetricAlgebra X) F)
local notation "φ[" q "]" =>
  InducedCategory.Hom.hom (CategoryTheory.Functor.map (gradedSymmetricAlgebra X) q)
local notation "ℒ[" E "]" =>
  Functor.obj (FiniteLocallyFreeSheaf.toQuasicoherent X) (ObjectProperty.FullSubcategory.obj E)

local macro "degreeOne[" F:term "]" : term =>
  `(eqToIso (degree_obj_obj ((gradedSymmetricAlgebra X).obj $F) 1).symm ≪≫
    (ObjectProperty.ι _).mapIso ((gradedSymmetricAlgebraDegreeOneIso X).app $F))

private theorem gradedSymmetricAlgebra_degreeOne_inv_naturality
    {F G : QuasicoherentSheaf X} (q : F ⟶ G) :
    degreeOne[F].inv ≫ φ[q].hom.hom 1 = q.hom ≫ degreeOne[G].inv := by
  have h := congrArg (fun f ↦ f.hom) ((gradedSymmetricAlgebraDegreeOneIso X).inv.naturality q)
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    Functor.id_map, Functor.comp_map, degree_map_hom] at h
  have h' := congrArg (· ≫ eqToHom (degree_obj_obj ((gradedSymmetricAlgebra X).obj G) 1)) h.symm
  erw [Category.assoc, Category.assoc, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id] at h'
  exact h'

namespace FiniteLocallyFreeSheaf.FixedRank

/-- After the projective map of a line quotient, the map from the original sheaf
to the pushforward of the first twist is the given quotient. The identification
of the pushforward with the line bundle is induced by degree-one evaluation. -/
theorem relativeProjToTwistingSheaf_lineQuotient (E : FixedRank X 1)
    {F : QuasicoherentSheaf X} (q : F ⟶ ℒ[E])
    (hq : ∀ U : X.Opens, IsAffineOpen U →
      HomogeneousIdeal.irrelevant (𝒜[ℒ[E]].gradedSectionsGrading U) ≤
        (HomogeneousIdeal.irrelevant (𝒜[F].gradedSectionsGrading U)).map
          (gradedSectionsGradedHom φ[q] U)) :
    let A := 𝒜[ℒ[E]]
    let B := 𝒜[F]
    let f := B.relativeProjToBase
    let g := relativeProjMap φ[q] hq
    let a := Scheme.Modules.pullbackPushforwardAdjunction g
    let τ := a.homEquiv _ _ (relativeProjTwistingSheafMap φ[q] hq 1)
    let T := A.relativeProjTwistingSheaf 1
    let σ := A.relativeProjToTwistingSheaf (show ((1 : ℕ) : ℤ) = 1 from rfl)
    let e := (asIso σ).symm ≪≫ degreeOne[ℒ[E]]
    degreeOne[F].inv ≫
      (B.relativeProjToTwistingSheaf (show ((1 : ℕ) : ℤ) = 1 from rfl) ≫
        (Scheme.Modules.pushforward f).map τ ≫
        (Scheme.Modules.pushforwardComp g f).hom.app T ≫
        (Scheme.Modules.pushforwardCongr (relativeProjMap_relativeProjToBase φ[q] hq)).hom.app T) ≫
      e.hom = q.hom := by
  intro A B f g a τ T σ e
  have h := relativeProjToTwistingSheaf_naturality φ[q] hq (d := 1) (n := 1) rfl
  refine (congrArg (fun m ↦ degreeOne[F].inv ≫ m ≫ e.hom) h).trans ?_
  have hq' := gradedSymmetricAlgebra_degreeOne_inv_naturality q
  calc
    _ = (degreeOne[F].inv ≫ φ[q].hom.hom 1) ≫ σ ≫ e.hom :=
      (Category.assoc _ _ _).symm
    _ = q.hom ≫ degreeOne[ℒ[E]].inv ≫ σ ≫ e.hom :=
      congrArg (· ≫ σ ≫ e.hom) hq'
    _ = _ := by
      let d := degreeOne[ℒ[E]]
      have hs := (asIso σ).hom_inv_id_assoc d.hom
      have hd := d.inv_hom_id
      exact (congrArg (fun m ↦ q.hom ≫ d.inv ≫ m) hs).trans
        ((congrArg (q.hom ≫ ·) hd).trans (Category.comp_id _))

end FiniteLocallyFreeSheaf.FixedRank

end TauCeti.AlgebraicGeometry
