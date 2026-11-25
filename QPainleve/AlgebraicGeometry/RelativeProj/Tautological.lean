/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.LineBundle.Basic
public import QPainleve.AlgebraicGeometry.RelativeProj.TwistingSheaf.GradedMap

import QPainleve.AlgebraicGeometry.Modules.Pullback.DirectImage

/-!
# Tautological evaluation of a line quotient

A line quotient induces a map from the projectivization of the quotient
line bundle to the original projective bundle. Under the identification of
the pushforward of the first twist with the quotient line bundle, the map
on degree-one sections is the original quotient. Pullback along the quotient
section recovers the quotient under the canonical identification of the
pulled-back twist with that line bundle.

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

/-- Pulling the tautological quotient back along the section defined by a line
quotient recovers the original quotient. The codomain is identified with the
quotient line bundle by the canonical pullback isomorphism. -/
@[reassoc (attr := simp)]
theorem relativeProjLineQuotient_relativeProjSectionOfQuotient (E : FixedRank X 1)
    {F : QuasicoherentSheaf X} (q : F ⟶ ℒ[E]) [Epi q.hom] :
    F.relativeProjLineQuotient (E.relativeProjSectionOfQuotient q)
        (E.relativeProjSectionOfQuotient_toBase q) ≫
      (E.relativeProjSectionOfQuotientPullbackTwistingSheafOneIso q).hom =
    (Scheme.Modules.pullbackId X).hom.app F.obj ≫ q.hom := by
  let B := 𝒜[F]
  let p := B.relativeProjToBase
  let hs : E.relativeProjSectionOfQuotient q ≫ p = 𝟙 X :=
    E.relativeProjSectionOfQuotient_toBase q
  let a := Scheme.Modules.pullbackPushforwardAdjunction p
  let M : X.Modules := F.obj
  let d : B.X 1 ≅ M := degreeOne[F]
  let σ := B.relativeProjToTwistingSheaf (rfl : ((1 : ℕ) : ℤ) = 1)
  have he : a.homEquiv _ _ ((Scheme.Modules.pullback p).map d.inv ≫ B.relativeProjEvaluation) =
      d.inv ≫ σ :=
    (a.homEquiv_naturality_left d.inv B.relativeProjEvaluation).trans
      (congrArg (d.inv ≫ ·) B.homEquiv_relativeProjEvaluation)
  have h := Scheme.Modules.homEquiv_comp_pushforwardToPullback_app hs
    ((Scheme.Modules.pullback p).map d.inv ≫ B.relativeProjEvaluation)
  rw [he] at h
  have h' : (d.inv ≫ σ) ≫ (Scheme.Modules.pushforwardToPullback hs).app
      (B.relativeProjTwistingSheaf 1) =
      (Scheme.Modules.pullbackId X).inv.app M ≫
        F.relativeProjLineQuotient (E.relativeProjSectionOfQuotient q) hs := by
    rw [F.relativeProjLineQuotient_def]
    exact h
  let i := (Scheme.Modules.pullbackId X).app M
  let e := E.relativeProjSectionOfQuotientPullbackTwistingSheafOneIso q
  let L : X.Modules := E.obj.obj
  let φ : M ⟶ L := q.hom
  apply (cancel_epi i.inv).mp
  calc
    _ = ((d.inv ≫ σ) ≫ (Scheme.Modules.pushforwardToPullback hs).app
          (B.relativeProjTwistingSheaf 1)) ≫ e.hom :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ e.hom) h'.symm)
    _ = φ := by
      simp only [Category.assoc, e]
      rw [E.pushforwardToPullback_app_relativeProjSectionOfQuotient q]
      have hq := E.relativeProjToTwistingSheaf_lineQuotient q
        (E.irrelevant_le_map_symmetricQuotient q)
      simp only [Iso.trans_hom, Iso.symm_hom] at hq
      exact hq
    _ = _ := (i.inv_hom_id_assoc φ).symm

end FiniteLocallyFreeSheaf.FixedRank

end TauCeti.AlgebraicGeometry
