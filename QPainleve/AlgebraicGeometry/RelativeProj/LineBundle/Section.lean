/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.Tautological

import QPainleve.AlgebraicGeometry.RelativeProj.TwistingSheaf.MorphismExt

/-!
# Recovering a section of a projective bundle from its line quotient

A section of a projective bundle is recovered from the restriction of the tautological
quotient to that section. This is the section case of the quotient description of
projective bundles in [Stacks, Section 27.21][Stacks].

[Stacks]: https://stacks.math.columbia.edu/tag/01OA
-/

public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank

open GradedQuasicoherentAlgebra

variable {X : Scheme.{u}} {F : QuasicoherentSheaf X}

local notation "A" =>
  ObjectProperty.FullSubcategory.obj (Functor.obj (gradedSymmetricAlgebra X) F)
local notation "T" => CommMon.relativeProjTwistingSheaf A 1
local notation "p" => CommMon.relativeProjToBase A
local notation "L[" E "]" =>
  Functor.obj (FiniteLocallyFreeSheaf.toQuasicoherent X) (ObjectProperty.FullSubcategory.obj E)

private theorem relativeProjLineQuotient_eq_evaluationAlong
    (s : X ⟶ (A).relativeProj) (hs : s ≫ p = 𝟙 X) :
    let d : (A).X 1 ≅ F.obj :=
      eqToIso (degree_obj_obj ((gradedSymmetricAlgebra X).obj F) 1).symm ≪≫
        (ObjectProperty.ι _).mapIso ((gradedSymmetricAlgebraDegreeOneIso X).app F)
    F.relativeProjLineQuotient s hs =
      (Scheme.Modules.pullback (𝟙 X)).map d.inv ≫ (A).relativeProjEvaluationAlong s hs := by
  intro d
  rw [F.relativeProjLineQuotient_def s hs, (A).relativeProjEvaluationAlong_def,
    Functor.map_comp]
  -- Move the degree-one identification through the two pullback comparisons.
  have hcomp :
      (Scheme.Modules.pullback (s ≫ p)).map d.inv ≫
          (Scheme.Modules.pullbackComp s p).inv.app ((A).X 1) =
        (Scheme.Modules.pullbackComp s p).inv.app F.obj ≫
          (Scheme.Modules.pullback s).map ((Scheme.Modules.pullback p).map d.inv) :=
    (Scheme.Modules.pullbackComp s p).inv.naturality d.inv
  have hcong := (Scheme.Modules.pullbackCongr hs).inv.naturality d.inv
  erw [Category.assoc, ← reassoc_of% hcomp, ← reassoc_of% hcong]

/-- A section whose tautological quotient is identified with a given line quotient is
the section defined by that quotient. -/
theorem relativeProjSectionOfQuotient_eq_of_relativeProjLineQuotient
    (E : FixedRank X 1) (q : F ⟶ L[E]) [Epi q.hom]
    (s : X ⟶ (A).relativeProj) (hs : s ≫ p = 𝟙 X)
    (e : (Scheme.Modules.pullback s).obj T ≅ E.obj.obj)
    (he : F.relativeProjLineQuotient s hs ≫ e.hom =
      (Scheme.Modules.pullbackId X).hom.app F.obj ≫ q.hom) :
    E.relativeProjSectionOfQuotient q = s := by
  let t := E.relativeProjSectionOfQuotient q
  let ht := E.relativeProjSectionOfQuotient_toBase q
  let i := E.relativeProjSectionOfQuotientPullbackTwistingSheafOneIso q
  have h := (E.relativeProjLineQuotient_relativeProjSectionOfQuotient q).trans he.symm
  rw [relativeProjLineQuotient_eq_evaluationAlong t ht,
    relativeProjLineQuotient_eq_evaluationAlong s hs] at h
  let d : (A).X 1 ≅ F.obj :=
    eqToIso (degree_obj_obj ((gradedSymmetricAlgebra X).obj F) 1).symm ≪≫
      (ObjectProperty.ι _).mapIso ((gradedSymmetricAlgebraDegreeOneIso X).app F)
  let v := (Scheme.Modules.pullback (𝟙 X)).mapIso d
  have : IsIso v.inv := v.isIso_inv
  simp only [Category.assoc] at h
  have h' := (cancel_epi v.inv).mp h
  exact (A).relativeProj_hom_ext_of_evaluation t ht
    (isGeneratedInDegreeOne_gradedSymmetricAlgebra F) hs (i ≪≫ e.symm)
    (by simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] using congrArg (· ≫ e.inv) h')

/-- A section is induced by a line quotient with any target line bundle identified
with the pullback of the tautological twist along that section. -/
theorem exists_relativeProjLineQuotient_of_section (E : FixedRank X 1)
    (s : X ⟶ (A).relativeProj) (hs : s ≫ p = 𝟙 X)
    (e : (Scheme.Modules.pullback s).obj T ≅ E.obj.obj) :
    ∃ q : F ⟶ L[E], ∃ hq : Epi q.hom,
      letI := hq
      E.relativeProjSectionOfQuotient q = s := by
  let φ := F.relativeProjLineQuotient s hs
  let i := (Scheme.Modules.pullbackId X).app F.obj
  let q : F ⟶ L[E] := ObjectProperty.homMk (C := X.Modules) (i.inv ≫ φ ≫ e.hom)
  have : Epi φ := F.epi_relativeProjLineQuotient s hs
  have hq : Epi q.hom := by
    change Epi (i.inv ≫ φ ≫ e.hom)
    infer_instance
  refine ⟨q, hq, E.relativeProjSectionOfQuotient_eq_of_relativeProjLineQuotient q s hs e ?_⟩
  exact (i.hom_inv_id_assoc (φ ≫ e.hom)).symm

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank
