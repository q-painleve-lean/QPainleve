/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.LineBundle.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
public import TauCeti.AlgebraicGeometry.VectorBundle.Quasicoherent

/-!
# Base change of projective line-quotient sections

The section of a projective bundle defined by a line quotient pulls back to the
section defined by the pulled-back quotient. The Cartesian comparison identifies
the two closed subschemes and their ideal sheaves, including over base changes to
nonreduced schemes.

The projectivizations use the quotient convention of
[Stacks, Section 27.21](https://stacks.math.columbia.edu/tag/01OA).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank

variable {X Y : Scheme.{u}}

local notation "ℒ[" L "]" =>
  Functor.obj (FiniteLocallyFreeSheaf.toQuasicoherent _) (ObjectProperty.FullSubcategory.obj L)
local notation "s[" L "," q "]" => relativeProjSectionOfQuotient L q

section CompatibleQuotients

variable (E : FixedRank X 1) (f : X ⟶ Y)
  (E' : FixedRank Y 1) {F : QuasicoherentSheaf X} {F' : QuasicoherentSheaf Y}

local notation "FP" => QuasicoherentSheaf.pullback f
local notation "π[" i "]" => QuasicoherentSheaf.projectivizationProjectionOfPullback f i

/-- Compatible identifications of pulled-back generators and quotient line
bundles exhibit the corresponding sections as a Cartesian square. -/
theorem isPullback_relativeProjSectionOfQuotient
    (i : F ≅ (FP).obj F') (j : ℒ[E] ≅ (FP).obj ℒ[E'])
    (q : F ⟶ ℒ[E]) (q' : F' ⟶ ℒ[E']) [Epi q.hom] [Epi q'.hom]
    (h : i.hom ≫ (FP).map q' = q ≫ (j).hom) :
    IsPullback s[E,q] f π[i] s[E',q'] := by
  refine IsPullback.of_right ?_
    (E.relativeProjSectionOfQuotient_comp_projectionOfPullback f E' i j q q' h)
    (QuasicoherentSheaf.isPullback_projectivizationProjectionOfPullback f i)
  simpa only [relativeProjSectionOfQuotient_toBase] using IsPullback.of_id_fst (f := f)

end CompatibleQuotients

variable (E' : FixedRank Y 1) (f : X ⟶ Y) {F' : QuasicoherentSheaf Y} (q' : F' ⟶ ℒ[E'])

local notation "FP" => QuasicoherentSheaf.pullback f

local notation "L" => Functor.obj (FixedRank.pullback f) E'
local notation "linePullbackIso" =>
  Iso.trans
    (eqToIso (congrArg (Functor.obj (FiniteLocallyFreeSheaf.toQuasicoherent X))
      (FixedRank.pullback_obj_obj f E')))
    (Iso.app (FiniteLocallyFreeSheaf.pullbackToQuasicoherentIso f)
      (ObjectProperty.FullSubcategory.obj E'))

/-- Pulling back a line quotient gives a map into the pulled-back line bundle,
viewed as a quasicoherent sheaf. -/
def pullbackLineQuotient : (FP).obj F' ⟶ ℒ[L] :=
  (FP).map q' ≫ (linePullbackIso).inv

/-- The comparison with the quasicoherent pullback recovers the pulled-back map. -/
@[reassoc]
theorem pullbackLineQuotient_comp_pullbackToQuasicoherentIso :
    E'.pullbackLineQuotient f q' ≫ (linePullbackIso).hom = (FP).map q' := by
  simp [pullbackLineQuotient]

instance epi_pullbackLineQuotient [Epi q'.hom] : Epi (E'.pullbackLineQuotient f q').hom := by
  let : (Scheme.Modules.pullback f).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (Scheme.Modules.pullbackPushforwardAdjunction f)
  let source := (QuasicoherentSheaf.pullbackCompιIso f).app F'
  let target := (QuasicoherentSheaf.pullbackCompιIso f).app ℒ[E']
  have hmap : ((FP).map q').hom =
      source.hom ≫ (Scheme.Modules.pullback f).map q'.hom ≫ target.inv := by
    rw [QuasicoherentSheaf.pullback_map_hom, ← QuasicoherentSheaf.pullbackCompιIso_hom_app,
      ← QuasicoherentSheaf.pullbackCompιIso_inv_app]
    rfl
  rw [pullbackLineQuotient, ObjectProperty.FullSubcategory.comp_hom, hmap]
  let : Epi (C := Y.Modules) q'.hom := ‹Epi q'.hom›
  let lineIso := (ObjectProperty.ι _).mapIso linePullbackIso
  exact epi_comp'
    (epi_comp' source.isIso_hom.epi_of_iso
      (epi_comp' (Functor.map_epi (Scheme.Modules.pullback f) q'.hom) target.isIso_inv.epi_of_iso))
    lineIso.isIso_inv.epi_of_iso

/-- The section associated to a pulled-back line quotient is the scheme-theoretic
base change of the original section. -/
theorem isPullback_relativeProjSectionOfQuotient_pullback [Epi q'.hom] :
    IsPullback s[L,E'.pullbackLineQuotient f q'] f
      (F'.relativeProjPullbackProjection f) s[E',q'] := by
  rw [← QuasicoherentSheaf.projectivizationProjectionOfPullback_refl]
  exact (L).isPullback_relativeProjSectionOfQuotient f E'
    (Iso.refl _) linePullbackIso _ q' (by
      simpa only [Iso.refl_hom, Category.id_comp] using
        (E'.pullbackLineQuotient_comp_pullbackToQuasicoherentIso f q').symm)

/-- The ideal sheaf of a line-quotient section pulls back to the ideal sheaf of
the section of the pulled-back quotient. -/
@[simp]
theorem ker_relativeProjSectionOfQuotient_pullback [Epi q'.hom] :
    s[L,E'.pullbackLineQuotient f q'].ker =
      s[E',q'].ker.comap (F'.relativeProjPullbackProjection f) :=
  ker_eq_comap_of_isPullback _ (E'.isPullback_relativeProjSectionOfQuotient_pullback f q')

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank
