/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.BaseChange
public import QPainleve.AlgebraicGeometry.RelativeProj.Isomorphism
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.Basic

import QPainleve.AlgebraicGeometry.Modules.GradedAlgebra.SymmetricAlgebraPullback

/-!
# Projectivization under base change

An identification of a quasicoherent sheaf with the pullback of another gives
a Cartesian comparison of their projectivizations. It commutes with the maps
induced by quotients in the convention of
[Stacks, Section 27.21](https://stacks.math.columbia.edu/tag/01OA).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open CategoryTheory.CommMon

universe u

namespace TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section Projection

variable {A : GradedQuasicoherentAlgebra X} {B : GradedQuasicoherentAlgebra Y}
  (i : A ≅ (pullback f).obj B)

private def relativeProjMapIsoOfPullback :
    A.obj.relativeProj ≅ ((pullback f).obj B).obj.relativeProj :=
  relativeProjMapIso ((ObjectProperty.ι _).mapIso i.symm)

/-- The base-change projection, computed using an identification of the source algebra
with the pulled-back algebra. -/
def relativeProjProjectionOfPullback : A.obj.relativeProj ⟶ B.obj.relativeProj :=
  (relativeProjMapIsoOfPullback f i).hom ≫ B.relativeProjBaseChange f

/-- An identification with the pulled-back algebra gives a Cartesian square on relative Proj. -/
theorem isPullback_relativeProjProjectionOfPullback :
    IsPullback A.obj.relativeProjToBase (relativeProjProjectionOfPullback f i)
      f B.obj.relativeProjToBase := by
  refine (B.isPullback_relativeProjBaseChange f).of_iso (relativeProjMapIsoOfPullback f i).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [relativeProjMapIsoOfPullback]
  · simp [relativeProjProjectionOfPullback]
  · simp
  · simp

/-- The projection commutes with the structure maps of relative Proj. -/
@[reassoc (attr := simp)]
theorem relativeProjProjectionOfPullback_toBase :
    relativeProjProjectionOfPullback f i ≫ B.obj.relativeProjToBase =
      A.obj.relativeProjToBase ≫ f :=
  (isPullback_relativeProjProjectionOfPullback f i).w.symm

variable {A' : GradedQuasicoherentAlgebra X} {B' : GradedQuasicoherentAlgebra Y}
  (i' : A' ≅ (pullback f).obj B') (g : A ⟶ A') (h : B ⟶ B')

/-- Compatible identifications with pullback algebras give a commutative square
of relative projective spectra over the base morphism. -/
@[reassoc]
theorem relativeProjProjectionOfPullback_naturality
    (hc : i.hom ≫ (pullback f).map h = g ≫ i'.hom)
    (hg : ∀ U : X.Opens, IsAffineOpen U →
      HomogeneousIdeal.irrelevant (A'.obj.gradedSectionsGrading U) ≤
        (HomogeneousIdeal.irrelevant (A.obj.gradedSectionsGrading U)).map
          (gradedSectionsGradedHom g.hom U))
    (hh : ∀ U : Y.Opens, IsAffineOpen U →
      HomogeneousIdeal.irrelevant (B'.obj.gradedSectionsGrading U) ≤
        (HomogeneousIdeal.irrelevant (B.obj.gradedSectionsGrading U)).map
          (gradedSectionsGradedHom h.hom U)) :
    relativeProjMap g.hom hg ≫ relativeProjProjectionOfPullback f i =
      relativeProjProjectionOfPullback f i' ≫ relativeProjMap h.hom hh := by
  let ι := ObjectProperty.ι (isGradedQuasicoherentAlgebra X)
  let gi : ((pullback f).obj B).obj ≅ A.obj := ι.mapIso i.symm
  let gi' : ((pullback f).obj B').obj ≅ A'.obj := ι.mapIso i'.symm
  have hh' : ((pullback f).map h).hom = gi.hom ≫ g.hom ≫ gi'.inv := by
    rw [← (Iso.inv_comp_eq i).mpr hc.symm]
    simp [gi, gi', ι]
  have hhPull (U : X.Opens) (hU : IsAffineOpen U) :
      HomogeneousIdeal.irrelevant (((pullback f).obj B').obj.gradedSectionsGrading U) ≤
        (HomogeneousIdeal.irrelevant (((pullback f).obj B).obj.gradedSectionsGrading U)).map
          (gradedSectionsGradedHom ((pullback f).map h).hom U) := by
    rw [hh', gradedSectionsGradedHom_comp, gradedSectionsGradedHom_comp]
    exact HomogeneousIdeal.irrelevant_le_map_comp
      (irrelevant_le_map_gradedSectionsGradedHom_of_iso gi U)
      (HomogeneousIdeal.irrelevant_le_map_comp (hg U hU)
        (irrelevant_le_map_gradedSectionsGradedHom_of_iso gi'.symm U))
  have hmaps : relativeProjMap g.hom hg ≫ (relativeProjMapIso gi).hom =
      (relativeProjMapIso gi').hom ≫ relativeProjMap ((pullback f).map h).hom hhPull := by
    rw [relativeProjMapIso_hom, relativeProjMapIso_hom, ← relativeProjMap_comp,
      ← relativeProjMap_comp]
    · congr 1
      rw [hh']
      simp only [Category.assoc, gi'.inv_hom_id, Category.comp_id]
    · intro U hU
      rw [gradedSectionsGradedHom_comp]
      exact HomogeneousIdeal.irrelevant_le_map_comp (hhPull U hU)
        (irrelevant_le_map_gradedSectionsGradedHom_of_iso gi' U)
    · intro U hU
      rw [gradedSectionsGradedHom_comp]
      exact HomogeneousIdeal.irrelevant_le_map_comp
        (irrelevant_le_map_gradedSectionsGradedHom_of_iso gi U) (hg U hU)
  simp only [relativeProjProjectionOfPullback, relativeProjMapIsoOfPullback]
  rw [← Category.assoc, hmaps, Category.assoc,
    relativeProjBaseChange_naturality f h hh hhPull, Category.assoc]

end Projection

section Iso

variable (e : X ≅ Y) {A : GradedQuasicoherentAlgebra X} {B : GradedQuasicoherentAlgebra Y}
  (i : A ≅ (pullback e.hom).obj B)

/-- A graded algebra identified with the pullback of another along an isomorphism
of bases induces an isomorphism of their relative projective spectra. -/
def relativeProjIsoOfPullback : A.obj.relativeProj ≅ B.obj.relativeProj := by
  letI := (isPullback_relativeProjProjectionOfPullback e.hom i).isIso_snd_of_isIso
  exact asIso (relativeProjProjectionOfPullback e.hom i)

/-- The forward map is the projective map of the algebra comparison followed
by the base-change comparison. -/
@[reassoc]
theorem relativeProjIsoOfPullback_hom :
    (relativeProjIsoOfPullback e i).hom =
      (relativeProjMapIso (A := ((pullback e.hom).obj B).obj) (B := A.obj)
        ((ObjectProperty.ι _).mapIso i.symm)).hom ≫
        B.relativeProjBaseChange e.hom := (rfl)

/-- The projective isomorphism induced by the pullback comparison covers the
chosen isomorphism of bases. -/
@[reassoc (attr := simp)]
theorem relativeProjIsoOfPullback_hom_toBase :
    (relativeProjIsoOfPullback e i).hom ≫ B.obj.relativeProjToBase =
      A.obj.relativeProjToBase ≫ e.hom :=
  relativeProjProjectionOfPullback_toBase e.hom i

end Iso

end TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra

namespace TauCeti.AlgebraicGeometry.QuasicoherentSheaf

variable {X Y : Scheme.{u}}

local notation "A[" E "]" => Functor.obj (gradedSymmetricAlgebra _) E

section Projection

variable (f : X ⟶ Y) {E : QuasicoherentSheaf X} {F : QuasicoherentSheaf Y}

private def gradedSymmetricAlgebraIsoOfPullback (i : E ≅ (pullback f).obj F) :
    A[E] ≅ (GradedQuasicoherentAlgebra.pullback f).obj A[F] :=
  (gradedSymmetricAlgebra X).mapIso i ≪≫ pullbackGradedSymmetricAlgebraIso f F

/-- The projection from the projectivization of a sheaf identified with a pullback
to the projectivization of the original sheaf. -/
def projectivizationProjectionOfPullback (i : E ≅ (pullback f).obj F) :
    A[E].obj.relativeProj ⟶ A[F].obj.relativeProj :=
  GradedQuasicoherentAlgebra.relativeProjProjectionOfPullback f
    (gradedSymmetricAlgebraIsoOfPullback f i)

/-- The projection is a Cartesian comparison over the chosen map of bases. -/
theorem isPullback_projectivizationProjectionOfPullback (i : E ≅ (pullback f).obj F) :
    IsPullback A[E].obj.relativeProjToBase (projectivizationProjectionOfPullback f i)
      f A[F].obj.relativeProjToBase :=
  GradedQuasicoherentAlgebra.isPullback_relativeProjProjectionOfPullback f _

/-- The projection commutes with the projective bundle structure maps. -/
@[reassoc (attr := simp)]
theorem projectivizationProjectionOfPullback_toBase (i : E ≅ (pullback f).obj F) :
    projectivizationProjectionOfPullback f i ≫ A[F].obj.relativeProjToBase =
      A[E].obj.relativeProjToBase ≫ f :=
  (isPullback_projectivizationProjectionOfPullback f i).w.symm

variable {E' : QuasicoherentSheaf X} {F' : QuasicoherentSheaf Y}

local notation "φ[" X "," q "]" =>
  InducedCategory.Hom.hom (CategoryTheory.Functor.map (gradedSymmetricAlgebra X) q)

/-- Compatible pullback identifications of generators preserve the maps on
projectivizations, provided the given maps are defined everywhere. -/
@[reassoc]
theorem projectivizationProjectionOfPullback_naturality
    (i : E ≅ (pullback f).obj F) (i' : E' ≅ (pullback f).obj F')
    (q : E ⟶ E') (q' : F ⟶ F')
    (hc : i.hom ≫ (pullback f).map q' = q ≫ i'.hom)
    (hq : ∀ U : X.Opens, IsAffineOpen U →
      HomogeneousIdeal.irrelevant (A[E'].obj.gradedSectionsGrading U) ≤
        (HomogeneousIdeal.irrelevant (A[E].obj.gradedSectionsGrading U)).map
          (gradedSectionsGradedHom φ[X,q] U))
    (hq' : ∀ U : Y.Opens, IsAffineOpen U →
      HomogeneousIdeal.irrelevant (A[F'].obj.gradedSectionsGrading U) ≤
        (HomogeneousIdeal.irrelevant (A[F].obj.gradedSectionsGrading U)).map
          (gradedSectionsGradedHom φ[Y,q'] U)) :
    relativeProjMap φ[X,q] hq ≫ projectivizationProjectionOfPullback f i =
      projectivizationProjectionOfPullback f i' ≫ relativeProjMap φ[Y,q'] hq' := by
  apply GradedQuasicoherentAlgebra.relativeProjProjectionOfPullback_naturality f _ _
    ((gradedSymmetricAlgebra X).map q) ((gradedSymmetricAlgebra Y).map q') _ hq hq'
  have hn := (pullbackGradedSymmetricAlgebraNatIso f).hom.naturality q'
  simp only [Functor.comp_map, ← Iso.app_hom, pullbackGradedSymmetricAlgebraNatIso_app] at hn
  simp only [gradedSymmetricAlgebraIsoOfPullback, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, ← hn, ← Functor.map_comp_assoc, hc]

end Projection

section CanonicalProjection

variable (F : QuasicoherentSheaf Y) (f : X ⟶ Y)

/-- The projection from the projectivization of the pulled-back quasicoherent
sheaf to that of the original sheaf. -/
def relativeProjPullbackProjection :
    A[(pullback f).obj F].obj.relativeProj ⟶ A[F].obj.relativeProj :=
  projectivizationProjectionOfPullback f (Iso.refl _)

/-- The base change of a projectivization is the projectivization of the
pulled-back sheaf. -/
theorem isPullback_relativeProjPullbackProjection :
    IsPullback A[(pullback f).obj F].obj.relativeProjToBase
      (F.relativeProjPullbackProjection f) f A[F].obj.relativeProjToBase :=
  isPullback_projectivizationProjectionOfPullback f (Iso.refl _)

/-- The projection over a change of base commutes with the structure maps. -/
@[reassoc (attr := simp)]
theorem relativeProjPullbackProjection_toBase :
    F.relativeProjPullbackProjection f ≫ A[F].obj.relativeProjToBase =
      A[(pullback f).obj F].obj.relativeProjToBase ≫ f :=
  (F.isPullback_relativeProjPullbackProjection f).w.symm

/-- The identity identification gives the canonical base-change projection. -/
@[simp]
theorem projectivizationProjectionOfPullback_refl :
    projectivizationProjectionOfPullback f (Iso.refl ((pullback f).obj F)) =
      F.relativeProjPullbackProjection f :=
  (rfl)

end CanonicalProjection

variable {E : QuasicoherentSheaf X} {F : QuasicoherentSheaf Y}

/-- Projectivizing a quasicoherent sheaf identified with a pullback along a
base isomorphism gives an isomorphism of the projective spectra. -/
def projectivizationIsoOfPullback (e : X ≅ Y) (i : E ≅ (pullback e.hom).obj F) :
    A[E].obj.relativeProj ≅ A[F].obj.relativeProj :=
  GradedQuasicoherentAlgebra.relativeProjIsoOfPullback e
    (gradedSymmetricAlgebraIsoOfPullback e.hom i)

/-- The projectivization comparison covers the given base isomorphism. -/
@[reassoc (attr := simp)]
theorem projectivizationIsoOfPullback_hom_toBase (e : X ≅ Y) (i : E ≅ (pullback e.hom).obj F) :
    (projectivizationIsoOfPullback e i).hom ≫ A[F].obj.relativeProjToBase =
      A[E].obj.relativeProjToBase ≫ e.hom :=
  GradedQuasicoherentAlgebra.relativeProjIsoOfPullback_hom_toBase e _

/-- The isomorphism over a base isomorphism has the Cartesian projection as its
forward morphism. -/
theorem projectivizationIsoOfPullback_hom (e : X ≅ Y) (i : E ≅ (pullback e.hom).obj F) :
    (projectivizationIsoOfPullback e i).hom = projectivizationProjectionOfPullback e.hom i :=
  (rfl)

end TauCeti.AlgebraicGeometry.QuasicoherentSheaf
