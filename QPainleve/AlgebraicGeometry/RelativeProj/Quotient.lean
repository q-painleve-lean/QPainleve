/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.BaseChange
public import QPainleve.AlgebraicGeometry.RelativeProj.Isomorphism
public import QPainleve.AlgebraicGeometry.RelativeProj.LineBundle

import QPainleve.AlgebraicGeometry.Modules.GradedAlgebra.SymmetricAlgebraPullback
import QPainleve.AlgebraicGeometry.RelativeProj.TwistingSheaf.Comparison

/-!
# Morphisms to projective bundles from line quotients

A line quotient of a pulled-back quasicoherent sheaf gives a morphism to the
relative projectivization of the original sheaf. Its graph over the base is the
closed section defined by the quotient on the pulled-back projective bundle,
and it pulls the tautological twist back to the quotient line bundle.
We use the quotient convention of [Stacks, Section 27.21][stacks-01OA].

[stacks-01OA]: https://stacks.math.columbia.edu/tag/01OA
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace TauCeti.AlgebraicGeometry

variable {X Y : Scheme.{u}}

local notation "Sym[" G "]" => Functor.obj (gradedSymmetricAlgebra _) G
local notation "PB[" f "," A "]" => Functor.obj (GradedQuasicoherentAlgebra.pullback f) A
local notation "F⟮" f "," F "⟯" => Functor.obj (QuasicoherentSheaf.pullback f) F

namespace QuasicoherentSheaf

variable (F : QuasicoherentSheaf Y) (f : X ⟶ Y)

private def projPullbackIso :
    Sym[F⟮f,F⟯].obj.relativeProj ≅
      PB[f,Sym[F]].obj.relativeProj :=
  CommMon.relativeProjMapIso ((ObjectProperty.ι _).mapIso
    (pullbackGradedSymmetricAlgebraIso f F).symm)

/-- The base-change projection from the projectivization of the pulled-back
quasicoherent sheaf to that of the original sheaf. -/
def relativeProjPullbackProjection :
    Sym[F⟮f,F⟯].obj.relativeProj ⟶ Sym[F].obj.relativeProj :=
  (projPullbackIso F f).hom ≫ Sym[F].relativeProjBaseChange f

/-- Projectivization of the pulled-back sheaf is the scheme-theoretic base change
of the original projectivization. -/
theorem isPullback_relativeProjPullbackProjection :
    IsPullback Sym[F⟮f,F⟯].obj.relativeProjToBase (F.relativeProjPullbackProjection f)
      f Sym[F].obj.relativeProjToBase := by
  refine (Sym[F].isPullback_relativeProjBaseChange f).of_iso (projPullbackIso F f).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [projPullbackIso]
  · simp [relativeProjPullbackProjection]
  · simp
  · simp

/-- The projectivization's base-change projection commutes with the structure maps. -/
@[reassoc (attr := simp)]
theorem relativeProjPullbackProjection_toBase :
    F.relativeProjPullbackProjection f ≫ Sym[F].obj.relativeProjToBase =
      Sym[F⟮f,F⟯].obj.relativeProjToBase ≫ f :=
  (F.isPullback_relativeProjPullbackProjection f).w.symm

/-- The projectivization's base-change projection pulls back every integral twist
to the corresponding twist of the projectivization of the pulled-back sheaf. -/
def relativeProjPullbackProjectionTwistingSheafIso (n : ℤ) :
    (Scheme.Modules.pullback (F.relativeProjPullbackProjection f)).obj
      (Sym[F].obj.relativeProjTwistingSheaf n) ≅
        Sym[F⟮f,F⟯].obj.relativeProjTwistingSheaf n := by
  let G := F⟮f,F⟯
  let A := Sym[F]
  let s := (pullbackGradedSymmetricAlgebraIso f F).symm
  let e : PB[f,A].obj ≅ Sym[G].obj := (ObjectProperty.ι _).mapIso s
  let hφ (U : X.Opens) (_ : IsAffineOpen U) :=
    CommMon.irrelevant_le_map_gradedSectionsGradedHom_of_iso e U
  let μ := A.relativeProjBaseChangeTwistingSheafMap f n
  have : IsIso μ :=
    A.isIso_relativeProjBaseChangeTwistingSheafMap f n
      (isGeneratedInDegreeOne_gradedSymmetricAlgebra F)
  have : Epi (e.hom.hom.hom 1) := by
    exact IsIso.epi_of_iso (f := s.hom.hom.hom.hom 1)
  let ν := CommMon.relativeProjTwistingSheafMap e.hom hφ n
  have : IsIso ν := CommMon.isIso_relativeProjTwistingSheafMap_of_epi_one e.hom hφ n
    (isGeneratedInDegreeOne_gradedSymmetricAlgebra G)
  rw [relativeProjPullbackProjection, projPullbackIso, CommMon.relativeProjMapIso_hom]
  let j := CommMon.relativeProjMap e.hom hφ
  exact (Scheme.Modules.pullbackComp j (A.relativeProjBaseChange f)).symm.app _ ≪≫
    (Scheme.Modules.pullback j).mapIso (asIso μ) ≪≫ asIso ν

end QuasicoherentSheaf

namespace FiniteLocallyFreeSheaf.FixedRank

variable (E : FixedRank X 1) (f : X ⟶ Y) {F : QuasicoherentSheaf Y}
  (q : F⟮f,F⟯ ⟶ (FiniteLocallyFreeSheaf.toQuasicoherent X).obj E.obj) [Epi q.hom]

/-- A quotient of the pullback of a quasicoherent sheaf onto a line bundle
defines a morphism to the projectivization of the original sheaf. -/
def relativeProjHomOfQuotient : X ⟶ Sym[F].obj.relativeProj :=
  E.relativeProjSectionOfQuotient q ≫ F.relativeProjPullbackProjection f

/-- The morphism defined by a line quotient lies over the chosen base morphism. -/
@[reassoc (attr := simp)]
theorem relativeProjHomOfQuotient_toBase :
    E.relativeProjHomOfQuotient f q ≫ Sym[F].obj.relativeProjToBase = f := by
  simp [relativeProjHomOfQuotient]

/-- The morphism defined by a line quotient pulls the degree-one twist back to
that quotient line bundle. -/
def relativeProjHomOfQuotientPullbackTwistingSheafOneIso :
    (Scheme.Modules.pullback (E.relativeProjHomOfQuotient f q)).obj
      (Sym[F].obj.relativeProjTwistingSheaf 1) ≅ E.obj.obj := by
  rw [relativeProjHomOfQuotient]
  let s := E.relativeProjSectionOfQuotient q
  let p := F.relativeProjPullbackProjection f
  exact (Scheme.Modules.pullbackComp s p).symm.app _ ≪≫
    (Scheme.Modules.pullback s).mapIso (F.relativeProjPullbackProjectionTwistingSheafIso f 1) ≪≫
    E.relativeProjSectionOfQuotientPullbackTwistingSheafOneIso q

/-- Under the Cartesian comparison, the section defined by the line quotient is
the graph of its morphism to the original projectivization. -/
theorem relativeProjSectionOfQuotient_comp_isoPullback :
    E.relativeProjSectionOfQuotient q ≫
        (F.isPullback_relativeProjPullbackProjection f).isoPullback.hom =
      pullback.lift (𝟙 X) (E.relativeProjHomOfQuotient f q)
        ((Category.id_comp f).trans (E.relativeProjHomOfQuotient_toBase f q).symm) := by
  apply pullback.hom_ext
  · rw [Category.assoc, IsPullback.isoPullback_hom_fst, E.relativeProjSectionOfQuotient_toBase,
      pullback.lift_fst]
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd]
    rfl

/-- The graph over the base of the morphism defined by a line quotient is a
closed immersion. -/
theorem isClosedImmersion_pullback_lift_relativeProjHomOfQuotient :
    IsClosedImmersion (pullback.lift (𝟙 X) (E.relativeProjHomOfQuotient f q)
      ((Category.id_comp f).trans (E.relativeProjHomOfQuotient_toBase f q).symm)) := by
  rw [← E.relativeProjSectionOfQuotient_comp_isoPullback f q]
  infer_instance

end FiniteLocallyFreeSheaf.FixedRank

end TauCeti.AlgebraicGeometry
