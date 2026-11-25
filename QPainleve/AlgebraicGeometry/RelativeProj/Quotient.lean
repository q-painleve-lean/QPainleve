/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.LineBundle.Basic
public import QPainleve.AlgebraicGeometry.RelativeProj.Pullback

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
local notation "F⟮" f "," F "⟯" => Functor.obj (QuasicoherentSheaf.pullback f) F

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
