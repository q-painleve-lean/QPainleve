/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Points
public import TauCeti.AlgebraicGeometry.GroupScheme.Kernel
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank

import Mathlib.GroupTheory.FiniteAbelian.Duality
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Kernel
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Kernel
import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Scheme-theoretic kernels of diagonalizable group morphisms

The kernel of `D(H) → D(G)` induced by `f : G → H` is the diagonalizable
group of the character quotient `H ⧸ range f`. The quotient map on characters
induces the kernel inclusion. This comparison applies to charge morphisms of
split tori, including when the charge image has less than full rank.

The construction uses Tau Ceti's `kernelCoordinateIso` and
`CommHopfAlgCat.isPullback_kernelSpec`. For a finite character quotient,
Mathlib's finite abelian duality computes the number of rational points
over an algebraically closed field of characteristic zero.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace TauCeti.DiagonalizableGroup

universe u

variable (R : Type u) [CommRing R] {G H : FGCommGrpCat.{u}} (f : G ⟶ H)

local notation "Q" => FGCommGrpCat.of (H ⧸ f.hom.hom.range)
local notation "q" => (FGCommGrpCat.ofHom (QuotientGroup.mk' f.hom.hom.range) : H ⟶ Q)
local notation "S" => Spec (CommRingCat.of R)
local notation "F" => AlgebraicGeometry.hopfSpec (CommRingCat.of R)

private def groupSchemeQuotientIsoKernelSpec :
    groupScheme R Q ≅ CommHopfAlgCat.kernelSpec (coordinateMap R f).hom :=
  eqToIso (groupScheme_def R Q) ≪≫ (F).mapIso (kernelCoordinateIso R f.hom.hom).op

private theorem groupSchemeQuotientIsoKernelSpec_hom_comp_ι :
    (groupSchemeQuotientIsoKernelSpec R f).hom ≫
        CommHopfAlgCat.kernelSpecι (coordinateMap R f).hom =
      groupSchemeMap R q ≫ eqToHom (groupScheme_def R H) := by
  rw [groupSchemeQuotientIsoKernelSpec, CommHopfAlgCat.kernelSpecι_def,
    CommHopfAlgCat.quotientSpecι_def, groupSchemeMap_def]
  simp only [Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom, Iso.op_hom, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [← Functor.map_comp, ← op_comp, mkQuotient_comp_kernelCoordinateIso_hom]
  rfl

/-- The quotient character group represents the fiber of the diagonalizable group
morphism over the identity section. -/
theorem isPullback_groupSchemeMap_quotient :
    IsPullback (groupSchemeMap R q)
      (0 : groupScheme R Q ⟶ Grp.trivial (Over S))
      (groupSchemeMap R f) (0 : Grp.trivial (Over S) ⟶ groupScheme R G) := by
  refine (CommHopfAlgCat.isPullback_kernelSpec (coordinateMap R f).hom).of_iso'
    (groupSchemeQuotientIsoKernelSpec R f) (eqToIso (groupScheme_def R H)) (Iso.refl _)
    (eqToIso (groupScheme_def R G)) (groupSchemeQuotientIsoKernelSpec_hom_comp_ι R f) ?_ ?_ ?_
  · simp
  · rw [groupSchemeMap_def]
    simp
  · simp

/-- The diagonalizable group of the quotient character group is the scheme-theoretic
kernel of the induced group-scheme morphism. -/
def groupSchemeQuotientIsoKernel :
    groupScheme R Q ≅ kernel (groupSchemeMap R f) :=
  (isPullback_groupSchemeMap_quotient R f).isoIsPullback _ _
    (GroupScheme.isPullback_kernel (groupSchemeMap R f))

/-- The kernel inclusion is induced by the quotient homomorphism on characters. -/
@[reassoc (attr := simp)]
theorem groupSchemeQuotientIsoKernel_hom_comp_ι :
    (groupSchemeQuotientIsoKernel R f).hom ≫ kernel.ι (groupSchemeMap R f) =
      groupSchemeMap R q :=
  IsPullback.isoIsPullback_hom_fst _ _ (isPullback_groupSchemeMap_quotient R f)
    (GroupScheme.isPullback_kernel (groupSchemeMap R f))

/-- Points of the scheme-theoretic kernel, over any coefficient algebra, are characters
of the quotient character group. -/
def kernelSchemePointsMulEquiv (B : Type u) [CommRing B] [Algebra R B] :
    ((Spec (CommRingCat.of B)).asOver S ⟶ (kernel (groupSchemeMap R f)).X) ≃*
      ((H ⧸ f.hom.hom.range) →* Bˣ) := by
  let e : (kernel (groupSchemeMap R f)).X ≅ (groupScheme R Q).X :=
    (Grp.forget (Over S)).mapIso (groupSchemeQuotientIsoKernel R f).symm
  letI : IsMonHom e.hom :=
    inferInstanceAs (IsMonHom (groupSchemeQuotientIsoKernel R f).inv.hom.hom)
  exact (CategoryTheory.Hom.mulEquivCongrRight
    (M := (kernel (groupSchemeMap R f)).X) (N := (groupScheme R Q).X)
    e ((Spec (CommRingCat.of B)).asOver S)).trans (schemePointsMulEquiv Q)

/-- The image of a kernel point in the ambient diagonalizable group evaluates on a
character via its class in the character quotient. -/
theorem schemePointsMulEquiv_comp_kernel_ι {B : Type u} [CommRing B] [Algebra R B]
    (z : (Spec (CommRingCat.of B)).asOver S ⟶ (kernel (groupSchemeMap R f)).X) :
    schemePointsMulEquiv (R := R) (A := B) H (z ≫ (kernel.ι (groupSchemeMap R f)).hom.hom) =
      (kernelSchemePointsMulEquiv R f B z).comp (QuotientGroup.mk' f.hom.hom.range) := by
  let e := groupSchemeQuotientIsoKernel R f
  have he : e.hom ≫ kernel.ι (groupSchemeMap R f) = groupSchemeMap R q :=
    groupSchemeQuotientIsoKernel_hom_comp_ι R f
  have hi : e.inv ≫ groupSchemeMap R q = kernel.ι (groupSchemeMap R f) := by
    rw [← he, Iso.inv_hom_id_assoc]
  rw [← hi, Grp.comp_hom_hom, ← Category.assoc, schemePointsMulEquiv_groupSchemeMap]
  -- On scheme points, the comparison postcomposes with the inverse kernel isomorphism.
  rw [kernelSchemePointsMulEquiv, MulEquiv.trans_apply, FGCommGrpCat.hom_hom_ofHom]
  congr 2

private def kernelOverIsoKernelSpec :
    (kernel (groupSchemeMap R f)).X ≅ (CommHopfAlgCat.kernelSpec (coordinateMap R f).hom).X :=
  (Grp.forget (Over S)).mapIso
    ((groupSchemeQuotientIsoKernel R f).symm ≪≫ groupSchemeQuotientIsoKernelSpec R f)

/-- The scheme-theoretic kernel is finite over a nonzero base exactly when the
character quotient is finite. -/
theorem isFinite_groupSchemeMap_kernel_iff [Nontrivial R] :
    IsFinite (kernel (groupSchemeMap R f)).X.hom ↔ Finite (H ⧸ f.hom.hom.range) := by
  rw [MorphismProperty.over_iso_iff (@IsFinite) (kernelOverIsoKernelSpec R f),
    ← moduleFinite_iff_isFinite_hopfSpec]
  exact moduleFinite_kernelCoordinate_iff R f.hom.hom

/-- A finite diagonalizable kernel has constant scheme-theoretic rank equal to the
index of the image of the character map, in every characteristic. -/
theorem finrank_groupSchemeMap_kernel [Finite (H ⧸ f.hom.hom.range)]
    (x : PrimeSpectrum R) :
    (kernel (groupSchemeMap R f)).X.hom.finrank x = f.hom.hom.range.index := by
  let : Nontrivial R := x.nontrivial
  let C := _root_.CommHopfAlgCat.quotient (coordinateRing R H).obj
    (CommHopfAlgCat.kernelHopfIdeal (coordinateMap R f).hom)
  let e := (_root_.CommHopfAlgCat.ofIso (kernelCoordinateIso R f.hom.hom)).toAlgEquiv
  let : Module.Free R C := Module.Free.of_equiv e.toLinearEquiv.symm
  let : Module.Finite R C := (moduleFinite_kernelCoordinate_iff R f.hom.hom).mpr inferInstance
  let : Flat (CommHopfAlgCat.kernelSpec (coordinateMap R f).hom).X.hom :=
    (moduleFlat_iff_flat_hopfSpec R C).mp inferInstance
  let : IsFinite (CommHopfAlgCat.kernelSpec (coordinateMap R f).hom).X.hom :=
    (moduleFinite_iff_isFinite_hopfSpec R C).mp inferInstance
  rw [congrFun (finrank_eq_of_nonempty_iso_over ⟨kernelOverIsoKernelSpec R f⟩) x,
    finrank_hopfSpec R C x, Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply,
    Nat.cast_id, Subgroup.index_eq_card]
  exact finrank_kernelCoordinate R f.hom.hom

/-- When the base has enough roots of unity for the finite character quotient,
the number of rational points of the kernel is its index. This applies over
algebraically closed fields of characteristic zero. -/
theorem natCard_kernelSchemePoints [Finite (H ⧸ f.hom.hom.range)]
    [HasEnoughRootsOfUnity R (Monoid.exponent (H ⧸ f.hom.hom.range))] :
    Nat.card ((Spec (CommRingCat.of R)).asOver S ⟶ (kernel (groupSchemeMap R f)).X) =
      f.hom.hom.range.index := by
  rw [Nat.card_congr (kernelSchemePointsMulEquiv R f R).toEquiv, Subgroup.index_eq_card]
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ R

end TauCeti.DiagonalizableGroup
