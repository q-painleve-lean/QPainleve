/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

import Mathlib.CategoryTheory.HomCongr
import QPainleve.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Basic
public import QPainleve.Algebra.MonoidAlgebra.Isomorphism
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Points
public import TauCeti.CategoryTheory.Monoidal.Grp.Translation

/-!
# Isomorphisms of split tori

An isomorphism of split tori over a field is specified by an isomorphism of character lattices
and a translation on the target. We use the monomial description of group algebra isomorphisms
and compare its two factors with `DiagonalizableGroup.groupSchemeMap` and
`TauCeti.leftTranslation`. In particular, a torus automorphism acting trivially on the exponents
of characters is a translation.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace QPainleve.CharacterTorus

open TauCeti DiagonalizableGroup

universe u

variable {k : Type u} [CommRing k] {G H : FGCommGrpCat.{u}}

local notation "S" => Spec (CommRingCat.of k)
local notation "D(" G ")" => (Grp.X (groupScheme k G))
local notation "R[" G "]" => MonoidAlgebra k G

private abbrev coord (k : Type u) [CommRing k] (G : FGCommGrpCat.{u}) :=
  CommAlgCat.of (CommRingCat.of k) (MonoidAlgebra k G)

private theorem groupScheme_X_eq_algSpec (G : FGCommGrpCat.{u}) :
    D(G) = (algSpec (CommRingCat.of k)).obj (op (coord k G)) := by
  rw [groupScheme_def]
  rfl

/-- Relative spectrum identifies algebra isomorphisms of the coordinate rings with
isomorphisms of the underlying schemes over the base, in the opposite direction. -/
def algEquivToSchemeIso : (R[G] ≃ₐ[k] R[H]) ≃ (D(H) ≅ D(G)) :=
  CommAlgCat.isoEquivAlgEquiv.symm.trans <|
    (isoOpEquiv (op (coord k H)) (op (coord k G))).symm.trans <|
      (algSpec.fullyFaithful (R := CommRingCat.of k)).isoEquiv.trans <|
        (eqToIso (groupScheme_X_eq_algSpec H).symm).isoCongr
          (eqToIso (groupScheme_X_eq_algSpec G).symm)

/-- In the affine spectrum presentation, the underlying morphism is the spectrum map of the
given algebra isomorphism. -/
theorem algEquivToSchemeIso_hom_left (e : R[G] ≃ₐ[k] R[H]) :
    (algEquivToSchemeIso e).hom.left =
      eqToHom (groupScheme_X_left k H) ≫
        Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom) ≫
        eqToHom (groupScheme_X_left k G).symm := by
  simp [algEquivToSchemeIso, algSpec_map_left, commAlgCatEquivUnder, AlgHom.toUnder,
    Over.eqToHom_left]
  rfl

private theorem groupSchemePointsMulEquiv_comp_algEquivToSchemeIso
    {A : Type u} [CommRing A] [Algebra k A]
    (e : R[G] ≃ₐ[k] R[H]) (p : (Spec (CommRingCat.of A)).asOver S ⟶ D(H)) :
    groupSchemePointsMulEquiv G (p ≫ (algEquivToSchemeIso e).hom) =
      WithConv.toConv ((groupSchemePointsMulEquiv H p).ofConv.comp e.toAlgHom) := by
  apply (groupSchemePointsMulEquiv (R := k) (A := A) G).symm.injective
  apply Over.OverMorphism.ext
  rw [MulEquiv.symm_apply_apply, Over.comp_left, algEquivToSchemeIso_hom_left,
    groupSchemePointsMulEquiv_symm_apply_left, ← Category.assoc,
    groupSchemePointsMulEquiv_apply_left_comp, CommHopfAlgCat.mapMulEquiv_left]
  -- Expose the affine test scheme under the over-category projection for `Spec.map_comp`.
  change (Spec.map _ : Spec (CommRingCat.of A) ⟶ _) ≫ _ = Spec.map _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

private def unitToSpec : 𝟙_ (Over S) ⟶ (S).asOver S :=
  Over.homMk (U := 𝟙_ (Over S)) (V := (S).asOver S) (𝟙 S) (by
    exact (Category.id_comp (Spec.algebraMap k k)).trans (Spec.map_id _))

private theorem unitToSpec_left : (unitToSpec (k := k)).left = 𝟙 S := (rfl)

/-- The global point of the diagonalizable group corresponding to a unit-valued character. -/
def pointOfCharacter (χ : G →* kˣ) : 𝟙_ (Over S) ⟶ D(G) :=
  unitToSpec ≫
    (schemePointsMulEquiv (R := k) (A := k) G).symm χ

/-- Over an affine test scheme, the constant point associated to a character is obtained by
extending its values along the coefficient algebra map. -/
@[simp]
theorem schemePointsMulEquiv_toUnit_comp_pointOfCharacter
    {A : Type u} [CommRing A] [Algebra k A] (χ : G →* kˣ) :
    schemePointsMulEquiv G
        (toUnit ((Spec (CommRingCat.of A)).asOver S) ≫ pointOfCharacter χ) =
      (Units.map (algebraMap k A).toMonoidHom).comp χ := by
  have h : toUnit ((Spec (CommRingCat.of A)).asOver S) ≫
      unitToSpec =
      (Spec.map (CommRingCat.ofHom (Algebra.ofId k A).toRingHom)).asOver S := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.toUnit_left, unitToSpec_left]
    rfl
  rw [pointOfCharacter, ← Category.assoc, h, schemePointsMulEquiv_mapValue
    (phi := Algebra.ofId k A), MulEquiv.apply_symm_apply]
  rfl

/-- Twisting by a character on the coordinate ring gives translation by that point
on the diagonalizable group scheme. -/
theorem algEquivToSchemeIso_charTwist (χ : G →* kˣ) :
    algEquivToSchemeIso (MonoidAlgebra.charTwist χ) =
      leftTranslation (pointOfCharacter χ) := by
  let p := groupSchemeUniversalPoint (k := k) G
  apply Iso.ext
  apply (cancel_epi p).mp
  apply (schemePointsMulEquiv G).injective
  apply MonoidHom.ext
  intro g
  apply Units.ext
  rw [schemePointsMulEquiv_apply_coe, groupSchemePointsMulEquiv_comp_algEquivToSchemeIso,
    WithConv.ofConv_toConv, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    MonoidAlgebra.charTwist_single,
    comp_leftTranslation_hom, map_mul, schemePointsMulEquiv_toUnit_comp_pointOfCharacter]
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, Units.coe_map,
    schemePointsMulEquiv_apply_coe, mul_one]
  rw [MonoidAlgebra.single_eq_algebraMap_mul_of, MonoidAlgebra.of_apply, map_mul, AlgHom.commutes]
  rfl

/-- Transporting exponents on the coordinate ring gives the group-scheme map induced by
the exponent isomorphism. -/
theorem algEquivToSchemeIso_domCongr_hom (σ : G ≃* H) :
    (algEquivToSchemeIso (MonoidAlgebra.domCongr k k σ)).hom =
      (groupSchemeMap k (FGCommGrpCat.ofHom σ.toMonoidHom)).hom.hom := by
  let p := groupSchemeUniversalPoint (k := k) H
  apply (cancel_epi p).mp
  apply (schemePointsMulEquiv G).injective
  apply MonoidHom.ext
  intro a
  apply Units.ext
  simp only [schemePointsMulEquiv_groupSchemeMap, FGCommGrpCat.hom_hom_ofHom,
    MonoidHom.comp_apply, schemePointsMulEquiv_apply_coe,
    groupSchemePointsMulEquiv_comp_algEquivToSchemeIso, WithConv.ofConv_toConv,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, MonoidAlgebra.domCongr_single,
    MulEquiv.coe_toMonoidHom]

/-- Relative spectrum sends composition of algebra isomorphisms to composition in the
opposite order. -/
theorem algEquivToSchemeIso_trans {J : FGCommGrpCat.{u}} (e : R[G] ≃ₐ[k] R[H])
    (f : R[H] ≃ₐ[k] R[J]) :
    algEquivToSchemeIso (e.trans f) = algEquivToSchemeIso f ≪≫ algEquivToSchemeIso e := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  simp only [Iso.trans_hom, Over.comp_left, algEquivToSchemeIso_hom_left, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Spec.map_comp_assoc]
  rfl

/-- The identity algebra isomorphism gives the identity scheme isomorphism. -/
@[simp]
theorem algEquivToSchemeIso_refl :
    algEquivToSchemeIso (AlgEquiv.refl : R[G] ≃ₐ[k] R[G]) = Iso.refl D(G) := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  simp [algEquivToSchemeIso_hom_left]

/-- The scheme isomorphism of an inverse algebra isomorphism is the inverse scheme
isomorphism. -/
@[simp]
theorem algEquivToSchemeIso_symm (e : R[G] ≃ₐ[k] R[H]) :
    algEquivToSchemeIso e.symm = (algEquivToSchemeIso e).symm := by
  apply Iso.ext
  apply (cancel_mono (algEquivToSchemeIso e).hom).mp
  rw [Iso.symm_hom, Iso.inv_hom_id, ← Iso.trans_hom, ← algEquivToSchemeIso_trans,
    AlgEquiv.self_trans_symm, algEquivToSchemeIso_refl, Iso.refl_hom]

variable [IsDomain k] [TwoUniqueProds G] [TwoUniqueProds H]

/-- An isomorphism of split tori is uniquely specified by a character giving a target
translation and an isomorphism from the target character group to the source character group. -/
def schemeIsoEquivCharacter : ((G →* kˣ) × (G ≃* H)) ≃ (D(H) ≅ D(G)) :=
  MonoidAlgebra.charTwistDomCongrEquiv.trans algEquivToSchemeIso

/-- The torus isomorphism associated to a character and a lattice isomorphism first applies
the induced torus homomorphism and then translates on its target. -/
theorem schemeIsoEquivCharacter_apply_hom (p : (G →* kˣ) × (G ≃* H)) :
    (schemeIsoEquivCharacter p).hom =
      (groupSchemeMap k (FGCommGrpCat.ofHom p.2.toMonoidHom)).hom.hom ≫
        (leftTranslation (pointOfCharacter p.1)).hom := by
  rw [schemeIsoEquivCharacter, Equiv.trans_apply, MonoidAlgebra.charTwistDomCongrEquiv_apply,
    algEquivToSchemeIso_trans, Iso.trans_hom, algEquivToSchemeIso_domCongr_hom,
    algEquivToSchemeIso_charTwist]

/-- An identity exponent map gives a translation on the torus. -/
@[simp]
theorem schemeIsoEquivCharacter_refl (χ : G →* kˣ) :
    schemeIsoEquivCharacter (χ, MulEquiv.refl G) = leftTranslation (pointOfCharacter χ) := by
  rw [schemeIsoEquivCharacter, Equiv.trans_apply, MonoidAlgebra.charTwistDomCongrEquiv_apply]
  have h : (MonoidAlgebra.charTwist χ).trans (MonoidAlgebra.domCongr k k (MulEquiv.refl G)) =
      MonoidAlgebra.charTwist χ := by
    apply AlgEquiv.ext
    intro x
    simp
  rw [h, algEquivToSchemeIso_charTwist]

/-- On points over any coefficient algebra, the torus isomorphism precomposes the point
character with its lattice map and multiplies by its translation character. -/
theorem schemePointsMulEquiv_comp_schemeIsoEquivCharacter
    {A : Type u} [CommRing A] [Algebra k A] (p : (G →* kˣ) × (G ≃* H))
    (x : (Spec (CommRingCat.of A)).asOver S ⟶ D(H)) :
    schemePointsMulEquiv G (x ≫ (schemeIsoEquivCharacter p).hom) =
      (Units.map (algebraMap k A).toMonoidHom).comp p.1 *
        (schemePointsMulEquiv H x).comp p.2.toMonoidHom := by
  rw [schemeIsoEquivCharacter_apply_hom, ← Category.assoc, comp_leftTranslation_hom, map_mul,
    schemePointsMulEquiv_toUnit_comp_pointOfCharacter, schemePointsMulEquiv_groupSchemeMap,
    FGCommGrpCat.hom_hom_ofHom]

end QPainleve.CharacterTorus
