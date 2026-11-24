/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsSepClosed
public import QPainleve.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Basic
public import QPainleve.AlgebraicGeometry.RationalMap.FunctionField
public import QPainleve.Geometry.Toric.CharacterTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Points
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra

import QPainleve.Algebra.MonoidAlgebra.Smooth
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RationalPoint

/-!
# Character schemes and their function fields

TauCeti's `DiagonalizableGroup.groupScheme` gives the torus of a finite free character
lattice. Its generic stalk identifies with the fraction field of the character algebra,
and the pullback of a lattice map transports monomial exponents. The additive spectrum
presentation also works for character groups without a finite-generation hypothesis.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti DiagonalizableGroup

namespace QPainleve.CharacterTorus

universe u

section Affine

variable (k B : Type u) [CommRing k] [AddCommGroup B]

/-- The spectrum of the character algebra. A finite free character lattice gives a split torus. -/
abbrev scheme : Scheme := Spec (CommRingCat.of (AddMonoidAlgebra k B))

/-- The underlying scheme of a diagonalizable group is the spectrum in additive coordinates. -/
def diagonalizableGroupSchemeIso (G : FGCommGrpCat.{u}) :
    (DiagonalizableGroup.groupScheme k G).X.left ≅ scheme k (Additive G) :=
  eqToIso (DiagonalizableGroup.groupScheme_X_left k G) ≪≫
    Scheme.Spec.mapIso
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k (Additive G)).toRingEquiv.toCommRingCatIso.op

/-- The structure morphism of the character scheme over its coefficient ring. -/
abbrev structureMap : scheme k B ⟶ Spec (CommRingCat.of k) :=
  Spec.algebraMap k (AddMonoidAlgebra k B)

variable {k B} in
/-- A finitely generated character lattice gives a scheme locally of finite type over the base. -/
instance [Module ℤ B] [Module.Finite ℤ B] :
    LocallyOfFiniteType (scheme k B ↘ Spec (CommRingCat.of k)) := by
  have h : (inferInstance : Module ℤ B) = AddCommGroup.toIntModule B := Subsingleton.elim _ _
  have : AddGroup.FG B := Module.Finite.iff_addGroup_fg.mp (h ▸ ‹Module.Finite ℤ B›)
  have : AddMonoid.FG B := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  exact AlgebraicGeometry.locallyOfFiniteType_specOverSpec

/-- Points of the character scheme over the coefficient ring. -/
abbrev Points :=
  {p : Spec (CommRingCat.of k) ⟶ scheme k B //
    p ≫ structureMap k B = 𝟙 (Spec (CommRingCat.of k))}

/-- Points over the coefficient ring are multiplicative characters of the lattice. -/
def pointsEquiv : Points k B ≃ (Multiplicative B →* kˣ) := by
  have h : Spec.algebraMap k k = 𝟙 (Spec (CommRingCat.of k)) := Spec.map_id _
  exact (Equiv.subtypeEquivProp (by rw [h])).trans <|
    Spec.homEquivAlgHom.trans <|
      (AlgEquiv.arrowCongr (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k B)
        (AlgEquiv.refl : k ≃ₐ[k] k)).trans
        DiagonalizableGroup.pointEquiv

/-- The point attached to a character is evaluation of each monomial at that character. -/
theorem pointsEquiv_symm_apply_val (c : Multiplicative B →* kˣ) :
    ((pointsEquiv k B).symm c).val =
      Spec.map (CommRingCat.ofHom
        ((DiagonalizableGroup.point c).comp
          (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k B).toAlgHom).toRingHom) := (rfl)

/-- The character scheme on a finite tuple of integer exponents is smooth over the base. -/
instance smooth_structureMap_pi_int (ι : Type u) [Finite ι] :
    Smooth (structureMap k (ι → ℤ)) := by
  rw [structureMap, Spec.algebraMap, HasRingHomProperty.Spec_iff (P := @Smooth),
    CommRingCat.hom_ofHom, RingHom.smooth_algebraMap]
  let e := (Finsupp.linearEquivFunOnFinite ℤ ℤ ι).toAddEquiv
  let := AddMonoidAlgebra.isStandardSmoothOfRelativeDimension_finsupp_int k ι
  let := Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (Nat.card ι)
    (AddMonoidAlgebra.domCongr k k e)
  let : Algebra.IsStandardSmooth k (AddMonoidAlgebra k (ι → ℤ)) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := Nat.card ι)
  infer_instance

/-- Over a separably closed field, the characters of the finite center lattice give a
Zariski-dense family of points. -/
theorem denseRange_centerPoints (K : Type u) [Field K] [IsSepClosed K] (ι : Type u)
    [Finite ι] :
    DenseRange (fun c : Multiplicative (ι → ℤ) →* Kˣ ↦
      ((pointsEquiv K (ι → ℤ)).symm c).val default) := by
  let f (c : Points K (ι → ℤ)) := c.val default
  have hf : DenseRange f := (structureMap K (ι → ℤ)).denseRange_rationalSections
  have hr : Set.range (f ∘ (pointsEquiv K (ι → ℤ)).symm) = Set.range f :=
    (pointsEquiv K (ι → ℤ)).symm.surjective.range_comp f
  -- Reindex the rational sections by their character values.
  change Dense (Set.range (f ∘ (pointsEquiv K (ι → ℤ)).symm))
  rw [hr]
  exact hf

variable {B} {C : Type u} [AddCommGroup C]

/-- A map on character lattices induces a contravariant morphism of their character schemes. -/
def map (f : B →+ C) : scheme k C ⟶ scheme k B :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainAlgHom k k f).toRingHom)

/-- The affine ring map sends a character monomial to the monomial of the transported exponent. -/
@[simp]
theorem preimage_map (f : B →+ C) :
    (Spec.preimage (map k f)).hom = (AddMonoidAlgebra.mapDomainAlgHom k k f).toRingHom := by
  exact congrArg CommRingCat.Hom.hom
    (Spec.preimage_map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainAlgHom k k f).toRingHom))

@[reassoc (attr := simp)]
theorem map_structureMap (f : B →+ C) : map k f ≫ structureMap k B = structureMap k C := by
  dsimp only [map, structureMap, Spec.algebraMap]
  rw [← Spec.map_comp]
  congr 1
  ext r : 2
  exact (AddMonoidAlgebra.mapDomainAlgHom k k f).commutes r

@[simp]
theorem map_id : map k (AddMonoidHom.id B) = 𝟙 (scheme k B) := by
  rw [map, AddMonoidAlgebra.mapDomainAlgHom_id]
  exact Spec.map_id _

theorem map_comp {D : Type u} [AddCommGroup D] (f : B →+ C) (g : C →+ D) :
    map k (g.comp f) = map k g ≫ map k f := by
  rw [map, map, map, AddMonoidAlgebra.mapDomainAlgHom_comp, ← Spec.map_comp]
  congr 1

/-- The map of character schemes restricts a point character along the lattice map. -/
theorem pointsEquiv_symm_comp_map (f : B →+ C) (c : Multiplicative C →* kˣ) :
    ((pointsEquiv k C).symm c).val ≫ map k f =
      ((pointsEquiv k B).symm (c.comp f.toMultiplicative)).val := by
  rw [pointsEquiv_symm_apply_val, pointsEquiv_symm_apply_val, map, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  have h : ((DiagonalizableGroup.point c).comp
        (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k C).toAlgHom).comp
          (AddMonoidAlgebra.mapDomainAlgHom k k f) =
      (DiagonalizableGroup.point (c.comp f.toMultiplicative)).comp
        (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k B).toAlgHom := by
    apply (AddMonoidAlgebra.lift k k B).symm.injective
    apply MonoidHom.ext
    intro y
    simp [AddMonoidAlgebra.mapDomainAlgHom]
  exact AlgHom.congr_fun h x

/-- The isomorphism of character schemes induced by a lattice equivalence. -/
def mapIso (e : B ≃+ C) : scheme k C ≅ scheme k B where
  hom := map k e.toAddMonoidHom
  inv := map k e.symm.toAddMonoidHom
  hom_inv_id := by rw [← map_comp]; simp
  inv_hom_id := by rw [← map_comp]; simp

@[simp]
theorem mapIso_hom (e : B ≃+ C) : (mapIso k e).hom = map k e.toAddMonoidHom := (rfl)

@[simp]
theorem mapIso_inv (e : B ≃+ C) : (mapIso k e).inv = map k e.symm.toAddMonoidHom := (rfl)

/-- An injective character map induces a dominant morphism of affine character schemes. -/
theorem isDominant_map (f : B →+ C) (hf : Function.Injective f) : IsDominant (map k f) := by
  rw [isDominant_iff]
  change DenseRange (PrimeSpectrum.comap (AddMonoidAlgebra.mapDomainAlgHom k k f).toRingHom)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp (AddMonoidAlgebra.mapDomain_injective hf)]
  exact bot_le

end Affine

section AffineField

variable {k B C : Type u} [Field k] [AddCommGroup B] [AddCommGroup C]
  [Module ℤ B] [Module.Free ℤ B] [Module ℤ C] [Module.Free ℤ C]

attribute [local instance] hasUniqueDiv_of_free_int

variable (k B) in
/-- The fraction field of the group algebra identifies with the generic stalk of the torus. -/
def affineFractionRingEquiv :
    FunctionField k B ≃+* (scheme k B).functionField :=
  let R := CommRingCat.of (AddMonoidAlgebra k B)
  letI : IsDomain R := inferInstanceAs (IsDomain (AddMonoidAlgebra k B))
  Scheme.specFractionRingEquiv R rfl

variable (k) in
/-- The pullback of a dominant rational map between character tori on the fraction-field models. -/
def affineRationalPullback (f : (scheme k C) ⤏ (scheme k B)) [f.IsDominant] :
    FunctionField k B →+* FunctionField k C :=
  ((affineFractionRingEquiv k C).symm.toRingHom.comp f.functionFieldMap.hom).comp
    (affineFractionRingEquiv k B).toRingHom

/-- On the fraction-field models, the rational pullback is the map of generic stalks
transported by the canonical fraction field identifications. -/
theorem affineRationalPullback_apply (f : (scheme k C) ⤏ (scheme k B)) [f.IsDominant]
    (a : FunctionField k B) :
    affineRationalPullback k f a =
      (affineFractionRingEquiv k C).symm (f.functionFieldMap (affineFractionRingEquiv k B a)) :=
  (rfl)

/-- The identity rational map of a character torus pulls back each rational function to itself. -/
@[simp]
theorem affineRationalPullback_id (k : Type u) [Field k] {B : Type u} [AddCommGroup B]
    [Module ℤ B] [Module.Free ℤ B] :
    affineRationalPullback k (Scheme.RationalMap.id (scheme k B)) = RingHom.id _ := by
  ext a
  simp [affineRationalPullback_apply]

/-- Pullbacks of rational maps between character tori compose in the reverse order. -/
@[simp]
theorem affineRationalPullback_comp (k : Type u) [Field k] {B C D : Type u}
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module ℤ B] [Module.Free ℤ B] [Module ℤ C] [Module.Free ℤ C] [Module ℤ D] [Module.Free ℤ D]
    (f : (scheme k D) ⤏ (scheme k C)) (g : (scheme k C) ⤏ (scheme k B))
    [f.IsDominant] [g.IsDominant] :
    affineRationalPullback k (f.comp g) =
      (affineRationalPullback k f).comp (affineRationalPullback k g) := by
  ext a
  simp [affineRationalPullback_apply]

/-- Equality of dominant rational maps is detected on the fraction fields of the character rings. -/
theorem affineRationalPullback_eq_iff (f g : (scheme k C) ⤏ (scheme k B))
    [f.IsDominant] [g.IsDominant] :
    affineRationalPullback k f = affineRationalPullback k g ↔ f = g := by
  rw [← f.functionFieldMap_eq_iff g]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp only [affineRationalPullback, h]⟩
  apply CommRingCat.hom_ext
  ext x : 1
  obtain ⟨a, rfl⟩ := (affineFractionRingEquiv k B).surjective x
  exact (affineFractionRingEquiv k C).symm.injective (DFunLike.congr_fun h a)

/-- The generic-point morphism of a character torus is induced by its Laurent ring inclusion. -/
theorem preimage_fromSpecStalk (k B : Type u) [Field k] [AddCommGroup B]
    [Module ℤ B] [Module.Free ℤ B] :
    (Spec.preimage ((scheme k B).fromSpecStalk (genericPoint (scheme k B)))).hom =
      (affineFractionRingEquiv k B).toRingHom.comp
        (algebraMap (AddMonoidAlgebra k B) (FunctionField k B)) := by
  let R := CommRingCat.of (AddMonoidAlgebra k B)
  let : IsDomain R := inferInstanceAs (IsDomain (AddMonoidAlgebra k B))
  simpa only [affineFractionRingEquiv, eqToHom_refl, Category.comp_id] using
    Scheme.preimage_fromSpecStalk_comp R rfl

/-- Restricting the fraction-field pullback to regular functions gives the map on the generic
point of the source. -/
theorem affineRationalPullback_comp_algebraMap
    (f : (scheme k C) ⤏ (scheme k B)) [f.IsDominant] :
    (affineRationalPullback k f).comp (algebraMap (AddMonoidAlgebra k B) (FunctionField k B)) =
      (affineFractionRingEquiv k C).symm.toRingHom.comp
        (Spec.preimage f.fromFunctionField).hom := by
  have h := congrArg Spec.preimage f.specMap_functionFieldMap
  rw [Spec.preimage_comp, Spec.preimage_map] at h
  rw [← h, CommRingCat.hom_comp, preimage_fromSpecStalk]
  simp only [affineRationalPullback, RingHom.comp_assoc]

/-- The character field and the generic stalk of the character scheme are canonically
isomorphic over the base field. -/
def affineFractionRingAlgEquiv (k : Type u) [Field k] (B : Type u) [AddCommGroup B]
    [Module ℤ B] [Module.Free ℤ B] : FunctionField k B ≃ₐ[k] (scheme k B).functionField :=
  AlgEquiv.ofRingEquiv (f := affineFractionRingEquiv k B) fun a ↦ by
    have h := congrArg Spec.preimage
      (Scheme.fromSpecStalk_genericPoint_comp_over k (scheme k B))
    rw [specOverSpec_over, Spec.preimage_comp, Spec.preimage_map, Spec.preimage_map] at h
    have hScalar := ConcreteCategory.congr_hom h a
    change (Spec.preimage ((scheme k B).fromSpecStalk (genericPoint (scheme k B)))).hom
      (algebraMap k (AddMonoidAlgebra k B) a) = algebraMap k (scheme k B).functionField a at hScalar
    rwa [preimage_fromSpecStalk, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply] at hScalar

@[simp]
theorem affineFractionRingAlgEquiv_toRingEquiv (k : Type u) [Field k] {B : Type u}
    [AddCommGroup B] [Module ℤ B] [Module.Free ℤ B] :
    (affineFractionRingAlgEquiv k B).toRingEquiv = affineFractionRingEquiv k B := (rfl)

/-- A lattice map's algebraic and scheme-theoretic pullbacks agree on the fraction fields. -/
theorem affineRationalPullback_map (f : B →+ C) (hf : Function.Injective f) :
    let : IsDominant (map k f) := isDominant_map k f hf
    affineRationalPullback k (map k f).toRationalMap = (functionFieldMap k f hf).toRingHom := by
  let : IsDominant (map k f) := isDominant_map k f hf
  apply IsFractionRing.ringHom_ext (A := AddMonoidAlgebra k B)
  have h : (map k f).toRationalMap.fromFunctionField =
      (scheme k C).fromSpecStalk (genericPoint (scheme k C)) ≫ map k f := by
    rw [Scheme.Hom.toRationalMap, Scheme.RationalMap.fromFunctionField_toRationalMap]
    exact Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap _ _
  intro p
  have eqOnCoordinates := DFunLike.congr_fun
    (affineRationalPullback_comp_algebraMap (map k f).toRationalMap) p
  rw [h, Spec.preimage_comp, CommRingCat.hom_comp, preimage_fromSpecStalk,
    preimage_map] at eqOnCoordinates
  simp only [RingHom.comp_apply] at eqOnCoordinates
  rw [eqOnCoordinates]
  calc
    _ = _ := (affineFractionRingEquiv k C).symm_apply_apply _
    _ = _ := (functionFieldMap_algebraMap k f hf p).symm

end AffineField

section Field

variable {k : Type u} [Field k]

variable {B C : Type u} [AddCommGroup B] [AddCommGroup C] [IsAddFG B] [IsAddFG C]

attribute [local instance] hasUniqueDiv_of_free_int

local notation "L" B => FGCommGrpCat.of (Multiplicative B)
local notation "D" B => groupScheme k (L B)
local notation "Dmap" f => groupSchemeMap k (FGCommGrpCat.ofHom (AddMonoidHom.toMultiplicative f))

/-- The group scheme of a finite free character lattice over a field is integral. -/
instance isIntegral_groupScheme [Module.Free ℤ B] : IsIntegral (D B).X.left := by
  rw [groupScheme_X_left]
  infer_instance

variable (k) in
/-- The fraction field of the additive character algebra identifies with the generic stalk
of the diagonalizable group scheme. -/
def fractionRingEquiv (B : Type u) [AddCommGroup B] [IsAddFG B] [Module.Free ℤ B] :
    FunctionField k B ≃+* (groupScheme k (L B)).X.left.functionField :=
  let R := CommRingCat.of (MonoidAlgebra k (Multiplicative B))
  letI : IsDomain R := inferInstanceAs (IsDomain (MonoidAlgebra k (Multiplicative B)))
  let e := (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k B).toRingEquiv
  (IsFractionRing.ringEquivOfRingEquiv e).trans
    (Scheme.specFractionRingEquiv R (groupScheme_X_left k (L B)))

private theorem preimage_groupScheme_fromSpecStalk [Module.Free ℤ B] :
    (Spec.preimage ((D B).X.left.fromSpecStalk (genericPoint (D B).X.left) ≫
      eqToHom (groupScheme_X_left k (L B)))).hom.comp
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k B).toRingHom =
        (fractionRingEquiv k B).toRingHom.comp (algebraMap (AddMonoidAlgebra k B)
          (FunctionField k B)) := by
  let R := CommRingCat.of (MonoidAlgebra k (Multiplicative B))
  let : IsDomain R := inferInstanceAs (IsDomain (MonoidAlgebra k (Multiplicative B)))
  rw [Scheme.preimage_fromSpecStalk_comp R]
  apply RingHom.ext
  intro x
  simp [fractionRingEquiv, R]

variable [Module.Free ℤ B] [Module.Free ℤ C]

variable (k) in
/-- The pullback of a dominant rational map of character tori on the fraction-field models. -/
def rationalPullback (f : (D C).X.left ⤏ (D B).X.left) [f.IsDominant] :
    FunctionField k B →+* FunctionField k C :=
  ((fractionRingEquiv k C).symm.toRingHom.comp f.functionFieldMap.hom).comp
    (fractionRingEquiv k B).toRingHom

/-- Equality of dominant rational maps of character tori is detected on the fraction fields
of their character algebras. -/
theorem rationalPullback_eq_iff (f g : (D C).X.left ⤏ (D B).X.left)
    [f.IsDominant] [g.IsDominant] : rationalPullback k f = rationalPullback k g ↔ f = g := by
  rw [← f.functionFieldMap_eq_iff g]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp only [rationalPullback, h]⟩
  apply CommRingCat.hom_ext
  ext x : 1
  obtain ⟨a, rfl⟩ := (fractionRingEquiv k B).surjective x
  exact (fractionRingEquiv k C).symm.injective (DFunLike.congr_fun h a)

/-- Restricting the fraction-field pullback to the character algebra gives the map from the
generic point of the source, in additive coordinates. -/
theorem rationalPullback_comp_algebraMap
    (f : (D C).X.left ⤏ (D B).X.left) [f.IsDominant] :
    (rationalPullback k f).comp
        (algebraMap (AddMonoidAlgebra k B) (FunctionField k B)) =
      (fractionRingEquiv k C).symm.toRingHom.comp
        ((Spec.preimage (f.fromFunctionField ≫ eqToHom (groupScheme_X_left k (L B)))).hom.comp
          (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k B).toRingHom) := by
  rw [← f.specMap_functionFieldMap_assoc, Spec.preimage_comp, CommRingCat.hom_comp,
    Spec.preimage_map, RingHom.comp_assoc,
    preimage_groupScheme_fromSpecStalk]
  simp only [rationalPullback, RingHom.comp_assoc]

/-- On fraction fields, the native group-scheme morphism agrees with transport of exponents
along the injective character-group map. -/
theorem rationalPullback_groupSchemeMap (f : B →+ C) (hf : Function.Injective f) :
    let : IsDominant (Dmap f).hom.hom.left :=
      isDominant_groupSchemeMap k _ hf
    rationalPullback k (Dmap f).hom.hom.left.toRationalMap =
      (functionFieldMap k f hf).toRingHom := by
  let : IsDominant (Dmap f).hom.hom.left :=
      isDominant_groupSchemeMap k _ hf
  let g := (Dmap f).hom.hom.left
  have hg : g.toRationalMap.fromFunctionField =
      (D C).X.left.fromSpecStalk (genericPoint (D C).X.left) ≫ g := by
    rw [Scheme.Hom.toRationalMap, Scheme.RationalMap.fromFunctionField_toRationalMap]
    exact Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap _ _
  have h : (rationalPullback k g.toRationalMap).comp
      (algebraMap (AddMonoidAlgebra k B) (FunctionField k B)) =
        (functionFieldMap k f hf).toRingHom.comp
          (algebraMap (AddMonoidAlgebra k B) (FunctionField k B)) := by
    rw [rationalPullback_comp_algebraMap, hg, Category.assoc, groupSchemeMap_comp_toSpec,
      ← Category.assoc, Spec.preimage_comp, Spec.preimage_map, CommRingCat.hom_comp]
    have hcoord :
        (MonoidAlgebra.mapDomainAlgHom k k f.toMultiplicative).comp
            (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k B).toAlgHom =
          (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k C).toAlgHom.comp
            (AddMonoidAlgebra.mapDomainAlgHom k k f) := by
      apply AddMonoidAlgebra.algHom_ext
      · intro x
        simp
      · exact Subsingleton.elim _ _
    have hrings :
        (MonoidAlgebra.mapDomainAlgHom k k f.toMultiplicative).toRingHom.comp
            (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k B).toRingHom =
          (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k C).toRingHom.comp
            (AddMonoidAlgebra.mapDomainAlgHom k k f).toRingHom :=
      congrArg AlgHom.toRingHom hcoord
    rw [RingHom.comp_assoc, CommRingCat.hom_ofHom, FGCommGrpCat.hom_hom_ofHom,
      hrings, ← RingHom.comp_assoc (AddMonoidAlgebra.mapDomainAlgHom k k f).toRingHom,
      preimage_groupScheme_fromSpecStalk]
    apply RingHom.ext
    intro x
    exact ((fractionRingEquiv k C).symm_apply_apply _).trans
      (functionFieldMap_algebraMap k f hf x).symm
  exact IsFractionRing.ringHom_ext (fun x ↦ DFunLike.congr_fun h x)

end Field

end QPainleve.CharacterTorus
