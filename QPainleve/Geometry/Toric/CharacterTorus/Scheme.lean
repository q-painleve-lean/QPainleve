/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.FunctionField
public import QPainleve.Geometry.Toric.CharacterTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Basic

/-!
# Split tori from character lattices

The spectrum of the character algebra has points given by multiplicative characters.
A map on lattices gives a contravariant morphism of these schemes. The generic stalk identifies
with the algebraic fraction field, so dominance and rational pullbacks can be checked in
the algebra of monomials. The additive presentation is related to TauCeti's
`DiagonalizableGroup.groupScheme`, and its points use `DiagonalizableGroup.pointEquiv`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti

namespace QPainleve.CharacterTorus

universe u

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

end QPainleve.CharacterTorus

namespace QPainleve.CharacterTorus

universe u

variable {k B C : Type u} [Field k] [AddCommGroup B] [AddCommGroup C]
  [Module ℤ B] [Module.Free ℤ B] [Module ℤ C] [Module.Free ℤ C]

local instance {G : Type*} [AddCommGroup G] [Module ℤ G] [Module.Free ℤ G] : HasUniqueDiv G :=
  .of_isTorsionFree ℤ G

omit [Module ℤ C] [Module.Free ℤ C] in
/-- Injective lattice maps give dominant morphisms of character tori. -/
theorem isDominant_map (f : B →+ C) (hf : Function.Injective f) : IsDominant (map k f) := by
  rw [isDominant_iff]
  -- The underlying map of an affine morphism is contraction of prime ideals.
  change DenseRange (PrimeSpectrum.comap (AddMonoidAlgebra.mapDomainAlgHom k k f).toRingHom)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, nilradical_eq_zero]
  exact ((RingHom.injective_iff_ker_eq_bot _).mp (AddMonoidAlgebra.mapDomain_injective hf)).le

variable (k B) in
/-- The fraction field of the group algebra identifies with the generic stalk of the torus. -/
def fractionRingEquiv :
    FunctionField k B ≃+* (scheme k B).functionField := by
  let R := CommRingCat.of (AddMonoidAlgebra k B)
  letI : IsDomain R := inferInstanceAs (IsDomain (AddMonoidAlgebra k B))
  letI : Algebra R (Spec R).functionField :=
    (StructureSheaf.toStalk R (genericPoint (Spec R))).hom.toAlgebra
  letI : IsFractionRing R (Spec R).functionField := functionField_isFractionRing_of_affine R
  exact (FractionRing.algEquiv R (Spec R).functionField).toRingEquiv

variable (k) in
/-- The pullback of a dominant rational map between character tori on the fraction-field models. -/
def rationalPullback (f : (scheme k C) ⤏ (scheme k B)) [f.IsDominant] :
    FunctionField k B →+* FunctionField k C :=
  ((fractionRingEquiv k C).symm.toRingHom.comp f.functionFieldMap.hom).comp
    (fractionRingEquiv k B).toRingHom

/-- Equality of dominant rational maps is detected on the fraction fields of the character rings. -/
theorem rationalPullback_eq_iff (f g : (scheme k C) ⤏ (scheme k B))
    [f.IsDominant] [g.IsDominant] : rationalPullback k f = rationalPullback k g ↔ f = g := by
  rw [← f.functionFieldMap_eq_iff g]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp only [rationalPullback, h]⟩
  apply CommRingCat.hom_ext
  ext x : 1
  obtain ⟨a, rfl⟩ := (fractionRingEquiv k B).surjective x
  exact (fractionRingEquiv k C).symm.injective (DFunLike.congr_fun h a)

private theorem preimage_fromSpecStalk (k B : Type u) [Field k] [AddCommGroup B]
    [Module ℤ B] [Module.Free ℤ B] :
    (Spec.preimage ((scheme k B).fromSpecStalk (genericPoint (scheme k B)))).hom =
      (fractionRingEquiv k B).toRingHom.comp
        (algebraMap (AddMonoidAlgebra k B) (FunctionField k B)) := by
  let R := CommRingCat.of (AddMonoidAlgebra k B)
  let : IsDomain R := inferInstanceAs (IsDomain (AddMonoidAlgebra k B))
  let : Algebra R (Spec R).functionField :=
    (StructureSheaf.toStalk R (genericPoint (Spec R))).hom.toAlgebra
  let : IsFractionRing R (Spec R).functionField := functionField_isFractionRing_of_affine R
  have h : Spec.preimage ((Spec R).fromSpecStalk (genericPoint (Spec R))) =
      StructureSheaf.toStalk R (genericPoint (Spec R)) :=
    congrArg Spec.preimage (Spec.fromSpecStalk_eq' R _) |>.trans (Spec.preimage_map _)
  apply RingHom.ext
  intro x
  exact (congrArg (fun ψ : R ⟶ (Spec R).functionField ↦ ψ x) h).trans
    ((FractionRing.algEquiv R (Spec R).functionField).commutes x).symm

/-- Restricting the fraction-field pullback to regular functions gives the map on the generic
point of the source. -/
theorem rationalPullback_comp_algebraMap (f : (scheme k C) ⤏ (scheme k B)) [f.IsDominant] :
    (rationalPullback k f).comp (algebraMap (AddMonoidAlgebra k B) (FunctionField k B)) =
      (fractionRingEquiv k C).symm.toRingHom.comp (Spec.preimage f.fromFunctionField).hom := by
  have h := congrArg Spec.preimage f.specMap_functionFieldMap
  rw [Spec.preimage_comp, Spec.preimage_map] at h
  rw [← h, CommRingCat.hom_comp, preimage_fromSpecStalk]
  simp only [rationalPullback, RingHom.comp_assoc]

/-- A lattice map's algebraic and scheme-theoretic pullbacks agree on the fraction fields. -/
theorem rationalPullback_map (f : B →+ C) (hf : Function.Injective f) :
    let : IsDominant (map k f) := isDominant_map f hf
    rationalPullback k (map k f).toRationalMap = (functionFieldMap k f hf).toRingHom := by
  let : IsDominant (map k f) := isDominant_map f hf
  apply IsFractionRing.ringHom_ext (A := AddMonoidAlgebra k B)
  have h : (map k f).toRationalMap.fromFunctionField =
      (scheme k C).fromSpecStalk (genericPoint (scheme k C)) ≫ map k f := by
    rw [Scheme.Hom.toRationalMap, Scheme.RationalMap.fromFunctionField_toRationalMap]
    exact Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap _ _
  intro p
  have eqOnCoordinates := DFunLike.congr_fun
    (rationalPullback_comp_algebraMap (map k f).toRationalMap) p
  rw [h, Spec.preimage_comp, CommRingCat.hom_comp, preimage_fromSpecStalk,
    preimage_map] at eqOnCoordinates
  simp only [RingHom.comp_apply] at eqOnCoordinates
  rw [eqOnCoordinates]
  calc
    _ = _ := (fractionRingEquiv k C).symm_apply_apply _
    _ = _ := (functionFieldMap_algebraMap k f hf p).symm

end QPainleve.CharacterTorus
