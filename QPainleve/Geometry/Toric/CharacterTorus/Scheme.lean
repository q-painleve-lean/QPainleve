/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme
public import QPainleve.AlgebraicGeometry.RationalMap.FunctionField
public import QPainleve.Geometry.Toric.CharacterTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Points

/-!
# Function fields of character tori

TauCeti's `DiagonalizableGroup.groupScheme` gives the torus of a finite free character
lattice. Its generic stalk identifies with the fraction field of the character algebra,
and the pullback of a lattice map transports monomial exponents.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti DiagonalizableGroup

namespace QPainleve.CharacterTorus

universe u

section Field

variable {k : Type u} [Field k]

variable {B C : Type u} [AddCommGroup B] [AddCommGroup C] [IsAddFG B] [IsAddFG C]

local notation "L" B => FGCommGrpCat.of (Multiplicative B)
local notation "D" B => groupScheme k (L B)
local notation "Dmap" f => groupSchemeMap k (FGCommGrpCat.ofHom (AddMonoidHom.toMultiplicative f))

private theorem isDomain_characterRing (B : Type u) [AddCommGroup B] [Module.Free ℤ B] :
    IsDomain (MonoidAlgebra k (Multiplicative B)) :=
  (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k B).symm.injective.isDomain _

/-- The group scheme of a finite free character lattice over a field is integral. -/
instance isIntegral_groupScheme [Module.Free ℤ B] : IsIntegral (D B).X.left := by
  rw [groupScheme_X_left]
  let : IsDomain (MonoidAlgebra k (Multiplicative B)) := isDomain_characterRing B
  infer_instance

variable (k) in
/-- The fraction field of the additive character algebra identifies with the generic stalk
of the diagonalizable group scheme. -/
def fractionRingEquiv (B : Type u) [AddCommGroup B] [IsAddFG B] [Module.Free ℤ B] :
    FunctionField k B ≃+* (groupScheme k (L B)).X.left.functionField :=
  let R := CommRingCat.of (MonoidAlgebra k (Multiplicative B))
  letI : IsDomain R := isDomain_characterRing B
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
  let : IsDomain R := isDomain_characterRing B
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
