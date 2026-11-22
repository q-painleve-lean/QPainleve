/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant

import TauCeti.AlgebraicGeometry.Morphisms.Epi

/-!
# Function fields and pullback along dominant rational maps

For an affine scheme presented as the spectrum of a domain, the function field is
identified with the fraction ring of that domain.

A dominant rational map with integral source is determined by its pullback on generic stalks.
The pullback applies Tau Ceti's `Scheme.Hom.functionFieldMap` to Mathlib's generic-point
restriction. Cancellation uses Tau Ceti's `RingHom.epi_SpecMap_ofHom` on the resulting homomorphism.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- If a scheme is presented as the spectrum of a domain, its generic stalk is isomorphic
to the fraction ring of that domain. -/
def specFractionRingEquiv {X : Scheme.{u}} [IrreducibleSpace X]
    (R : CommRingCat.{u}) [IsDomain R] (h : X = Spec R) :
    FractionRing R ≃+* X.functionField := by
  subst X
  letI : Algebra R (Spec R).functionField :=
    (StructureSheaf.toStalk R (genericPoint (Spec R))).hom.toAlgebra
  letI : IsFractionRing R (Spec R).functionField := functionField_isFractionRing_of_affine R
  exact (FractionRing.algEquiv R (Spec R).functionField).toRingEquiv

/-- For a scheme presented as the spectrum of a domain, the generic-stalk morphism
corresponds to the inclusion of the domain into its fraction ring. -/
theorem preimage_fromSpecStalk_comp {X : Scheme.{u}} [IrreducibleSpace X]
    (R : CommRingCat.{u}) [IsDomain R] (h : X = Spec R) :
    (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ eqToHom h)).hom =
      (specFractionRingEquiv R h).toRingHom.comp (algebraMap R (FractionRing R)) := by
  subst X
  let s : R ⟶ (Spec R).functionField :=
    StructureSheaf.toStalk R (genericPoint (Spec R))
  have hs : (Spec R).fromSpecStalk (genericPoint (Spec R)) = Spec.map s :=
    Spec.fromSpecStalk_eq' R _
  rw [eqToHom_refl, Category.comp_id, hs, Spec.preimage_map]
  let : Algebra R (Spec R).functionField := s.hom.toAlgebra
  let : IsFractionRing R (Spec R).functionField := functionField_isFractionRing_of_affine R
  exact RingHom.ext fun x ↦ ((FractionRing.algEquiv R (Spec R).functionField).commutes x).symm

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.RationalMap

variable {X Y : Scheme}

/-- The generic-point restriction of a dominant rational map is dominant. -/
instance [IrreducibleSpace X] (f : X ⤏ Y) [f.IsDominant] : IsDominant f.fromFunctionField := by
  obtain ⟨p, rfl⟩ := f.exists_rep
  have : IsDominant p.hom := p.isDominant_toRationalMap_iff.mp inferInstance
  rw [fromFunctionField_toRationalMap]
  dsimp only [PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem]
  have h : IsDominant (p.domain.fromSpecStalkOfMem (genericPoint X)
      ((genericPoint_specializes _).mem_open p.domain.2 p.dense_domain.nonempty.choose_spec) ≫
        p.domain.ι) := by
    rw [Opens.fromSpecStalkOfMem_ι]
    infer_instance
  have := IsDominant.of_comp_of_isOpenImmersion _ _ (H := h)
  infer_instance

variable [IsIntegral X] [IrreducibleSpace Y]

/-- Pullback on generic stalks along a dominant rational map with integral source. -/
def functionFieldMap (f : X ⤏ Y) [f.IsDominant] : Y.functionField ⟶ X.functionField :=
  f.fromFunctionField.functionFieldMap ≫
    (Spec X.functionField).presheaf.stalkSpecializes
      (specializes_of_eq (Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _)) ≫
    (stalkClosedPointIso X.functionField).hom

/-- The function field pullback recovers the restriction to the generic point. -/
@[reassoc]
theorem specMap_functionFieldMap (f : X ⤏ Y) [f.IsDominant] :
    Spec.map f.functionFieldMap ≫ Y.fromSpecStalk (genericPoint Y) = f.fromFunctionField := by
  have h := SpecMap_stalkSpecializes_fromSpecStalk_assoc (X := Spec X.functionField)
    (x := IsLocalRing.closedPoint X.functionField) (y := genericPoint (Spec X.functionField))
    (specializes_of_eq (Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _))
    f.fromFunctionField
  simp only [functionFieldMap, Spec.map_comp_assoc, Hom.SpecMap_functionFieldMap_fromSpecStalk, h,
    ← Spec_stalkClosedPointIso]
  rw [← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

/-- Dominant rational maps from an integral scheme agree exactly when their pullbacks agree. -/
theorem functionFieldMap_eq_iff (f g : X ⤏ Y) [f.IsDominant] [g.IsDominant] :
    f.functionFieldMap = g.functionFieldMap ↔ f = g := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst g; rfl⟩
  exact f.eq_of_fromFunctionField_eq g (by rw [← f.specMap_functionFieldMap,
    ← g.specMap_functionFieldMap, h])

section Composition

variable {Z : Scheme}

/-- Restricting a composition to the generic point pulls the second map back along the
function field map of the dominant first map. -/
theorem fromFunctionField_comp (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) :
    (f.comp g).fromFunctionField = Spec.map f.functionFieldMap ≫ g.fromFunctionField := by
  obtain ⟨q, rfl⟩ := g.exists_rep
  rw [comp_def, fromFunctionField_toRationalMap, fromFunctionField_toRationalMap]
  let p := f.representative
  let W := p.domain.ι ''ᵁ p.hom ⁻¹ᵁ q.domain
  have hx : genericPoint X ∈ W :=
    (genericPoint_specializes _).mem_open W.2 (p.comp q).dense_domain.nonempty.choose_spec
  have hy : genericPoint Y ∈ q.domain :=
    (genericPoint_specializes _).mem_open q.domain.2 q.dense_domain.nonempty.choose_spec
  have hWp : W ≤ p.domain := p.domain.ι_image_le _
  -- The composite domain and the first domain contain the same generic point.
  have hLift : W.fromSpecStalkOfMem _ hx ≫ X.homOfLE hWp =
      p.domain.fromSpecStalkOfMem _ (hWp hx) := by
    apply (cancel_mono p.domain.ι).mp
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  -- Compare the two lifts after inclusion of the second domain into the intermediate scheme.
  have h : W.fromSpecStalkOfMem _ hx ≫ (p.domain.ι.isoImage _).inv ≫ p.hom ∣_ q.domain =
      Spec.map f.functionFieldMap ≫ q.domain.fromSpecStalkOfMem _ hy := by
    apply (cancel_mono q.domain.ι).mp
    simp only [Category.assoc, morphismRestrict_ι, Scheme.Opens.isoImage_ι_inv_ι_assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι, specMap_functionFieldMap]
    rw [← Category.assoc, hLift, ← f.toRationalMap_representative, fromFunctionField_toRationalMap]
    rfl
  calc
    _ = (W.fromSpecStalkOfMem _ hx ≫ (p.domain.ι.isoImage _).inv ≫ p.hom ∣_ q.domain) ≫ q.hom := by
      simp only [PartialMap.fromSpecStalkOfMem, PartialMap.comp_hom, Category.assoc]
      rfl
    _ = _ := by rw [h, Category.assoc]; rfl

/-- A dominant rational map of integral schemes can be cancelled on the left of a
composition. The two maps out of its target may be arbitrary rational maps. -/
theorem comp_left_injective [IsIntegral Y] (f : X ⤏ Y) [f.IsDominant] :
    Function.Injective (fun g : Y ⤏ Z ↦ f.comp g) := by
  have : Epi (Spec.map f.functionFieldMap) :=
    inferInstanceAs (Epi (Spec.map (CommRingCat.ofHom f.functionFieldMap.hom)))
  intro g₁ g₂ h
  apply g₁.eq_of_fromFunctionField_eq
  apply (cancel_epi (Spec.map f.functionFieldMap)).mp
  simpa only [fromFunctionField_comp] using congrArg RationalMap.fromFunctionField h

end Composition

end AlgebraicGeometry.Scheme.RationalMap
