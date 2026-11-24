/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic
public import TauCeti.AlgebraicGeometry.Normalization.Finite
public import TauCeti.AlgebraicGeometry.Scheme.GlobalFunctions

import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import QPainleve.AlgebraicGeometry.Morphisms.Flat.StructureSheaf
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.AffineScheme.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Flat.StructureSheaf

/-!
# Relative normalization along proper morphisms

For a universally closed morphism, the affine charts in Mathlib's relative normalization are
the spectra of all sections over the corresponding inverse images. This identifies their
rings of sections with integrally closed domains when the source is normal and integral.
For a dominant morphism quasi-finite at the generic point, the normalization is finite
when the target is locally of finite type over a Noetherian universally Japanese ring.
-/

public section

open CategoryTheory TauCeti TauCeti.AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}}

section UniversallyClosed

variable (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [UniversallyClosed f]

/-- In the relative normalization along a universally closed morphism, the sections on the
preimage of an affine open are all the sections on its inverse image in the source. -/
private theorem isIso_toNormalization_app_of_isAffineOpen {U : Y.Opens} (hU : IsAffineOpen U) :
    IsIso (f.toNormalization.app (f.fromNormalization ⁻¹ᵁ U)) := by
  let := (f.app U).hom.toAlgebra
  have : IsIso (CommRingCat.ofHom
      (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)).val.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨Subtype.val_injective, fun s ↦ ⟨⟨s, f.isIntegral_app_of_universallyClosed hU s⟩, rfl⟩⟩
  have h := f.toNormalization_app_preimage ⟨U, hU⟩
  dsimp only at h
  rw [h]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' ‹_› inferInstance)

/-- Pullback along the source map of the relative normalization of a universally
closed morphism is an isomorphism on sections over every open. -/
theorem isIso_app_toNormalization (W : f.normalization.Opens) :
    IsIso (f.toNormalization.app W) := by
  let ι := {UV : f.normalization.affineOpens × Y.affineOpens //
    (UV.1 : f.normalization.Opens) ≤ f.fromNormalization ⁻¹ᵁ UV.2}
  refine f.toNormalization.isIso_app_of_isBasis (B := fun i : ι ↦ i.val.1)
    f.fromNormalization.isBasis_range_affineOpens_le_preimage (fun i ↦ ?_) W
  obtain ⟨⟨V, U⟩, hVU⟩ := i
  have := f.isIso_toNormalization_app_of_isAffineOpen U.property
  exact f.toNormalization.isIso_app_of_isIso_app_of_le (U.property.preimage _) V.property hVU

/-- The relative normalization along a universally closed morphism from a normal integral
scheme is normal. -/
theorem isNormalScheme_normalization_of_isNormalScheme [IsIntegral X] [IsNormalScheme X] :
    IsNormalScheme f.normalization := by
  refine isNormalScheme_iff_forall_exists_affineOpens.mpr fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.fromNormalization x))
      isOpen_univ
  let V := f.fromNormalization ⁻¹ᵁ U
  have hxV : x ∈ V := hxU
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  obtain ⟨y, hy⟩ := f.toNormalization.surjective x
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨y, by
    rw [← f.toNormalization_fromNormalization, comp_preimage]
    exact f.toNormalization.mem_preimage.mpr (hy.symm ▸ hxV)⟩⟩
  have := f.isIso_app_toNormalization V
  let e := (asIso (f.toNormalization.app V)).commRingCatIsoToRingEquiv
  have : IsIntegrallyClosed Γ(X, f.toNormalization ⁻¹ᵁ V) := by
    rw [← comp_preimage, f.toNormalization_fromNormalization]
    have h := X.isIntegrallyClosedIn_functionField (f ⁻¹ᵁ U) fun _ _ ↦ inferInstance
    exact .of_isIntegrallyClosedIn _ X.functionField
  have : IsIntegrallyClosed Γ(f.normalization, V) := .of_equiv e.symm
  exact ⟨⟨V, hU.preimage _⟩, hxV, inferInstance⟩

end UniversallyClosed

section Finite

variable (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f]

/-- Quasi-finiteness of a dominant morphism of integral schemes at the generic point gives a
finite extension on function fields. -/
theorem finite_functionFieldMap_of_quasiFiniteAt_genericPoint
    (hf : f.QuasiFiniteAt (genericPoint X)) :
    let := f.functionFieldMap.hom.toAlgebra
    Module.Finite Y.functionField X.functionField := by
  let := f.functionFieldMap.hom.toAlgebra
  have : LocallyQuasiFinite (Spec.map f.functionFieldMap ≫ Y.fromSpecStalk (genericPoint Y)) :=
    f.SpecMap_functionFieldMap_fromSpecStalk.symm ▸ Scheme.Hom.quasiFiniteAt_iff.mp hf
  have h := LocallyQuasiFinite.of_comp (Spec.map f.functionFieldMap)
    (Y.fromSpecStalk (genericPoint Y))
  have hq : f.functionFieldMap.hom.QuasiFinite :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp h
  have : Algebra.QuasiFinite Y.functionField X.functionField := hq.toAlgebra
  exact .of_quasiFinite

variable [QuasiCompact f] [QuasiSeparated f]

/-- The relative normalization along a dominant morphism of integral schemes quasi-finite
at the generic point is finite when the target is locally of finite type over a Noetherian
universally Japanese ring. -/
theorem isFinite_fromNormalization_of_quasiFiniteAt_genericPoint
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Ring.IsUniversallyJapanese R]
    (g : Y ⟶ Spec (.of R)) [LocallyOfFiniteType g] (hf : f.QuasiFiniteAt (genericPoint X)) :
    IsFinite f.fromNormalization := by
  refine f.isFinite_fromNormalization_iff.mpr fun U hU ↦ ?_
  let := (f.app U).hom.toAlgebra
  by_cases hη : genericPoint Y ∈ U
  · have : Nonempty U := ⟨⟨_, hη⟩⟩
    let := f.functionFieldMap.hom.toAlgebra
    have : Module.Finite Y.functionField X.functionField :=
      f.finite_functionFieldMap_of_quasiFiniteAt_genericPoint hf
    have := functionField_isFractionRing_of_isAffineOpen Y U hU
    have := isJapanese_sections_of_locallyOfFiniteType g hU
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
    have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    let : Algebra Γ(Y, U) X.functionField :=
      (f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U)).hom.toAlgebra
    have : IsScalarTower Γ(Y, U) Y.functionField X.functionField :=
      .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom
        (f.germToFunctionField_functionFieldMap U)).symm
    let j : Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, U)] X.functionField :=
      ⟨(X.germToFunctionField (f ⁻¹ᵁ U)).hom, fun _ ↦ rfl⟩
    have := Ring.IsJapanese.finite_integralClosure (R := Γ(Y, U)) Y.functionField X.functionField
    exact Module.Finite.of_injective j.mapIntegralClosure.toLinearMap
      (fun a b hab ↦ Subtype.ext (X.germToFunctionField_injective _ (congrArg Subtype.val hab)))
  · have : U = ⊥ := eq_bot_iff.mpr fun y hy ↦
      (hη ((genericPoint_specializes y).mem_open U.isOpen hy)).elim
    subst U
    have : Subsingleton Γ(X, f ⁻¹ᵁ (⊥ : Y.Opens)) := f.preimage_bot.symm ▸
      (inferInstance : Subsingleton Γ(X, (⊥ : X.Opens)))
    infer_instance

end Finite

section Modification

variable (f : X ⟶ Y) [IsProper f]

/-- The source map of the relative normalization of a proper morphism is a modification
if the source is irreducible and the morphism has a quasi-finite point. -/
theorem isModification_toNormalization_of_quasiFiniteAt [IrreducibleSpace X]
    {x : X} (hx : f.QuasiFiniteAt x) : IsModification f.toNormalization := by
  have : IsProper (f.toNormalization ≫ f.fromNormalization) :=
    f.toNormalization_fromNormalization.symm ▸ ‹IsProper f›
  have : IsProper f.toNormalization := IsProper.of_comp _ f.fromNormalization
  have : IrreducibleSpace f.normalization :=
    f.toNormalization.surjective.irreducibleSpace f.toNormalization.continuous
  obtain ⟨U, hxU, hU⟩ := f.exists_mem_and_isIso_morphismRestrict_toNormalization x hx
  have hxV := f.toNormalization.mem_preimage.mpr hxU
  exact ⟨⟨U, U.isOpen.dense ⟨_, hxU⟩,
    (f.toNormalization ⁻¹ᵁ U).isOpen.dense ⟨x, hxV⟩, hU⟩⟩

/-- A nonempty connected fiber of a proper morphism over which the relative normalization
is finite lies over a single point of that normalization. Its full inverse image under
the source map is the original fiber. -/
theorem exists_preimage_singleton_toNormalization_of_isConnected [IsFinite f.fromNormalization]
    {p : Y} (hp : _root_.IsConnected (f ⁻¹' {p})) :
    ∃ q : f.normalization, f.fromNormalization q = p ∧
      f.toNormalization ⁻¹' {q} = f ⁻¹' {p} := by
  have hpre : f ⁻¹' {p} = f.toNormalization ⁻¹' (f.fromNormalization ⁻¹' {p}) := by
    exact congrArg (fun g : X ⟶ Y ↦ g ⁻¹' ({p} : Set Y))
      f.toNormalization_fromNormalization.symm
  have himage : f.toNormalization '' (f ⁻¹' {p}) = f.fromNormalization ⁻¹' {p} := by
    rw [hpre]
    exact Set.image_preimage_eq _ f.toNormalization.surjective
  have hC := hp.image f.toNormalization f.toNormalization.continuous.continuousOn
  rw [himage] at hC
  obtain ⟨q, hq⟩ := hC.nonempty
  have hs := hC.isPreconnected.isDiscrete_iff_subsingleton.mp
    (f.fromNormalization.isDiscrete_preimage_singleton p)
  have heq := hs.eq_singleton_of_mem hq
  refine ⟨q, hq, ?_⟩
  rw [hpre, heq]

/-- If a fiber of a proper morphism is connected and has more than one point, and
the morphism is quasi-finite off it, the source map of a finite relative normalization
has a single point in its non-isomorphism locus. The fiber over that point is the
original exceptional fiber. -/
theorem exists_centre_eq_singleton_toNormalization [IsFinite f.fromNormalization]
    {p : Y} (hp : _root_.IsConnected (f ⁻¹' {p})) (hn : ¬ (f ⁻¹' {p}).Subsingleton)
    (hq : ∀ x, f x ≠ p → f.QuasiFiniteAt x) :
    ∃ q : f.normalization, f.toNormalization ⁻¹' {q} = f ⁻¹' {p} ∧
      f.toNormalization.centre = {q} := by
  obtain ⟨q, _, hfiber⟩ := f.exists_preimage_singleton_toNormalization_of_isConnected hp
  refine ⟨q, hfiber, Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · rw [centre_def, Set.mem_compl_iff]
    intro hqIso
    apply hn
    rw [← hfiber]
    intro a ha b hb
    have ha' : f.toNormalization a = q := ha
    have hb' : f.toNormalization b = q := hb
    exact f.toNormalization.injOn_preimage_isoLocus
      (Set.mem_preimage.mpr (ha'.symm ▸ hqIso)) (Set.mem_preimage.mpr (hb'.symm ▸ hqIso))
      (ha'.trans hb'.symm)
  · intro y hy
    by_contra hne
    obtain ⟨x, rfl⟩ := f.toNormalization.surjective y
    have hx : x ∉ f ⁻¹' {p} := hfiber ▸ hne
    obtain ⟨U, hxU, hU⟩ := f.exists_mem_and_isIso_morphismRestrict_toNormalization x (hq x hx)
    rw [centre_def, Set.mem_compl_iff] at hy
    exact hy ((f.toNormalization.le_isoLocus_iff.mpr hU) hxU)

end Modification

end AlgebraicGeometry.Scheme.Hom
