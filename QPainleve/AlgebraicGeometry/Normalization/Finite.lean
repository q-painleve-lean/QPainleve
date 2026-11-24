/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Normalization.Finite
import TauCeti.AlgebraicGeometry.Morphisms.FiniteType.Basic
import TauCeti.RingTheory.UniversallyJapanese

/-!
# Finiteness of normalization

The normalization in the function field of an integral scheme locally of finite type over a
field is finite. The affine criterion
`TauCeti.AlgebraicGeometry.isFinite_fromNormalization_fromSpecStalk_genericPoint_iff` reduces
this to the fact that domains of finite type over a field are Japanese.

For a dominant morphism quasi-finite at the generic point, the relative normalization is
finite when the target is locally of finite type over a Noetherian universally Japanese ring.
-/

public section

open CategoryTheory TauCeti TauCeti.AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Normalization in the function field of an integral scheme locally of finite type over a
field is finite. -/
theorem isFinite_fromNormalization_fromSpecStalk_genericPoint_of_locallyOfFiniteType
    {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    IsFinite (Y.fromSpecStalk (genericPoint Y)).fromNormalization := by
  apply isFinite_fromNormalization_fromSpecStalk_genericPoint_iff.mpr
  intro U hU hne
  let : Nonempty U := hne
  let : Algebra k Γ(Y, U) :=
    (((p.appLE ⊤ U le_top).hom).comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have : Algebra.FiniteType k Γ(Y, U) := p.finiteType_ΓSpecIso_inv_comp_appLE hU
  let : TauCeti.Ring.IsJapanese Γ(Y, U) :=
    TauCeti.Ring.IsUniversallyJapanese.isJapanese k _
  infer_instance

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f]

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

end

end AlgebraicGeometry.Scheme.Hom
