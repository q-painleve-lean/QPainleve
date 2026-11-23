/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.AlgebraicGeometry.Cohomology.Support
import TauCeti.AlgebraicGeometry.IdealSheaf.EulerCharacteristic

/-!
# Euler characteristics of restriction to an effective Cartier divisor

The exact sequence of an effective Cartier divisor gives the Euler characteristic of
a line bundle restricted to the divisor as a difference on the ambient projective scheme.
This uses the exact sequence and projection formula for the actual closed subscheme,
including its scheme structure. It uses Tau Ceti's `shortExact_tensor_toPushforwardSubscheme`
and `eulerCharBelow_tensor_pushforwardSubscheme`.
-/

open CategoryTheory MonoidalCategory AlgebraicGeometry
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] {I : X.IdealSheafData}

/-- The Euler characteristic of a line bundle splits into that of its twist by the ideal of
an effective Cartier divisor and that of its restriction. The truncation lies above the
dimension of the ambient scheme. -/
public theorem eulerCharBelow_eq_add_restriction (hI : I.IsEffectiveCartier)
    (a : LineBundleClass X) {n : ℕ} (hdim : topologicalKrullDim X < n) :
    LineBundleClass.eulerCharBelow k a n =
      LineBundleClass.eulerCharBelow k (a * LineBundleClass.mk hI.toInvertibleSheaf) n +
      LineBundleClass.eulerCharBelow k (LineBundleClass.pullback I.subschemeι a) n := by
  obtain ⟨L, rfl⟩ := LineBundleClass.mk_surjective a
  let K := L.tensorProduct hI.toInvertibleSheaf
  let e₁ : K.obj ≅ L.obj ⊗ I.sheaf :=
    InvertibleSheaf.tensorProductObjIso _ _ ≪≫
      (tensorLeft L.obj).mapIso (eqToIso hI.toInvertibleSheaf_obj)
  let e₂ : L.obj ⊗ SheafOfModules.unit X.ringCatSheaf ≅ L.obj :=
    (tensorLeft L.obj).mapIso (eqToIso (TauCeti.SheafOfModules.tensorUnit_eq X.sheaf).symm) ≪≫
      ρ_ L.obj
  have := subsingleton_cohomology_of_projective_dim_lt (k := k) K.obj hdim
  have h := eulerCharBelow_eq_add k (I.shortExact_tensor_toPushforwardSubscheme L.obj) n
    (fun i _ _ ↦ (finiteDimensional_cohomology_congr k e₁ i).mp
      (moduleFinite_cohomology_of_isProjectiveOver k K.obj i))
    (fun i _ ↦ (finiteDimensional_cohomology_congr k e₂ i).mpr
      (moduleFinite_cohomology_of_isProjectiveOver k L.obj i))
    (cohomologyBaseLinearEquivOfIso k e₁.symm n).toEquiv.subsingleton
  -- The three terms of the mapped short complex are the tensor products in these comparisons.
  change eulerCharBelow k X (L.obj ⊗ SheafOfModules.unit X.ringCatSheaf) n =
    eulerCharBelow k X (L.obj ⊗ I.sheaf) n +
      eulerCharBelow k X (L.obj ⊗ I.pushforwardSubscheme) n at h
  have h₃ := I.eulerCharBelow_tensor_pushforwardSubscheme k
    ((InvertibleSheaf.toFiniteLocallyFree X).obj L) n
  simp only [FiniteLocallyFreeSheaf.pullback_obj_obj, ObjectProperty.ιOfLE_obj_obj] at h₃
  rw [eulerCharBelow_congr k e₂, ← eulerCharBelow_congr k e₁, h₃] at h
  simpa only [← LineBundleClass.mk_tensorProduct, LineBundleClass.pullback_mk,
    LineBundleClass.eulerCharBelow_mk, InvertibleSheaf.pullback_obj_obj] using h

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
