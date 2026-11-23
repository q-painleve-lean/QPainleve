/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.FunctionField
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra

import TauCeti.AlgebraicGeometry.Morphisms.FiniteType
import TauCeti.AlgebraicGeometry.Scheme.SpecOver

/-!
# Rational maps to affine schemes

A homomorphism from a finite type coordinate algebra to the function field of an
integral scheme defines a rational map to the spectrum of the algebra. This also
handles maps with image in a proper closed subscheme of the affine target.
-/

public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.RationalMap

universe u

variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  {X Y : Scheme.{u}} [IsIntegral X] [X.Over (Spec (.of k))]

private theorem specMap_toRingHom_comp_algebraMap (φ : A →ₐ[k] X.functionField) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.algebraMap k A =
      X.fromSpecStalk (genericPoint X) ≫ X ↘ Spec (.of k) := by
  rw [X.fromSpecStalk_genericPoint_comp_over (k := k)]
  simpa only [Spec.homEquivAlgHom_symm_apply_val] using (Spec.homEquivAlgHom.symm φ).property

variable [Algebra.FiniteType k A]

/-- The rational map to an affine scheme determined by a homomorphism to the generic stalk. -/
def ofAffineAlgHom (φ : A →ₐ[k] X.functionField) : X ⤏ Spec (.of A) :=
  (equivFunctionFieldOver (X ↘ Spec (.of k)) (Spec.algebraMap k A)
    ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), specMap_toRingHom_comp_algebraMap φ⟩).val

instance (φ : A →ₐ[k] X.functionField) :
    (ofAffineAlgHom φ).IsOver (X ↘ Spec (.of k)) (Spec.algebraMap k A) :=
  ((equivFunctionFieldOver (X ↘ Spec (.of k)) (Spec.algebraMap k A))
    ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), specMap_toRingHom_comp_algebraMap φ⟩).property

/-- At the generic point the affine rational map is the spectrum of its defining homomorphism. -/
@[simp]
theorem fromFunctionField_ofAffineAlgHom (φ : A →ₐ[k] X.functionField) :
    (ofAffineAlgHom φ).fromFunctionField = Spec.map (CommRingCat.ofHom φ.toRingHom) :=
  congrArg Subtype.val
    (Equiv.symm_apply_apply (equivFunctionFieldOver (X ↘ Spec (.of k)) (Spec.algebraMap k A)) _)

/-- A dominant morphism into the source pulls back an affine rational map by composition
with the homomorphism on function fields. -/
theorem comp_ofAffineAlgHom [IsIntegral Y] [Y.Over (Spec (.of k))]
    (f : Y ⟶ X) [IsDominant f] [f.IsOver (Spec (.of k))]
    (φ : A →ₐ[k] X.functionField) :
    f.toRationalMap.comp (ofAffineAlgHom φ) =
      ofAffineAlgHom ((f.functionFieldAlgHom k).comp φ) := by
  apply eq_of_fromFunctionField_eq
  rw [fromFunctionField_comp, Hom.functionFieldMap_toRationalMap,
    fromFunctionField_ofAffineAlgHom, fromFunctionField_ofAffineAlgHom,
    ← Spec.map_comp, Spec.map_inj]
  ext a
  exact (Hom.functionFieldAlgHom_apply k f (φ a)).symm

/-- Postcomposing an affine rational map by a morphism of spectra precomposes its
coordinate algebra homomorphism. -/
theorem ofAffineAlgHom_compHom [Algebra.FiniteType k B] (φ : A →ₐ[k] X.functionField)
    (g : B →ₐ[k] A) :
    (ofAffineAlgHom φ).compHom (Spec.map (CommRingCat.ofHom g.toRingHom)) =
      ofAffineAlgHom (φ.comp g) := by
  apply eq_of_fromFunctionField_eq
  rw [fromFunctionField_compHom, fromFunctionField_ofAffineAlgHom, fromFunctionField_ofAffineAlgHom,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end AlgebraicGeometry.Scheme.RationalMap
