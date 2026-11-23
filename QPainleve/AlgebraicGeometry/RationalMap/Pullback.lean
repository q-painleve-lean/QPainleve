/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.FunctionField
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra

/-!
# Dominant rational maps and function field homomorphisms

Dominant rational maps pull back function fields contravariantly. Over an affine base, every
base-algebra homomorphism of function fields comes from a unique such rational map when the target
is locally of finite type. The construction uses Mathlib's `RationalMap.equivFunctionFieldOver`
and Tau Ceti's comparison of the structure morphism with the algebra map at the generic point.
-/

public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

variable {X Y Z : Scheme.{u}}

namespace RationalMap

section Algebra

variable (k : Type u) [CommRing k] [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [IsIntegral X] [IsIntegral Y]

/-- Pullback of rational functions along a dominant rational map over an affine base,
as a homomorphism of algebras over the base ring. -/
def functionFieldAlgHom (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] :
    Y.functionField →ₐ[k] X.functionField where
  __ := f.functionFieldMap.hom
  commutes' c := by
    have hOver := RationalMap.isOver_iff.mp
      ‹f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))›
    have h := congrArg RationalMap.fromFunctionField hOver
    rw [← comp_toRationalMap, fromFunctionField_comp] at h
    simp only [fromFunctionField_toRationalMap, PartialMap.fromSpecStalkOfMem_toPartialMap,
      Scheme.fromSpecStalk_genericPoint_comp_over] at h
    rw [← Spec.map_comp, Spec.map_inj] at h
    exact ConcreteCategory.congr_hom h c

/-- The algebra pullback has the same values as the map on generic stalks. -/
@[simp]
theorem functionFieldAlgHom_apply (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))]
    (a : Y.functionField) : f.functionFieldAlgHom k a = f.functionFieldMap a := (rfl)

/-- The algebra pullback of a composite is the reverse composite of the algebra pullbacks. -/
@[simp]
theorem functionFieldAlgHom_comp [Z.Over (Spec (.of k))] [IsIntegral Z] (f : X ⤏ Y) (g : Y ⤏ Z)
    [f.IsDominant] [g.IsDominant] [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))]
    [g.IsOver (Y ↘ Spec (.of k)) (Z ↘ Spec (.of k))] :
    letI := isOver_comp f ‹f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))›
      g ‹g.IsOver (Y ↘ Spec (.of k)) (Z ↘ Spec (.of k))›
    (f.comp g).functionFieldAlgHom k =
      (f.functionFieldAlgHom k).comp (g.functionFieldAlgHom k) := by
  ext a
  simp

/-- A dominant morphism and its rational map induce the same algebra pullback. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Hom.functionFieldAlgHom_toRationalMap
    (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (.of k))] :
    letI : f.toPartialMap.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) :=
      Hom.isOver_toPartialMap (comp_over f (Spec (.of k)))
    letI : f.toRationalMap.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) :=
      RationalMap.isOver_toRationalMap f.toPartialMap _ _
    f.toRationalMap.functionFieldAlgHom k = f.functionFieldAlgHom k := by
  ext a
  simp

variable [LocallyOfFiniteType (Y ↘ Spec (.of k))]

/-- The rational map over an affine base induced by a homomorphism of function fields. -/
def ofFunctionFieldAlgHom (φ : Y.functionField →ₐ[k] X.functionField) : X ⤏ Y :=
  (equivFunctionFieldOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))
    ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y),
      Scheme.specMap_comp_fromSpecStalk_genericPoint_comp_over k
        (CommRingCat.ofHom φ.toRingHom) φ.commutes⟩).val

/-- On the generic point, the rational map induced by a function field homomorphism is its
spectrum followed by the generic point of the target. -/
@[simp]
theorem fromFunctionField_ofFunctionFieldAlgHom (φ : Y.functionField →ₐ[k] X.functionField) :
    (ofFunctionFieldAlgHom k φ).fromFunctionField =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y) :=
  congrArg Subtype.val
    (Equiv.symm_apply_apply (equivFunctionFieldOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))) _)

instance (φ : Y.functionField →ₐ[k] X.functionField) :
    (ofFunctionFieldAlgHom k φ).IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) :=
  Subtype.property (equivFunctionFieldOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) _)

instance (φ : Y.functionField →ₐ[k] X.functionField) :
    (ofFunctionFieldAlgHom k φ).IsDominant := by
  rw [← isDominant_fromFunctionField_iff, fromFunctionField_ofFunctionFieldAlgHom]
  have : Surjective (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    ⟨fun y ↦ ⟨IsLocalRing.closedPoint X.functionField, Subsingleton.elim _ y⟩⟩
  infer_instance

/-- Pulling back along the rational map induced by a function field homomorphism recovers the
homomorphism. -/
@[simp]
theorem functionFieldAlgHom_ofFunctionFieldAlgHom (φ : Y.functionField →ₐ[k] X.functionField) :
    (ofFunctionFieldAlgHom k φ).functionFieldAlgHom k = φ := by
  have h := ((ofFunctionFieldAlgHom k φ).eq_functionFieldMap_iff
    (CommRingCat.ofHom φ.toRingHom)).mpr (fromFunctionField_ofFunctionFieldAlgHom k φ).symm
  ext a
  exact (ConcreteCategory.congr_hom h a).symm

/-- A dominant rational map is recovered from its function field homomorphism. -/
@[simp]
theorem ofFunctionFieldAlgHom_functionFieldAlgHom (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] :
    ofFunctionFieldAlgHom k (f.functionFieldAlgHom k) = f := by
  apply eq_of_fromFunctionField_eq
  rw [fromFunctionField_ofFunctionFieldAlgHom]
  exact f.specMap_functionFieldMap

/-- The identity homomorphism induces the identity rational map. -/
@[simp]
theorem ofFunctionFieldAlgHom_id [LocallyOfFiniteType (X ↘ Spec (.of k))] :
    ofFunctionFieldAlgHom k (AlgHom.id k X.functionField) = RationalMap.id X := by
  have : ((𝟙 X : X ⟶ X).toRationalMap).IsOver (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) :=
    isOver_iff.mpr (id_compHom _)
  simpa only [Hom.functionFieldAlgHom_toRationalMap, Hom.functionFieldAlgHom_id] using
    ofFunctionFieldAlgHom_functionFieldAlgHom k (𝟙 X : X ⟶ X).toRationalMap

/-- Composition of function field homomorphisms induces composition of the corresponding
rational maps in the reverse order. -/
@[simp]
theorem ofFunctionFieldAlgHom_comp [Z.Over (Spec (.of k))] [IsIntegral Z]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    (φ : Y.functionField →ₐ[k] X.functionField) (ψ : Z.functionField →ₐ[k] Y.functionField) :
    ofFunctionFieldAlgHom k (φ.comp ψ) =
      (ofFunctionFieldAlgHom k φ).comp (ofFunctionFieldAlgHom k ψ) := by
  let f := ofFunctionFieldAlgHom k φ
  let g := ofFunctionFieldAlgHom k ψ
  have hf : f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) := inferInstance
  have hg : g.IsOver (Y ↘ Spec (.of k)) (Z ↘ Spec (.of k)) := inferInstance
  have := isOver_comp f hf g hg
  rw [← ofFunctionFieldAlgHom_functionFieldAlgHom k (f.comp g)]
  dsimp only [f, g]
  simp

/-- Dominant rational maps over an affine base correspond contravariantly to homomorphisms
of function fields over the base ring. -/
def equivFunctionFieldAlgHom :
    { f : X ⤏ Y // f.IsDominant ∧ f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) } ≃
      (Y.functionField →ₐ[k] X.functionField) where
  toFun f :=
    letI := f.property.left
    letI := f.property.right
    f.val.functionFieldAlgHom k
  invFun φ := ⟨ofFunctionFieldAlgHom k φ, inferInstance, inferInstance⟩
  left_inv f := by
    have := f.property.left
    have := f.property.right
    exact Subtype.ext (ofFunctionFieldAlgHom_functionFieldAlgHom k f.val)
  right_inv := functionFieldAlgHom_ofFunctionFieldAlgHom k

/-- The forward comparison sends a rational map to its pullback. -/
@[simp]
theorem equivFunctionFieldAlgHom_apply (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] :
    equivFunctionFieldAlgHom k ⟨f, inferInstance, inferInstance⟩ = f.functionFieldAlgHom k :=
  (rfl)

/-- The inverse comparison returns the rational map induced by the homomorphism. -/
@[simp]
theorem equivFunctionFieldAlgHom_symm_apply_val (φ : Y.functionField →ₐ[k] X.functionField) :
    ((equivFunctionFieldAlgHom k).symm φ).val = ofFunctionFieldAlgHom k φ :=
  (rfl)

end Algebra

end RationalMap

end AlgebraicGeometry.Scheme
