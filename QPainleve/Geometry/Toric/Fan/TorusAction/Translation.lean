/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.FunctionField
public import TauCeti.Algebra.MonoidAlgebra.CharacterTwist
public import TauCeti.Geometry.Toric.Algebraic.Fan.TorusAction.Action

import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import QPainleve.Algebra.AlgebraicGroup.Hopf.SchemeTranslation
import QPainleve.Geometry.Toric.Fan.Separated
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic
import TauCeti.Geometry.Toric.Algebraic.TorusAction.Action

/-!
# Translations on toric fan schemes

Specializing the native torus action at a complex point gives an automorphism.
On the zero-cone chart its pullback is the character twist, so it scales each
rational character by its value at the translating point. The twist comparison
uses the shared translation formula for spectra with group-like coordinates.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open SemiCartesianMonoidalCategory
open Multiplicative

namespace TauCeti.Toric.Fan

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

local notation "R" => affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V)
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "T" => (Φ.denseTorus.asOver S)
local notation "X" => (Φ.algebraicRealization.asOver S)
local notation "Chars" => (Multiplicative (N →+ ℤ) →* ℂˣ)

private def evaluation (χ : Chars) : R →ₐ[ℂ] ℂ :=
  (DiagonalizableGroup.point χ).comp (denseTorusCoordinateRingEquiv Φ.lattice).toAlgHom

private def twist (χ : Chars) : R ≃ₐ[ℂ] R :=
  MonoidAlgebra.charTwist (χ.comp (denseTorusDualEquiv Φ.lattice).toMultiplicative.toMonoidHom)

private def torusPoint (χ : Chars) : 𝟙_ (Over S) ⟶ T :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Φ.evaluation χ).toRingHom)) (by
    -- Display the structure maps of the two affine objects in the over category.
    change Spec.map (CommRingCat.ofHom (Φ.evaluation χ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ R)) = 𝟙 S
    rw [← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map (CommRingCat.hom_ext ((Φ.evaluation χ).comp_algebraMap)))

private def translate (χ : Chars) : X ⟶ X :=
  (toUnit X ≫ Φ.torusPoint χ) • 𝟙 X

private theorem denseTorus_twist_eq_mul (χ : Chars) :
    ((Spec.map (CommRingCat.ofHom (Φ.twist χ).toAlgHom.toRingHom)).asOver S : T ⟶ T) =
      (toUnit T ≫ Φ.torusPoint χ) * 𝟙 T := by
  refine QPainleve.specMap_eq_mul_of_groupLike_basis (MonoidAlgebra.basis _ ℂ)
    (fun m ↦ by simp) (Φ.evaluation χ) (Φ.twist χ).toAlgHom ?_ (Φ.torusPoint χ) rfl
  intro m
  obtain ⟨a, rfl⟩ : ∃ a, ofAdd a = m := ⟨m.toAdd, ofAdd_toAdd m⟩
  simp [twist, evaluation, denseTorusDualEquiv_apply, MonoidAlgebra.smul_single]

variable [Nonempty Φ.cones]

private theorem denseTorusι_comp_translate (χ : Chars) :
    Φ.denseTorusι inferInstance ≫ (Φ.translate χ).left =
      Spec.map (CommRingCat.ofHom (Φ.twist χ).toAlgHom.toRingHom) ≫
        Φ.denseTorusι inferInstance := by
  have hbot := Φ.bot_mem (Classical.choice (inferInstance : Nonempty Φ.cones)).property
  rw [Φ.denseTorusι_eq_affineToricChartι _ hbot]
  let j : T ⟶ X := (Φ.affineToricChartι ⟨⊥, hbot⟩).asOver S
  let : IsModHom T j := Φ.isModHom_affineToricChartι ⟨⊥, hbot⟩
  have he : j ≫ Φ.translate χ =
      (Spec.map (CommRingCat.ofHom (Φ.twist χ).toAlgHom.toRingHom)).asOver S ≫ j := by
    rw [Φ.denseTorus_twist_eq_mul, translate, ModObj.comp_smul,
      comp_toUnit_assoc, Category.comp_id]
    have hh := IsModHom.map_smul j (toUnit T ≫ Φ.torusPoint χ) (𝟙 T)
    -- The module structure on the source chart is the zero-cone action.
    change (lift (toUnit T ≫ Φ.torusPoint χ) (𝟙 T) ≫
      (affineToricSchemeModObj Φ.lattice ⊥).smul) ≫ j = _ at hh
    rw [affineToricSchemeModObj_bot, ModObj.smul_eq_mul] at hh
    -- Multiplication on the torus is the action of its regular module.
    change _ = (lift (toUnit T ≫ Φ.torusPoint χ) (𝟙 T) ≫ μ[T]) ≫ j
    simpa only [Category.id_comp] using hh.symm
  exact congrArg (fun f ↦ f.left) he

private theorem translate_comp (χ ψ : Chars) :
    Φ.translate χ ≫ Φ.translate ψ = Φ.translate (χ * ψ) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  -- The component maps of over-morphisms live on the fan scheme itself.
  let f : Φ.algebraicRealization ⟶ Φ.algebraicRealization := (Φ.translate χ).left
  let g : Φ.algebraicRealization ⟶ Φ.algebraicRealization := (Φ.translate ψ).left
  let h : Φ.algebraicRealization ⟶ Φ.algebraicRealization := (Φ.translate (χ * ψ)).left
  have hf : Φ.denseTorusι inferInstance ≫ f = _ := Φ.denseTorusι_comp_translate χ
  have hg : Φ.denseTorusι inferInstance ≫ g = _ := Φ.denseTorusι_comp_translate ψ
  have hh : Φ.denseTorusι inferInstance ≫ h = _ := Φ.denseTorusι_comp_translate (χ * ψ)
  suffices f ≫ g = h from this
  apply AlgebraicGeometry.ext_of_isDominant (Φ.denseTorusι inferInstance)
  rw [← Category.assoc, hf, Category.assoc, hg, hh, ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  -- Composition of the twists multiplies the two characters, which commute.
  exact RingHom.ext fun f ↦ by
    simp [twist, MonoidAlgebra.charTwist_charTwist, MonoidHom.mul_comp]

private theorem translate_one : Φ.translate (1 : Chars) = 𝟙 X := by
  apply Over.OverMorphism.ext
  rw [Over.id_left]
  let f : Φ.algebraicRealization ⟶ Φ.algebraicRealization := (Φ.translate 1).left
  have hf : Φ.denseTorusι inferInstance ≫ f = _ := Φ.denseTorusι_comp_translate 1
  suffices f = 𝟙 Φ.algebraicRealization from this
  apply AlgebraicGeometry.ext_of_isDominant (Φ.denseTorusι inferInstance)
  rw [hf]
  simp [twist, MonoidAlgebra.charTwist_one]

private def torusTranslationOver (χ : Chars) : X ≅ X where
  hom := Φ.translate χ
  inv := Φ.translate χ⁻¹
  hom_inv_id := by rw [translate_comp, (mul_inv_cancel χ : χ * χ⁻¹ = 1), translate_one]
  inv_hom_id := by rw [translate_comp, (inv_mul_cancel χ : χ⁻¹ * χ = 1), translate_one]

/-- Translation of the fan scheme by the torus point with character values `χ`. -/
def torusTranslation (χ : Chars) : Φ.algebraicRealization ≅ Φ.algebraicRealization :=
  (Over.forget S).mapIso (Φ.torusTranslationOver χ)

/-- The torus translation is a morphism over the complex base. -/
instance isOver_torusTranslation_hom (χ : Chars) :
    (Φ.torusTranslation χ).hom.IsOver S :=
  ⟨Over.w (Φ.torusTranslationOver χ).hom⟩

/-- Unit translation is the identity. -/
@[simp]
theorem torusTranslation_one : Φ.torusTranslation 1 = Iso.refl Φ.algebraicRealization :=
  Iso.ext (congrArg (fun f : X ⟶ X ↦ f.left) (Φ.translate_one))

/-- Composing translations multiplies the translating torus points. -/
theorem torusTranslation_trans (χ ψ : Chars) :
    Φ.torusTranslation χ ≪≫ Φ.torusTranslation ψ = Φ.torusTranslation (χ * ψ) :=
  Iso.ext (congrArg (fun f : X ⟶ X ↦ f.left) (Φ.translate_comp χ ψ))

/-- The inverse translation uses the inverse torus point. -/
@[simp]
theorem torusTranslation_symm (χ : Chars) :
    (Φ.torusTranslation χ).symm = Φ.torusTranslation χ⁻¹ :=
  Iso.ext (congrArg (fun f : X ⟶ X ↦ f.left) (rfl :
    (Φ.torusTranslationOver χ).inv = (Φ.torusTranslationOver χ⁻¹).hom))

/-- On the dense torus translation is the spectrum map of the corresponding
character twist of the zero-cone coordinate ring. -/
theorem denseTorusι_comp_torusTranslation_hom (χ : Chars) :
    Φ.denseTorusι inferInstance ≫ (Φ.torusTranslation χ).hom =
      Spec.map (CommRingCat.ofHom (MonoidAlgebra.charTwist
        (χ.comp (denseTorusDualEquiv Φ.lattice).toMultiplicative.toMonoidHom)).toAlgHom.toRingHom) ≫
          Φ.denseTorusι inferInstance :=
  Φ.denseTorusι_comp_translate χ

/-- Translation pulls back a rational character to that character times its value at
the translating point. -/
@[simp]
theorem functionFieldMap_torusTranslation_character (χ : Chars)
    (m : Multiplicative (N →+ ℤ)) :
    (Φ.torusTranslation χ).hom.functionFieldMap (Φ.character m) =
      algebraMap ℂ Φ.algebraicRealization.functionField (χ m : ℂ) * Φ.character m := by
  let j := Φ.denseTorusι inferInstance
  let a := CommRingCat.ofHom (Φ.twist χ).toAlgHom.toRingHom
  let q := Spec.map a
  have : IsIso q := (Scheme.Spec.mapIso (Φ.twist χ).toRingEquiv.toCommRingCatIso.op).isIso_hom
  let t := (Φ.torusTranslation χ).hom
  have : IsIso t := (Φ.torusTranslation χ).isIso_hom
  have ht : j ≫ t = q ≫ j := Φ.denseTorusι_comp_translate χ
  have hcomp : t.functionFieldMap ≫ j.functionFieldMap =
      j.functionFieldMap ≫ q.functionFieldMap := by
    calc
      _ = (j ≫ t).functionFieldMap := (Scheme.Hom.functionFieldMap_comp j t).symm
      _ = (q ≫ j).functionFieldMap := by
        rw [Scheme.Hom.eq_functionFieldMap_iff, Scheme.Hom.SpecMap_functionFieldMap_fromSpecStalk,
          ht]
      _ = _ := Scheme.Hom.functionFieldMap_comp q j
  have hnat : (Scheme.ΓSpecIso (.of R)).inv ≫ Φ.denseTorus.germToFunctionField ⊤ ≫
      q.functionFieldMap = a ≫ (Scheme.ΓSpecIso (.of R)).inv ≫
        Φ.denseTorus.germToFunctionField ⊤ := by
    have hq : Φ.denseTorus.germToFunctionField ⊤ ≫ q.functionFieldMap =
        q.appTop ≫ Φ.denseTorus.germToFunctionField ⊤ :=
      q.germToFunctionField_functionFieldMap ⊤
    rw [hq, ← Scheme.ΓSpecIso_inv_naturality_assoc a]
  apply j.functionFieldMap.hom.injective
  rw [← CommRingCat.comp_apply, hcomp, CommRingCat.comp_apply, map_mul,
    j.functionFieldMap_algebraMap ℂ, Φ.functionFieldMap_character, ← CommRingCat.comp_apply,
    Category.assoc, hnat, CommRingCat.comp_apply, Scheme.Spec.algebraMap_functionField_base]
  have ha : a (MonoidAlgebra.of ℂ _ (ofAdd ((denseTorusDualEquiv Φ.lattice).symm m.toAdd))) =
      algebraMap ℂ R (χ m : ℂ) *
        MonoidAlgebra.of ℂ _ (ofAdd ((denseTorusDualEquiv Φ.lattice).symm m.toAdd)) := by
    simp [a, twist]
  rw [ha, map_mul]

variable {Φ}

/-- Pullback by translation preserves the weighted rational character when its
parameter is divided by the translating character value. -/
theorem functionFieldMap_torusTranslation_mul_character (χ : Chars)
    (a : Multiplicative (N →+ ℤ)) (c : ℂˣ) :
    (Φ.torusTranslation χ).hom.functionFieldMap
        (algebraMap ℂ Φ.algebraicRealization.functionField (↑(c / χ a) : ℂ) * Φ.character a) =
      algebraMap ℂ Φ.algebraicRealization.functionField (c : ℂ) * Φ.character a := by
  rw [map_mul, Scheme.Hom.functionFieldMap_algebraMap ℂ,
    Φ.functionFieldMap_torusTranslation_character, ← _root_.mul_assoc, ← map_mul, ← Units.val_mul,
    div_mul_cancel]

/-- On every affine chart, translation is induced by twisting monomials by their
character values. -/
theorem affineToricChartι_comp_torusTranslation_hom (χ : Chars) (σ : Φ.cones) :
    Φ.affineToricChartι σ ≫ (Φ.torusTranslation χ).hom =
      Spec.map (CommRingCat.ofHom (MonoidAlgebra.charTwist
        (χ.comp (dualSemigroup Φ.lattice σ.val).subtype.toMultiplicative)).toAlgHom.toRingHom) ≫
        Φ.affineToricChartι σ := by
  let hface := (Φ.isToricCone σ.property).salient.bot_isFaceOf
  let j := faceAffineToricSchemeMap Φ.lattice hface
  have : IsDominant j := isDominant_faceAffineToricSchemeMap _ _
  apply AlgebraicGeometry.ext_of_isDominant j
  dsimp only [j]
  rw [← Category.assoc, ← Φ.denseTorusι_face σ, Φ.denseTorusι_comp_torusTranslation_hom χ,
    Φ.denseTorusι_face σ, ← Category.assoc, ← Category.assoc, faceAffineToricSchemeMap_def,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  let res := faceAffineCoordinateRingMap Φ.lattice hface
  have heq : (MonoidAlgebra.charTwist
      (χ.comp (denseTorusDualEquiv Φ.lattice).toMultiplicative.toMonoidHom)).toAlgHom.comp res =
      res.comp (MonoidAlgebra.charTwist
        (χ.comp (dualSemigroup Φ.lattice σ.val).subtype.toMultiplicative)).toAlgHom := by
    apply MonoidAlgebra.algHom_ext
    · intro a
      obtain ⟨a, rfl⟩ := ofAdd.surjective a
      simp [res, denseTorusDualEquiv_apply]
    · apply AlgHom.ext
      intro z
      have hz : MonoidAlgebra.single 1 z = algebraMap ℂ (affineCoordinateRing Φ.lattice σ.val) z :=
        (rfl)
      simp only [AlgHom.comp_apply, MonoidAlgebra.singleOneAlgHom_apply, hz, AlgHom.commutes]
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom heq)

end TauCeti.Toric.Fan
