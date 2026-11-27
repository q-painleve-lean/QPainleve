/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Instances
public import QPainleve.Algebra.MonoidAlgebra.CharacterTwist
public import QPainleve.Geometry.Toric.BaseChange.FunctionField

import QPainleve.AlgebraicGeometry.Scheme.FunctionField

/-!
# Torus translations over a coefficient ring

A unit-valued character twists the monomials of every affine cone chart.
The twists commute with face localization and glue to an automorphism of the fan scheme.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra Multiplicative

namespace TauCeti.Toric.Fan

universe u

variable (R : Type u) [CommRing R] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V} (Φ : Fan i)

local notation "Chars" => (Multiplicative (N →+ ℤ) →* Rˣ)

local notation "twist[" χ "," σ "]" => AddMonoidAlgebra.charTwist
  (MonoidHom.comp χ (AddMonoidHom.toMultiplicative
    (AddSubmonoid.subtype (dualSemigroup Φ.lattice (Subtype.val σ)))))

private def chartTranslate (χ : Chars) (σ : Φ.cones) :
    affineChart R Φ.lattice σ.val ⟶ affineChart R Φ.lattice σ.val :=
  Spec.map (CommRingCat.ofHom (twist[χ, σ]).toAlgHom.toRingHom)

private theorem faceAffineChartMap_comp_chartTranslate (χ : Chars) {τ σ : Φ.cones}
    (h : τ.val.IsFaceOf σ.val) :
    faceAffineChartMap R Φ.lattice h ≫ Φ.chartTranslate R χ σ =
      Φ.chartTranslate R χ τ ≫ faceAffineChartMap R Φ.lattice h := by
  rw [chartTranslate, chartTranslate, faceAffineChartMap_def,
    ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  change ((faceAffineChartRingMap R Φ.lattice h).comp
      (twist[χ, σ]).toAlgHom).toRingHom =
    ((twist[χ, τ]).toAlgHom.comp (faceAffineChartRingMap R Φ.lattice h)).toRingHom
  apply congrArg AlgHom.toRingHom
  apply AddMonoidAlgebra.algHom_ext
  · intro m
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AddMonoidAlgebra.charTwist_single, faceAffineChartRingMap_single]
    rfl
  · exact Subsingleton.elim _ _

private theorem chartTranslate_compatible (χ : Chars) {τ σ : Φ.cones} (h : τ ≤ σ) :
    faceAffineChartMap R Φ.lattice (Φ.isFaceOf_of_le σ.property τ.property h) ≫
        (Φ.chartTranslate R χ σ ≫ Φ.affineChartι R σ) =
      Φ.chartTranslate R χ τ ≫ Φ.affineChartι R τ := by
  let hf := Φ.isFaceOf_of_le σ.property τ.property h
  rw [← Category.assoc, Φ.faceAffineChartMap_comp_chartTranslate R χ hf,
    Category.assoc, Φ.faceAffineChartMap_comp_affineChartι R hf]

private def translateBy (χ : Chars) : Φ.finiteFanScheme R ⟶ Φ.finiteFanScheme R :=
  Φ.finiteFanSchemeDesc R (fun σ ↦ Φ.chartTranslate R χ σ ≫ Φ.affineChartι R σ)
    (Φ.chartTranslate_compatible R χ)

private theorem affineChartι_comp_translateBy (χ : Chars) (σ : Φ.cones) :
    Φ.affineChartι R σ ≫ Φ.translateBy R χ =
      Spec.map (CommRingCat.ofHom (twist[χ, σ]).toAlgHom.toRingHom) ≫
        Φ.affineChartι R σ :=
  Φ.affineChartι_finiteFanSchemeDesc R _ (Φ.chartTranslate_compatible R χ) σ

private theorem translateBy_one : Φ.translateBy R (1 : Chars) = 𝟙 (Φ.finiteFanScheme R) := by
  apply Φ.finiteFanScheme_hom_ext R
  intro σ
  rw [affineChartι_comp_translateBy, Category.comp_id]
  have h : (twist[(1 : Chars), σ]).toAlgHom = AlgHom.id R _ := by
    apply AddMonoidAlgebra.algHom_ext
    · intro m
      simp [AddMonoidAlgebra.charTwist_single]
    · exact Subsingleton.elim _ _
  rw [h]
  simp

private theorem translateBy_comp (χ ψ : Chars) :
    Φ.translateBy R χ ≫ Φ.translateBy R ψ = Φ.translateBy R (χ * ψ) := by
  apply Φ.finiteFanScheme_hom_ext R
  intro σ
  rw [← Category.assoc, affineChartι_comp_translateBy, Category.assoc,
    affineChartι_comp_translateBy, ← Category.assoc, affineChartι_comp_translateBy,
    ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  change ((twist[χ, σ]).toAlgHom.comp
      (twist[ψ, σ]).toAlgHom).toRingHom =
    (twist[(χ * ψ), σ]).toAlgHom.toRingHom
  apply congrArg AlgHom.toRingHom
  apply AddMonoidAlgebra.algHom_ext
  · intro m
    simp
  · exact Subsingleton.elim _ _

/-- The translation automorphism defined by a character with values in coefficient units. -/
def torusTranslationIso (χ : Chars) : Φ.finiteFanScheme R ≅ Φ.finiteFanScheme R where
  hom := Φ.translateBy R χ
  inv := Φ.translateBy R χ⁻¹
  hom_inv_id := by rw [translateBy_comp, (mul_inv_cancel χ : χ * χ⁻¹ = 1), translateBy_one]
  inv_hom_id := by rw [translateBy_comp, (inv_mul_cancel χ : χ⁻¹ * χ = 1), translateBy_one]

/-- Translation is a morphism over the coefficient ring. -/
instance isOver_torusTranslationIso_hom (χ : Chars) :
    (Φ.torusTranslationIso R χ).hom.IsOver (Spec (.of R)) := by
  constructor
  change Φ.translateBy R χ ≫ (Φ.finiteFanScheme R ↘ Spec (.of R)) = _
  rw [finiteFanScheme_over]
  apply Φ.finiteFanScheme_hom_ext R
  intro σ
  rw [← Category.assoc, affineChartι_comp_translateBy, Category.assoc,
    affineChartι_finiteFanSchemeToSpec,
    Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
    (twist[χ, σ]).toAlgHom.comp_algebraMap

/-- Translation restricts to the character twist on each cone chart. -/
@[reassoc]
theorem affineChartι_comp_torusTranslationIso_hom (χ : Chars) (σ : Φ.cones) :
    Φ.affineChartι R σ ≫ (Φ.torusTranslationIso R χ).hom =
      Spec.map (CommRingCat.ofHom (twist[χ, σ]).toAlgHom.toRingHom) ≫
        Φ.affineChartι R σ :=
  Φ.affineChartι_comp_translateBy R χ σ

/-- Translation preserves the points of each affine chart. -/
theorem preimage_range_affineChartι_torusTranslationIso (χ : Chars) (σ : Φ.cones) :
    (Φ.torusTranslationIso R χ).hom ⁻¹' Set.range (Φ.affineChartι R σ) =
      Set.range (Φ.affineChartι R σ) := by
  let t := (Φ.torusTranslationIso R χ).hom
  let j := Φ.affineChartι R σ
  let q := Scheme.Spec.mapIso (twist[χ, σ]).toRingEquiv.toCommRingCatIso.op
  have hcomp : j ≫ t = q.hom ≫ j := Φ.affineChartι_comp_torusTranslationIso_hom R χ σ
  have hrange : t '' Set.range j = Set.range j := by
    rw [← Set.range_comp, ← show ⇑(j ≫ t) = ⇑t ∘ ⇑j from funext (Scheme.Hom.comp_apply j t),
      hcomp, show ⇑(q.hom ≫ j) = ⇑j ∘ ⇑q.hom from funext (Scheme.Hom.comp_apply q.hom j)]
    exact q.hom.surjective.range_comp j
  exact (congrArg (Set.preimage t) hrange.symm).trans
    (t.injective.preimage_image (Set.range j))

/-- Translation by the identity character is the identity. -/
@[simp]
theorem torusTranslationIso_one :
    Φ.torusTranslationIso R (1 : Chars) = Iso.refl (Φ.finiteFanScheme R) :=
  Iso.ext (Φ.translateBy_one R)

/-- Composing translations multiplies the characters. -/
theorem torusTranslationIso_trans (χ ψ : Chars) :
    Φ.torusTranslationIso R χ ≪≫ Φ.torusTranslationIso R ψ =
      Φ.torusTranslationIso R (χ * ψ) :=
  Iso.ext (Φ.translateBy_comp R χ ψ)

/-- The inverse translation uses the inverse character. -/
@[simp]
theorem torusTranslationIso_symm (χ : Chars) :
    (Φ.torusTranslationIso R χ).symm = Φ.torusTranslationIso R χ⁻¹ :=
  Iso.ext rfl

section FunctionField

variable [IsDomain R] [Nonempty Φ.cones]

/-- The pullback of a rational character is scaled by its value at the translating point. -/
theorem functionFieldMap_torusTranslationIso_character (χ : Chars)
    (m : N →+ ℤ) :
    (Φ.torusTranslationIso R χ).hom.functionFieldMap (Φ.functionFieldCharacter R (ofAdd m)) =
      algebraMap R (Φ.finiteFanScheme R).functionField (χ (ofAdd m) : R) *
        Φ.functionFieldCharacter R (ofAdd m) := by
  let hb := Φ.bot_mem (inferInstance : Nonempty Φ.cones).some.property
  let σ : Φ.cones := ⟨⊥, hb⟩
  let B := CommRingCat.of (affineChartRing R Φ.lattice (⊥ : PointedCone ℝ V))
  let j : Spec B ⟶ Φ.finiteFanScheme R := Φ.affineChartι R σ
  let b := CommRingCat.ofHom (twist[χ, σ]).toAlgHom.toRingHom
  let q := Spec.map b
  have : IsIso q := (Scheme.Spec.mapIso
    (twist[χ, σ]).toRingEquiv.toCommRingCatIso.op).isIso_hom
  let t := (Φ.torusTranslationIso R χ).hom
  have ht : j ≫ t = q ≫ j := Φ.affineChartι_comp_translateBy R χ σ
  have : j.IsOver (Spec (.of R)) := Φ.isOver_affineChartι R σ
  let : IsDominant j := isDominant_of_isOpenImmersion j
  let : Algebra B (Spec B).functionField := instAlgebraCarrierFunctionFieldSpec B
  let m' : dualSemigroup Φ.lattice (⊥ : PointedCone ℝ V) := ⟨m, by simp⟩
  let c : R := χ (ofAdd m)
  apply j.functionFieldMap.hom.injective
  change j.functionFieldMap (t.functionFieldMap (Φ.functionFieldCharacter R (ofAdd m))) =
    j.functionFieldMap (algebraMap R (Φ.finiteFanScheme R).functionField c *
      Φ.functionFieldCharacter R (ofAdd m))
  have hcomp : t.functionFieldMap ≫ j.functionFieldMap = j.functionFieldMap ≫ q.functionFieldMap :=
    (Scheme.Hom.functionFieldMap_comp j t).symm.trans
      ((Scheme.Hom.functionFieldMap_congr ht).trans (Scheme.Hom.functionFieldMap_comp q j))
  have hchar : j.functionFieldMap (Φ.functionFieldCharacter R (ofAdd m)) =
      algebraMap B (Spec B).functionField (single m' 1) :=
    Φ.functionFieldMap_affineChartι_bot_character R m hb
  rw [← CommRingCat.comp_apply, hcomp, CommRingCat.comp_apply, map_mul,
    j.functionFieldMap_algebraMap R, hchar, Scheme.Hom.functionFieldMap_SpecMap_algebraMap]
  have hbmono : b (single m' (1 : R)) = single m' c := by
    change twist[χ, σ] (single m' 1) = _
    rw [AddMonoidAlgebra.charTwist_single, mul_one]
    rfl
  rw [hbmono]
  have hc : algebraMap R (Spec B).functionField c =
      algebraMap B (Spec B).functionField (algebraMap R B c) := by
    rw [Scheme.Spec.algebraMap_functionField_base, Scheme.ΓSpecIso_inv]
    rfl
  rw [hc, ← map_mul]
  change _ = algebraMap B (Spec B).functionField (single 0 c * single m' 1)
  rw [single_mul_single, zero_add, mul_one]

end FunctionField

end TauCeti.Toric.Fan
