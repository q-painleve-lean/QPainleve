/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Degree.Normalization
public import TauCeti.AlgebraicGeometry.Curves.Degree.Pullback
import TauCeti.AlgebraicGeometry.Curves.Normalization
import QPainleve.AlgebraicGeometry.Curves.Morphism

/-!
# Pullback of degrees on integral curves

A dominant morphism of proper integral curves multiplies degrees by a positive integer.
The normalization comparison reduces the proof to the projection formula for a regular
target, so the result also applies to singular curves.

See [Stacks Project, Lemma 33.44.4](https://stacks.math.columbia.edu/tag/0AYU).
-/

public section

open AlgebraicGeometry CategoryTheory Limits TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.LineBundleClass

variable {k : Type u} [Field k] {C D : Scheme.{u}}
  [C.Over (Spec (.of k))] [D.Over (Spec (.of k))]
  [C.IsCurveOver k] [D.IsCurveOver k]

/-- A dominant map of proper integral curves multiplies degrees by a fixed positive integer,
including when the source or the target is singular. -/
theorem exists_pos_eulerDegree_pullback (g : C ⟶ D)
    [g.IsOver (Spec (.of k))] [IsDominant g] :
    ∃ n : ℕ, 0 < n ∧ ∀ a : LineBundleClass D,
      eulerDegree k (pullback g a) = n * eulerDegree k a := by
  let c := C.fromSpecStalk (genericPoint C)
  let d := D.fromSpecStalk (genericPoint D)
  let νC := c.fromNormalization
  let νD := d.fromNormalization
  let : c.normalization.Over (Spec (.of k)) := ⟨νC ≫ C ↘ Spec (.of k)⟩
  let : d.normalization.Over (Spec (.of k)) := ⟨νD ≫ D ↘ Spec (.of k)⟩
  have : νC.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : νD.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : c.normalization.IsCurveOver k := Scheme.IsCurveOver.isCurveOver_normalization k
  have : d.normalization.IsCurveOver k := Scheme.IsCurveOver.isCurveOver_normalization k
  have : IsRegular d.normalization := Scheme.IsCurveOver.isRegular_normalization k
  have (y : CodimensionOnePoint d.normalization) :
      IsDiscreteValuationRing (d.normalization.presheaf.stalk (y : d.normalization)) :=
    inferInstance
  have (y : d.normalization) : ValuationRing (d.normalization.presheaf.stalk y) :=
    Scheme.IsCurveOver.valuationRing_stalk k _ y
  -- Lift the generic point to the pullback of the target normalization, then use
  -- integrality of the pullback projection to extend it across the source normalization.
  let φ := Spec.map g.functionFieldMap ≫ d.toNormalization
  have hφ : c ≫ g = φ ≫ νD := by
    simp [φ, νD, c, d, Scheme.Hom.SpecMap_functionFieldMap_fromSpecStalk]
  let ψ := pullback.lift c φ hφ
  have hψ : c = ψ ≫ pullback.fst g νD := (pullback.lift_fst _ _ _).symm
  let h := c.normalizationDesc ψ (pullback.fst g νD) hψ ≫ pullback.snd g νD
  have hw : h ≫ νD = νC ≫ g := by
    rw [Category.assoc, ← pullback.condition,
      ← Category.assoc, Scheme.Hom.normalizationDesc_comp]
  have : h.IsOver (Spec (.of k)) := ⟨by
    rw [← comp_over νD (Spec (.of k)), ← Category.assoc, hw, Category.assoc,
      comp_over g (Spec (.of k)), comp_over νC (Spec (.of k))]⟩
  have : IsDominant h := by
    have hgeneric := c.toNormalization_normalizationDesc ψ (pullback.fst g νD) hψ
    have heq : c.toNormalization ≫ h = φ := by simp [h, ← Category.assoc, hgeneric, ψ]
    have : IsDominant φ := by dsimp [φ, d]; infer_instance
    have : IsDominant (c.toNormalization ≫ h) := heq ▸ inferInstance
    exact IsDominant.of_comp c.toNormalization h
  have : IsFinite h := h.isFinite_of_isDominant_of_isCurveOver (k := k)
  have : RelativeDimensionLE 1 (d.normalization ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  have : Flat h := h.flat_of_isDominant_of_valuationRing
  let y := genericPoint d.normalization
  have hpos : 0 < h.finrank y := Nat.pos_of_ne_zero fun hz ↦
    (h.finrank_eq_zero_iff_notMem_range y).mp hz
      ⟨genericPoint c.normalization, h.genericPoint_eq_of_isDominant⟩
  refine ⟨h.finrank y, hpos, fun a ↦ ?_⟩
  rw [← eulerDegree_pullback_normalization k (pullback g a), pullback_comp,
    ← hw, ← pullback_comp, eulerDegree_pullback_of_isDominant k h,
    eulerDegree_pullback_normalization k, h.finrank_eq_finrank_fieldRange_functionFieldMap]

end TauCeti.AlgebraicGeometry.LineBundleClass
