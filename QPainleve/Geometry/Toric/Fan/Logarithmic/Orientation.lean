/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Divisor
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Morphism

import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.Geometry.Toric.Fan.Boundary.DualGraph
import QPainleve.Geometry.Toric.Fan.Subdivision.FunctionField

/-!
# Oriented boundaries of logarithmic factorizations

The ray valuations of a logarithmic morphism to a toric surface identify the prime
components of the source boundary. The positive cyclic order of those rays orders
the nodes and the two normalization branches at each node of the source boundary.
Internal blowups leave this boundary curve isomorphic to the subdivided toric
boundary. The construction applies to repeated centers.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative TauCeti QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} [Nonempty Ψ.cones] {X : Scheme}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "B" => (Ψ.boundaryIdeal inferInstance)
local notation "C" => Scheme.IdealSheafData.subscheme B
local notation "ν[" Y "]" => Scheme.IdealSheafData.blowupToBase (Scheme.singularLocus ℂ Y)

variable [X.Over S] {P : X.IdealSheafData} [PrestableFamily (P.subscheme ↘ S)]
  {ι : Type*} (p : ι → (P.subscheme ↘ S).smoothLocus)

private theorem range_numberedComponent_of_boundaryIso
    [PrestableFamily (C ↘ S)] (hΨ : Ψ.IsRegular) (d : C ≅ P.subscheme) [d.hom.IsOver S]
    {n : ℕ} [NeZero n] {ι' : Type*} {q : ι' → (C ↘ S).smoothLocus}
    (W : Scheme.NodalCycleNumbering q n) (j : ZMod n) (r : Ψ.Ray)
    (hw : W.component j = Ψ.boundaryNormalizationComponentEquiv hΨ r) :
    Set.range ((P.subscheme.blowupComponent ((d.mapNodalCycleNumbering W (q := p)).component j)).ι
      ≫ ν[P.subscheme] ≫ P.subschemeι) =
      Set.range (r.boundaryComponentι hΨ ≫ d.hom ≫ P.subschemeι) := by
  let g := (d.singularLocusBlowupIso (R := ℂ)).hom
  let g' := ν[P.subscheme] ≫ P.subschemeι
  have hg : g ≫ g' = ν[C] ≫ d.hom ≫ P.subschemeι := by simp [g, g']
  calc
    _ = g' '' (g '' (W.component j : Set _)) := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
        Scheme.coe_blowupComponent, d.coe_component_mapNodalCycleNumbering]
    _ = Set.range (((C).blowupComponent (W.component j)).ι ≫ ν[C] ≫ d.hom ≫ P.subschemeι) := by
      rw [← Set.image_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, hg,
        ← (C).coe_blowupComponent, ← Scheme.Opens.range_ι, ← Set.range_comp, ← TopCat.coe_comp,
        ← Scheme.Hom.comp_base]
    _ = _ := by
      rw [← Category.assoc ((C).blowupComponent _).ι (ν[C])]
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.image_comp, Scheme.Opens.range_ι, Scheme.coe_blowupComponent]
      rw [congrArg Subtype.val hw]
      have hr := Ψ.range_boundaryNormalizationComponentEquiv hΨ r
      simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
        Scheme.coe_blowupComponent] using
        congrArg (fun s : Set C ↦ P.subschemeι '' (d.hom '' s)) hr

variable (b : Module.Basis (Fin 2) ℤ N) (hΨ : Ψ.IsRegular) (hc : Φ.IsComplete)
  (H : Ψ.IsSubdivision Φ) {m : ℕ} (ρ : Fin m → Ψ.Ray) (u : Fin m → ℂˣ)
  [IsIntegral X] {f : X ⟶ Φ.algebraicRealization} [f.IsOver S]

section

variable [Nonempty Φ.cones] [IsLocallyNoetherian X] [IsDominant f]

include hΨ hc in
/-- A specified logarithmic factorization numbers the actual boundary cycle of the source
starting at any chosen boundary prime. The first branch at node `j` is on the prime for
ray `j` and the second is on the prime for ray `j` + 1. Their primitive ray generators,
recovered from the orders of pulled-back characters, have positive determinant one. -/
theorem exists_oriented_boundary_of_logarithmic_factorization
    (e : (Ψ.internalBlowupTower b ρ u).1 ≅ X)
    (he : e.hom ≫ f = (Ψ.internalBlowupTower b ρ u).2.toTower.toBase ≫ H.toFanHom.algebraicMap)
    (hP : P.comap e.hom = (Ψ.internalBlowupTower b ρ u).2.boundaryι.ker)
    (p₀ : P.boundaryPrimes) :
    ∃ (n : ℕ) (_ : NeZero n) (W : Scheme.NodalCycleNumbering p n)
      (v : ZMod n ≃ Ψ.Ray) (R : Ψ.Ray ≃ P.boundaryPrimes),
      R (v 0) = p₀ ∧
      (∀ (r : Ψ.Ray) (a : N →+ ℤ),
        X.ord (f.functionFieldMap (Φ.character (ofAdd a))) (R r).val = a r.primitiveGenerator) ∧
      ∀ j, b.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
        Set.range ((P.subscheme.blowupComponent (W.component j)).ι ≫
          ν[P.subscheme] ≫ P.subschemeι) = closure {((R (v j)).val : X)} := by
  let A := Ψ.internalBlowupTower b ρ u
  obtain ⟨R, hord, hrange⟩ :=
    exists_equiv_boundaryPrimes_of_toric_internal_factorization b hΨ H ρ u e he hP
  obtain ⟨d, hd⟩ := P.exists_iso_of_comap_eq_ker e A.2.boundaryι hP
  have hdOver : d.hom.IsOver S := ⟨by
    simp only [over_eq_subschemeι_comp, reassoc_of% hd]
    rw [← comp_over f S, reassoc_of% he, WithBoundary.boundaryι_toBase_assoc, comp_over]⟩
  have : PrestableFamily (C ↘ S) := by
    rw [← comp_over d.hom S]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily)
      d.hom _).2 inferInstance
  let r₀ := R.symm p₀
  have : Nonempty Ψ.Ray := ⟨r₀⟩
  let : NeZero (Nat.card Ψ.Ray) := ⟨Nat.card_pos.ne'⟩
  have hc' := H.isComplete_iff.mpr hc
  obtain ⟨v, ⟨hv₀, hv⟩, -⟩ := existsUnique_cyclicRayNumbering b hΨ hc' r₀
  let q : Empty → (C ↘ S).smoothLocus := Empty.elim
  obtain ⟨E, o, w, hw, hw', -⟩ := exists_toric_boundary_dualGraph_cycle hΨ hc' q b v hv
  let W : Scheme.NodalCycleNumbering q (Nat.card Ψ.Ray) := ⟨w, E, o, hw⟩
  refine ⟨_, inferInstance, d.mapNodalCycleNumbering W, v, R, ?_,
    fun r a ↦ ((hord r (R r)).mp rfl) a, fun j ↦ ⟨(hv j).1, ?_⟩⟩
  · exact (congrArg R hv₀).trans (R.apply_symm_apply p₀)
  · have hW : W.component j = Ψ.boundaryNormalizationComponentEquiv hΨ (v j) := by
      simpa only [Scheme.NodalCycleNumbering.component_apply, W] using hw' j
    rw [range_numberedComponent_of_boundaryIso p hΨ d W j (v j) hW, hd]
    exact hrange (v j)

end

variable (hΦ : Φ.IsRegular) [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)]

/-- Recover the positive cycle on the source boundary directly from the pole-divisor
hypothesis. The orders of the two pulled-back coordinate characters on consecutive
components have determinant one in the order of the actual branches. -/
theorem exists_oriented_boundary_of_pullbackTopFormDivisor
    (hf : Scheme.BirationalOver f (𝟙 Φ.algebraicRealization))
    (hP : P.IsEffectiveCartier) (p₀ : P.boundaryPrimes) :
    let _ : Nonempty Φ.cones := hc.nonempty_cones
    let _ : SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S) :=
      ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ S)
    let hD := Φ.isEffectiveCartier_boundaryIdeal hΦ hc
      ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2))
    ∀ (ω : hD.toInvertibleSheaf ≅ canonicalBundle ℂ Φ.algebraicRealization 2)
      (hTotal : ((Φ.boundaryIdeal inferInstance).comap f).IsEffectiveCartier)
      (hRam : let _ := SmoothOfRelativeDimension.smooth 2 (X ↘ S)
        (ramificationIdealSheaf ℂ f).IsEffectiveCartier),
      pullbackTopFormDivisor ℂ f 2 hD ω hTotal hRam = -hP.toCartierDivisor →
    ∃ hDom : IsDominant f,
      let _ : IsDominant f := hDom
      ∃ (n : ℕ) (_ : NeZero n) (W : Scheme.NodalCycleNumbering p n)
        (R : ZMod n ≃ P.boundaryPrimes),
        let order (q : P.boundaryPrimes) (a : Fin 2) :=
          X.ord (f.functionFieldMap (Φ.character (ofAdd (b.coord a).toAddMonoidHom))) q.val
        R 0 = p₀ ∧
        ∀ j, order (R j) 0 * order (R (j + 1)) 1 - order (R j) 1 * order (R (j + 1)) 0 = 1 ∧
          Set.range ((P.subscheme.blowupComponent (W.component j)).ι ≫
            ν[P.subscheme] ≫ P.subschemeι) = closure {((R j).val : X)} := by
  intro _ _ _ hD ω hTotal hRam hdiv
  obtain ⟨Ψ, hΨ, H, m, ρ, u, e, he, hboundary⟩ :=
    exists_toric_internal_factorization_of_pullbackTopFormDivisor b hΦ hc hf hP ω hTotal hRam hdiv
  have : Nonempty Ψ.cones := H.nonempty_cones_of_nonempty hc.nonempty_cones
  have := isModification_internalBlowupTower_toBase b ρ u hΨ
  have : IsDominant (e.hom ≫ f) := by
    rw [he]
    infer_instance
  have hDom : IsDominant f := IsDominant.of_comp e.hom f
  obtain ⟨n, hn, W, v, R, h₀, hord, hcycle⟩ :=
    exists_oriented_boundary_of_logarithmic_factorization p b hΨ hc H ρ u e he hboundary p₀
  refine ⟨hDom, n, hn, W, v.trans R, h₀, fun j ↦ ⟨?_, (hcycle j).2⟩⟩
  let x := (v j).primitiveGenerator
  let y := (v (j + 1)).primitiveGenerator
  calc
    _ = b.repr x 0 * b.repr y 1 - b.repr x 1 * b.repr y 0 :=
      congrArg₂ (· - ·)
        (congrArg₂ (· * ·) (hord (v j) (b.coord 0).toAddMonoidHom)
          (hord (v (j + 1)) (b.coord 1).toAddMonoidHom))
        (congrArg₂ (· * ·) (hord (v j) (b.coord 1).toAddMonoidHom)
          (hord (v (j + 1)) (b.coord 0).toAddMonoidHom))
    _ = 1 := by
      have hdet : b.det ![x, y] = 1 :=
        (b.detDualEquiv_apply x y).symm.trans (hcycle j).1
      rw [mul_comm (b.repr x 1) (b.repr y 0)]
      simpa only [Module.Basis.det_apply, Module.Basis.toMatrix_apply,
        Matrix.det_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one] using hdet

end TauCeti.Toric.Fan
