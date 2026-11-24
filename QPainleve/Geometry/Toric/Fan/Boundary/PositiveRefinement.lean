/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Refinement

import QPainleve.AlgebraicGeometry.Curves.Node.Period.Orientation
import QPainleve.Geometry.Toric.Fan.Boundary.Node
import QPainleve.Geometry.Toric.Fan.Boundary.Period
import QPainleve.Geometry.Toric.Fan.CyclicOrder
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback

/-!
# Positive boundary numberings under toric refinement

The boundary morphism of a regular toric subdivision respects the orientation
determined by a single ordered lattice basis. A ratio of binomial center ideals
on a surviving ray has the same period in the two positive numberings by
`exists_toric_boundary_period_of_cyclicRayNumbering`. Comparing that value
with `Scheme.Hom.IsOrientedCycleSubdivision.period_pullback` determines the
sign of the actual conductor branch order.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory DihedralGroup Module TauCeti.AlgebraicGeometry
open Scheme (NodalCycleNumbering)
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "D[" Φ "]" => Fan.boundaryIdeal Φ inferInstance
local notation "C[" Φ "]" => Scheme.IdealSheafData.subscheme D[Φ]
local notation "ν[" X "]" => Scheme.IdealSheafData.blowupToBase (Scheme.singularLocus ℂ X)
local notation "P[" X "]" => MonoidHom.ker (LineBundleClass.pullbackHom ν[X])

variable (b : Basis (Fin 2) ℤ N) (h : Ψ.IsSubdivision Φ)

local notation "β" => h.boundaryMap hΨ₀ hΦ₀
local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))

section Numberings

variable [PrestableFamily (C[Φ] ↘ S)]
  {γ δ : Type*} {p : γ → (C[Φ] ↘ S).smoothLocus}
  {n : ℕ} [NeZero n]

local instance (X : Scheme) [X.Over S] : (Iso.refl X).hom.IsOver S := by
  rw [Iso.refl_hom]
  infer_instance

private theorem cycleOrientationSign_refl_of_matching_rays
    (hΦ : Φ.IsRegular) (A A' : NodalCycleNumbering p n) (r : ZMod n ≃ Φ.Ray)
    (hA : ∀ j, A.component j = Φ.boundaryNormalizationComponentEquiv hΦ (r j))
    (hA' : ∀ j, A'.component j = Φ.boundaryNormalizationComponentEquiv hΦ (r j))
    (hpos : ∀ j, b.detDualEquiv (r j).primitiveGenerator (r (j + 1)).primitiveGenerator = 1) :
    cycleOrientationSign ((Iso.refl C[Φ]).boundaryCycleAction A A') = 1 := by
  let g := (Iso.refl C[Φ]).boundaryCycleAction A A'
  have hfix (j : ZMod n) : cycleVertexPerm g j = j := by
    have hr := (Iso.refl C[Φ]).apply_componentGenericPoint A A' j
    have hj : A.componentGenericPoint j = A'.componentGenericPoint j := by
      rw [A.componentGenericPoint_def, A'.componentGenericPoint_def, hA, hA']
    simp only [Iso.refl_hom, Scheme.Hom.id_base, TopCat.coe_id, id_eq] at hr
    exact A'.componentGenericPoint_injective (hr.symm.trans hj)
  cases hg : g with
  | r j => simpa only [g, cycleOrientationSign_r] using congrArg cycleOrientationSign hg
  | sr j =>
    have hz := hfix 0
    rw [hg, cycleVertexPerm_sr_apply, sub_zero, neg_eq_zero] at hz
    subst j
    have hone := hfix 1
    rw [hg, cycleVertexPerm_sr_apply, neg_zero, zero_sub] at hone
    have hn := hpos (-1)
    rw [neg_add_cancel, hone, b.detDualEquiv_swap] at hn
    have hz := hpos 0
    simp only [zero_add] at hz
    rw [hz] at hn
    norm_num at hn

private def twoUnit : ℂˣ := Units.mk0 2 (by norm_num)

private theorem twoUnit_ne_inv : twoUnit ≠ twoUnit⁻¹ := by
  intro h
  have hh := congrArg Units.val h
  norm_num [twoUnit] at hh

private theorem preserves_orientation_of_centerRatio
    [PrestableFamily (C[Ψ] ↘ S)] [(β).IsOver S]
    {q : δ → (C[Ψ] ↘ S).smoothLocus} {l : ℕ} [NeZero l]
    (A : NodalCycleNumbering p n) (U W : NodalCycleNumbering q l)
    (hW : (β).IsOrientedCycleSubdivision W A) (x : P[C[Φ]]) (y : P[C[Ψ]])
    (hxy : LineBundleClass.pullback β x.val = y.val)
    (hx : Scheme.nodalPicardCycleMulEquiv A.endpoint_eq x = twoUnit)
    (hy : Scheme.nodalPicardCycleMulEquiv U.endpoint_eq y = twoUnit) :
    (β).IsOrientedCycleSubdivision U A := by
  obtain ⟨hm, hp⟩ := hW.period_pullback x
  have he : (⟨_, hm⟩ : P[C[Ψ]]) = y := Subtype.ext hxy
  rw [he, hx] at hp
  let e := Iso.refl C[Ψ]
  have : e.hom.IsOver S := inferInstanceAs ((Iso.refl C[Ψ]).hom.IsOver S)
  have ht := e.nodalPicardCycleMulEquiv_pullback_boundaryCycleAction U W y
  have hy' : (⟨_, e.pullback_mem_ker_pullback_blowupToBase_singularLocus y⟩ : P[C[Ψ]]) = y :=
    Subtype.ext (by simp [e])
  rw [hy', hy, hp] at ht
  have hsign : cycleOrientationSign (e.boundaryCycleAction U W) = 1 := by
    rcases Int.units_eq_one_or (cycleOrientationSign (e.boundaryCycleAction U W)) with hs | hs
    · exact hs
    · simp only [hs, Units.val_neg, Units.val_one, zpow_neg_one] at ht
      exact (twoUnit_ne_inv ht).elim
  simpa [e] using (e.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one U W hsign).comp hW

variable (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hc : Φ.IsComplete)
  (A : NodalCycleNumbering p n) (r : ZMod n ≃ Φ.Ray)
  (hA : ∀ j, A.component j = Φ.boundaryNormalizationComponentEquiv hΦ (r j))
  (hr : ∀ j, b.detDualEquiv (r j).primitiveGenerator (r (j + 1)).primitiveGenerator = 1 ∧
    ∃ σ : Φ.cones, (r j).toCone ≤ σ ∧ (r (j + 1)).toCone ≤ σ)

omit [PrestableFamily (C[Φ] ↘ S)] in
private theorem pullback_centerRatio (ρ : Φ.Ray) (c d : ℂˣ) :
    LineBundleClass.pullback β
      (LineBundleClass.mk (ρ.internalCenter b c).property.toInvertibleSheaf /
        LineBundleClass.mk (ρ.internalCenter b d).property.toInvertibleSheaf) =
      LineBundleClass.mk ((h.liftRay ρ).internalCenter b c).property.toInvertibleSheaf /
        LineBundleClass.mk ((h.liftRay ρ).internalCenter b d).property.toInvertibleSheaf := by
  have hp (a : ℂˣ) :
      LineBundleClass.pullback β
        (LineBundleClass.mk (ρ.internalCenter b a).property.toInvertibleSheaf) =
      LineBundleClass.mk ((h.liftRay ρ).internalCenter b a).property.toInvertibleSheaf :=
    ((ρ.internalCenter b a).property.pullback_mk_toInvertibleSheaf
      ((h.comap_internalCenter b ρ a).symm ▸ ((h.liftRay ρ).internalCenter b a).property)).trans
        (LineBundleClass.mk_toInvertibleSheaf_congr _ _ (h.comap_internalCenter b ρ a))
  rw [← LineBundleClass.pullbackHom_apply, map_div, LineBundleClass.pullbackHom_apply,
    LineBundleClass.pullbackHom_apply, hp, hp]

include hc hA hr in
/-- The determinant-positive numbering of a regular toric refinement extends the
given positive numbering on the old boundary in the sense of ordered conductor
branches. It starts at the lift of any specified old ray. -/
theorem IsSubdivision.exists_positive_boundary_subdivision_numbering (ρ : Φ.Ray) :
    ∃ (hpre : PrestableFamily (C[Ψ] ↘ S)) (l : ℕ) (_ : NeZero l),
      letI := hpre
      ∀ q : δ → (C[Ψ] ↘ S).smoothLocus,
        ∃ (U : NodalCycleNumbering q l) (v : ZMod l ≃ Ψ.Ray),
          (β).IsOrientedCycleSubdivision U A ∧ v 0 = h.liftRay ρ ∧
          (∀ j, U.component j = Ψ.boundaryNormalizationComponentEquiv hΨ (v j)) ∧
          ∀ j, b.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
            ∃ σ : Ψ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ := by
  obtain ⟨edge, order, vertex, hw, hwA, hperiod⟩ :=
    Φ.exists_toric_boundary_period_of_cyclicRayNumbering hΦ b hc p r hr
  let A' : NodalCycleNumbering p n := ⟨vertex, edge, order, hw⟩
  have hsign := cycleOrientationSign_refl_of_matching_rays b hΦ A' A r
    (by simpa only [NodalCycleNumbering.component_apply, A'] using hwA) hA (fun j ↦ (hr j).1)
  have hAA' : (𝟙 C[Φ] : C[Φ] ⟶ C[Φ]).IsOrientedCycleSubdivision A' A :=
    (Iso.refl C[Φ]).isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one A' A hsign
  obtain ⟨hpre, m, hm, hW⟩ := h.exists_isOrientedCycleSubdivision_boundaryMap
    (δ := δ) A' hΦ hΨ (Φ.isEffectiveCartier_boundaryIdeal hΦ hc rankTwo) rankTwo
  let : PrestableFamily (C[Ψ] ↘ S) := hpre
  let : Nonempty Ψ.Ray := ⟨h.liftRay ρ⟩
  let : NeZero (Nat.card Ψ.Ray) := ⟨Nat.card_pos.ne'⟩
  have hc' := h.isComplete_iff.mpr hc
  obtain ⟨v, ⟨hv, hpos⟩, -⟩ := Ψ.existsUnique_cyclicRayNumbering b hΨ hc' (h.liftRay ρ)
  refine ⟨hpre, Nat.card Ψ.Ray, inferInstance, fun q ↦ ?_⟩
  obtain ⟨edge', order', vertex', hu, huA, hperiod'⟩ :=
    Ψ.exists_toric_boundary_period_of_cyclicRayNumbering hΨ b hc' q v hpos
  let U : NodalCycleNumbering q (Nat.card Ψ.Ray) := ⟨vertex', edge', order', hu⟩
  obtain ⟨W, hWA'⟩ := hW q
  have hlen := (Iso.refl C[Ψ]).nodalCycleNumbering_length_eq W U
  subst m
  have : (β).IsOver S := ⟨by
    rw [over_eq_subschemeι_comp, reassoc_of% (h.boundaryMap_comp_subschemeι hΨ₀ hΦ₀),
      algebraicRealization_over, FanHom.algebraicMap_comp_algebraicRealizationStructureMap,
      ← algebraicRealization_over, ← over_eq_subschemeι_comp]⟩
  obtain ⟨x, hx, hpx⟩ := hperiod ρ 1 twoUnit
  obtain ⟨y, hy, hpy⟩ := hperiod' (h.liftRay ρ) 1 twoUnit
  have hxy : LineBundleClass.pullback β x.val = y.val := by
    rw [hx, hy, pullback_centerRatio]
  have hUA' := preserves_orientation_of_centerRatio h A' U W hWA' x y hxy
    (by simpa only [div_one] using hpx) (by simpa only [div_one] using hpy)
  exact ⟨U, v, by simpa only [Category.comp_id] using hUA'.comp hAA', hv,
    by simpa only [NodalCycleNumbering.component_apply, U] using huA, hpos⟩

end Numberings

end TauCeti.Toric.Fan
