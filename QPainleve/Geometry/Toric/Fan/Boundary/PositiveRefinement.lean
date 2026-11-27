/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Refinement

import QPainleve.Geometry.Toric.Fan.Boundary.CycleAction
import QPainleve.Geometry.Toric.Fan.Boundary.Node
import QPainleve.Geometry.Toric.Fan.Boundary.Period
import QPainleve.Geometry.Toric.Fan.CyclicOrder.Basic
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

variable (K : Type) [Field K] [IsAlgClosed K]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]

local notation "S" => Spec (CommRingCat.of K)
local notation "D[" Φ "]" => Fan.toricBoundaryIdeal K Φ inferInstance
local notation "C[" Φ "]" => Scheme.IdealSheafData.subscheme D[Φ]
local notation "ν[" X "]" => Scheme.IdealSheafData.blowupToBase (Scheme.singularLocus K X)
local notation "P[" X "]" => MonoidHom.ker (LineBundleClass.pullbackHom ν[X])

variable (b : Basis (Fin 2) ℤ N) (h : Ψ.IsSubdivision Φ)

local notation "β" => h.boundaryMap K hΨ₀ hΦ₀
local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))

section Numberings

variable [PrestableFamily ((Φ.toricBoundaryIdeal K hΦ₀).subscheme ↘ Spec (.of K))]
  {γ δ : Type*} {p : γ → ((Φ.toricBoundaryIdeal K hΦ₀).subscheme ↘ Spec (.of K)).smoothLocus}
  {n : ℕ} [NeZero n]

local instance (X : Scheme) [X.Over S] : (Iso.refl X).hom.IsOver S := by
  rw [Iso.refl_hom]
  infer_instance

/-- The identity preserves orientation between any two determinant-positive
numberings of the same toric boundary, even when their initial rays differ. -/
theorem cycleOrientationSign_refl_of_positive_numberings
    (hΦ : Φ.IsRegular) {γ' : Type*} {p' : γ' → (C[Φ] ↘ S).smoothLocus}
    (A : NodalCycleNumbering p n) (A' : NodalCycleNumbering p' n)
    (r r' : ZMod n ≃ Φ.Ray)
    (hA : ∀ j, A.component j = Φ.boundaryNormalizationComponentEquiv K hΦ (r j))
    (hA' : ∀ j, A'.component j = Φ.boundaryNormalizationComponentEquiv K hΦ (r' j))
    (hpos : ∀ j, b.detDualEquiv (r j).primitiveGenerator (r (j + 1)).primitiveGenerator = 1)
    (hpos' : ∀ j, b.detDualEquiv (r' j).primitiveGenerator (r' (j + 1)).primitiveGenerator = 1) :
    cycleOrientationSign ((Iso.refl C[Φ]).boundaryCycleAction A A') = 1 := by
  have hrefl : (FanEquiv.refl Φ).boundaryIso K hΦ₀ hΦ₀ = Iso.refl C[Φ] := by
    apply Iso.ext
    apply (cancel_mono (D[Φ]).subschemeι).mp
    rw [FanEquiv.boundaryIso_hom_subschemeι, FanEquiv.toFanHom_refl, FanHom.finiteFanSchemeHom_id,
      Iso.refl_hom, Category.comp_id, Category.id_comp]
  simpa only [hrefl, Bool.false_eq_true, ↓reduceIte] using
    (FanEquiv.refl Φ).cycleOrientationSign_boundaryIso K hΦ hΦ A A' hA hA' b b hpos hpos'
      false (fun _ _ ↦ by simp only [FanEquiv.refl_latticeEquiv, AddEquiv.refl_apply,
        Bool.false_eq_true, ↓reduceIte])

private theorem preserves_orientation_of_centerRatio
    [PrestableFamily (C[Ψ] ↘ S)] [(β).IsOver S]
    {q : δ → (C[Ψ] ↘ S).smoothLocus} {l : ℕ} [NeZero l]
    (A : NodalCycleNumbering p n) (U W : NodalCycleNumbering q l)
    (hW : (β).IsOrientedCycleSubdivision W A) (x : P[C[Φ]]) (y : P[C[Ψ]])
    (hxy : LineBundleClass.pullback β x.val = y.val)
    (u : Kˣ) (hu : u ≠ u⁻¹)
    (hx : Scheme.nodalPicardCycleMulEquiv A.endpoint_eq x = u)
    (hy : Scheme.nodalPicardCycleMulEquiv U.endpoint_eq y = u) :
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
      exact (hu ht).elim
  simpa [e] using (e.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one U W hsign).comp hW

variable (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hc : Φ.IsComplete)
  (A : NodalCycleNumbering p n) (r : ZMod n ≃ Φ.Ray)
  (hA : ∀ j, A.component j = Φ.boundaryNormalizationComponentEquiv K hΦ (r j))
  (hr : ∀ j, b.detDualEquiv (r j).primitiveGenerator (r (j + 1)).primitiveGenerator = 1 ∧
    ∃ σ : Φ.cones, (r j).toCone ≤ σ ∧ (r (j + 1)).toCone ≤ σ)

omit [IsAlgClosed K] [PrestableFamily ((Φ.toricBoundaryIdeal K hΦ₀).subscheme ↘ Spec (.of K))] in
private theorem pullback_centerRatio (ρ : Φ.Ray) (c d : Kˣ) :
    LineBundleClass.pullback β
      (LineBundleClass.mk (ρ.internalCenter K b c).property.toInvertibleSheaf /
        LineBundleClass.mk (ρ.internalCenter K b d).property.toInvertibleSheaf) =
      LineBundleClass.mk ((h.liftRay ρ).internalCenter K b c).property.toInvertibleSheaf /
        LineBundleClass.mk ((h.liftRay ρ).internalCenter K b d).property.toInvertibleSheaf := by
  have hp (a : Kˣ) :
      LineBundleClass.pullback β
        (LineBundleClass.mk (ρ.internalCenter K b a).property.toInvertibleSheaf) =
      LineBundleClass.mk ((h.liftRay ρ).internalCenter K b a).property.toInvertibleSheaf :=
    ((ρ.internalCenter K b a).property.pullback_mk_toInvertibleSheaf
      ((h.comap_internalCenter K b ρ a).symm ▸ ((h.liftRay ρ).internalCenter K b a).property)).trans
        (LineBundleClass.mk_toInvertibleSheaf_congr _ _ (h.comap_internalCenter K b ρ a))
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
          (∀ j, U.component j = Ψ.boundaryNormalizationComponentEquiv K hΨ (v j)) ∧
          ∀ j, b.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
            ∃ σ : Ψ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ := by
  obtain ⟨edge, order, vertex, hw, hwA, hperiod⟩ :=
    Φ.exists_toric_boundary_period_of_cyclicRayNumbering K hΦ b hc p r hr
  let A' : NodalCycleNumbering p n := ⟨vertex, edge, order, hw⟩
  have hsign := cycleOrientationSign_refl_of_positive_numberings K b hΦ A' A r r
    (by simpa only [NodalCycleNumbering.component_apply, A'] using hwA) hA
    (fun j ↦ (hr j).1) (fun j ↦ (hr j).1)
  have hAA' : (𝟙 C[Φ] : C[Φ] ⟶ C[Φ]).IsOrientedCycleSubdivision A' A :=
    (Iso.refl C[Φ]).isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one A' A hsign
  obtain ⟨hpre, m, hm, hW⟩ := h.exists_isOrientedCycleSubdivision_boundaryMap K
    (δ := δ) A' hΦ hΨ (Φ.isEffectiveCartier_boundaryIdeal K hΦ hc rankTwo) rankTwo
  let : PrestableFamily (C[Ψ] ↘ S) := hpre
  let : Nonempty Ψ.Ray := ⟨h.liftRay ρ⟩
  let : NeZero (Nat.card Ψ.Ray) := ⟨Nat.card_pos.ne'⟩
  have hc' := h.isComplete_iff.mpr hc
  obtain ⟨v, ⟨hv, hpos⟩, -⟩ := Ψ.existsUnique_cyclicRayNumbering b hΨ hc' (h.liftRay ρ)
  refine ⟨hpre, Nat.card Ψ.Ray, inferInstance, fun q ↦ ?_⟩
  obtain ⟨edge', order', vertex', hu, huA, hperiod'⟩ :=
    Ψ.exists_toric_boundary_period_of_cyclicRayNumbering K hΨ b hc' q v hpos
  let U : NodalCycleNumbering q (Nat.card Ψ.Ray) := ⟨vertex', edge', order', hu⟩
  obtain ⟨W, hWA'⟩ := hW q
  have hlen := (Iso.refl C[Ψ]).nodalCycleNumbering_length_eq W U
  subst m
  have : (β).IsOver S := ⟨by
    rw [over_eq_subschemeι_comp, reassoc_of% (h.boundaryMap_comp_subschemeι K hΨ₀ hΦ₀),
      finiteFanScheme_over, FanHom.finiteFanSchemeHom_comp_finiteFanSchemeToSpec,
      ← finiteFanScheme_over, ← over_eq_subschemeι_comp]⟩
  classical
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset K)
  let u := Units.mk0 t (fun h ↦ ht (Finset.mem_insert.mpr (Or.inl h)))
  have hu : u ≠ u⁻¹ := by
    intro h
    have he : t = t⁻¹ := by
      simpa only [u, Units.val_inv_eq_inv_val, Units.val_mk0] using congrArg Units.val h
    rcases self_eq_inv₀.mp he with h | h | h <;> exact ht (by rw [h]; simp)
  obtain ⟨x, hx, hpx⟩ := hperiod ρ 1 u
  obtain ⟨y, hy, hpy⟩ := hperiod' (h.liftRay ρ) 1 u
  have hxy : LineBundleClass.pullback β x.val = y.val := by
    rw [hx, hy, pullback_centerRatio]
  have hUA' := preserves_orientation_of_centerRatio K h A' U W hWA' x y hxy u hu
    (by simpa only [div_one] using hpx) (by simpa only [div_one] using hpy)
  exact ⟨U, v, by simpa only [Category.comp_id] using hUA'.comp hAA', hv,
    by simpa only [NodalCycleNumbering.component_apply, U] using huA, hpos⟩

end Numberings

end TauCeti.Toric.Fan
