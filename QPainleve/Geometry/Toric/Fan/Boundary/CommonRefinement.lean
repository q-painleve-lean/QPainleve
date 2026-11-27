/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.PositiveRefinement
public import QPainleve.Geometry.Toric.Fan.Subdivision

import QPainleve.Geometry.Toric.Fan.Boundary.Orientation
import QPainleve.Geometry.Toric.Fan.CommonRefinement

/-!
# Oriented common refinements of toric boundaries

When two complete regular surface fans are compared in the same oriented lattice,
a single numbering of a common regular refinement preserves the ordered branches
under both boundary projections. A determinant-preserving change of lattice
transports the positive order before taking the refinement.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Module
open Scheme (NodalCycleNumbering)
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ Ω : Fan i} {Ψ : Fan i'}
  [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "D[" k "," Φ "," h "]" =>
  Scheme.IdealSheafData.subscheme (Fan.toricBoundaryIdeal k Φ h)

section Transport

variable [hΩ₀ : Nonempty Ω.cones]
  [PrestableFamily (D[k₀,Ψ,hΨ₀] ↘ Spec (.of k₀))] [PrestableFamily (D[k₀,Ω,hΩ₀] ↘ Spec (.of k₀))]
  {α : Type*} {p : α → (D[k₀,Ψ,hΨ₀] ↘ Spec (.of k₀)).smoothLocus}
  {m : ℕ} [NeZero m] (B : NodalCycleNumbering p m)
  {v : ZMod m ≃ Ψ.Ray} (hΨ : Ψ.IsRegular) (hΩ : Ω.IsRegular)
  (hv : ∀ j, B.component j = Ψ.boundaryNormalizationComponentEquiv k₀ hΨ (v j))
  (e : FanEquiv Ψ Ω) (b : Basis (Fin 2) ℤ N) (b' : Basis (Fin 2) ℤ N')
  (hdet : ∀ x y, b.detDualEquiv (e.latticeEquiv x) (e.latticeEquiv y) = b'.detDualEquiv x y)

local notation "g" => e.boundaryIso k₀ hΨ₀ hΩ₀
local notation "marks" => (Empty.elim : Empty → Scheme.Hom.smoothLocus (D[k₀,Ω,hΩ₀] ↘ S))
local notation "B₀" => Iso.mapNodalCycleNumbering g B (q := marks)
local notation "v₀" => v.trans e.rayEquiv

include hv in
private theorem component_mapNodalCycleNumbering (j : ZMod m) :
    (B₀).component j = Ω.boundaryNormalizationComponentEquiv k₀ hΩ (v₀ j) := by
  apply Subtype.ext
  rw [Iso.coe_component_mapNodalCycleNumbering, hv,
    e.image_singularLocusBlowupIso_boundaryNormalizationComponent k₀ hΨ hΩ]
  rfl

omit hΨ₀ hΩ₀ [PrestableFamily (D[k₀,Ψ,hΨ₀] ↘ Spec (.of k₀))] [PrestableFamily (D[k₀,Ω,hΩ₀] ↘ Spec
  (.of k₀))] [NeZero m] in
include hdet in
private theorem positive_mapRayNumbering
    (hpos : ∀ j, b'.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Ψ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ) (j : ZMod m) :
    b.detDualEquiv (v₀ j).primitiveGenerator (v₀ (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Ω.cones, (v₀ j).toCone ≤ σ ∧ (v₀ (j + 1)).toCone ≤ σ := by
  obtain ⟨hpair, σ, hle, hle'⟩ := hpos j
  refine ⟨by simpa only [Equiv.trans_apply, FanEquiv.primitiveGenerator_rayEquiv, hdet] using hpair,
    e.coneEquiv σ, ?_, ?_⟩
  · simpa only [Equiv.trans_apply, FanEquiv.toCone_rayEquiv] using e.coneEquiv.monotone hle
  · simpa only [Equiv.trans_apply, FanEquiv.toCone_rayEquiv] using e.coneEquiv.monotone hle'

end Transport

section Common

variable [PrestableFamily (D[k₀,Φ,hΦ₀] ↘ Spec (.of k₀))] [PrestableFamily (D[k₀,Ψ,hΨ₀] ↘ Spec
  (.of k₀))]
  {α β : Type*} {p : α → (D[k₀,Φ,hΦ₀] ↘ Spec (.of k₀)).smoothLocus}
  {q : β → (D[k₀,Ψ,hΨ₀] ↘ Spec (.of k₀)).smoothLocus}
  {n m : ℕ} [NeZero n] [NeZero m]
  (A : NodalCycleNumbering p n) (B : NodalCycleNumbering q m)
  {u : ZMod n ≃ Φ.Ray} {v : ZMod m ≃ Ψ.Ray}
  (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hcΦ : Φ.IsComplete) (hcΨ : Ψ.IsComplete)
  (hu : ∀ j, A.component j = Φ.boundaryNormalizationComponentEquiv k₀ hΦ (u j))
  (hv : ∀ j, B.component j = Ψ.boundaryNormalizationComponentEquiv k₀ hΨ (v j))
  (e : FanEquiv Ψ Ω) (b : Basis (Fin 2) ℤ N) (b' : Basis (Fin 2) ℤ N')
  (hdet : ∀ x y, b.detDualEquiv (e.latticeEquiv x) (e.latticeEquiv y) = b'.detDualEquiv x y)
  (hpos : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
    ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ)
  (hpos' : ∀ j, b'.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
    ∃ σ : Ψ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ)

local notation "hΩ₀" => Nonempty.map (FanEquiv.coneEquiv e) hΨ₀
local notation "g" => FanEquiv.boundaryIso k₀ e hΨ₀ hΩ₀

include hcΦ hcΨ hu hv hdet hpos hpos' in
/-- A common regular refinement of two complete toric surfaces in identified oriented
lattices has a single numbering that extends both positive boundary numberings.
The projection to the second boundary uses the inverse of the specified fan equivalence. -/
theorem FanEquiv.exists_oriented_common_boundary_subdivision :
    ∃ (Δ : Fan i) (hΔΦ : Δ.IsSubdivision Φ) (hΔΩ : Δ.IsSubdivision Ω),
      let hΔ₀ := hΔΦ.nonempty_cones_of_nonempty hΦ₀
      ∃ (_ : Δ.IsRegular) (hpre : PrestableFamily (D[k₀,Δ,hΔ₀] ↘ S)) (l : ℕ) (_ : NeZero l),
        letI := hpre
        ∃ U : NodalCycleNumbering (Empty.elim : Empty → (D[k₀,Δ,hΔ₀] ↘ S).smoothLocus) l,
          (hΔΦ.boundaryMap k₀ hΔ₀ hΦ₀).IsOrientedCycleSubdivision U A ∧
          (hΔΩ.boundaryMap k₀ hΔ₀ hΩ₀ ≫ (g).inv).IsOrientedCycleSubdivision U B := by
  obtain ⟨Δ, hΔΦ, hΔΩ, hΔ⟩ := e.exists_common_regular_subdivision_of_complete hΦ hΨ hcΦ hcΨ b
  let : Nonempty Δ.cones := hΔΦ.nonempty_cones_of_nonempty hΦ₀
  let : Nonempty Ω.cones := hΩ₀
  let : (g).symm.hom.IsOver S := inferInstanceAs ((g).inv.IsOver S)
  let : PrestableFamily (D[k₀,Ω,hΩ₀] ↘ S) := by
    rw [← comp_over (g).inv S]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily) (g).inv _).2
      inferInstance
  let B₀ := (g).mapNodalCycleNumbering B
    (q := (Empty.elim : Empty → (D[k₀,Ω,hΩ₀] ↘ S).smoothLocus))
  have hrot := (g).boundaryCycleAction_symm B B₀
  rw [(g).boundaryCycleAction_mapNodalCycleNumbering B, inv_one] at hrot
  have hg := (g).symm.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one B₀ B
    (by simp only [hrot, map_one])
  have hΩ := e.isRegular_iff.mpr hΨ
  obtain ⟨hpre, l, hl, hleft⟩ :=
    hΔΦ.exists_positive_boundary_subdivision_numbering k₀ (δ := Empty) b hΦ hΔ hcΦ A u hu hpos (u 0)
  let : PrestableFamily (D[k₀,Δ,inferInstance] ↘ S) := hpre
  let : NeZero l := hl
  obtain ⟨U, w, hU, -, hw, hwpos⟩ := hleft Empty.elim
  obtain ⟨_, l', hl', hright⟩ :=
    hΔΩ.exists_positive_boundary_subdivision_numbering k₀ (δ := Empty) b hΩ hΔ
      (e.isComplete_iff.mpr hcΨ) B₀ (v.trans e.rayEquiv)
      (component_mapNodalCycleNumbering k₀ B hΨ hΩ hv e) (positive_mapRayNumbering e b b'
        hdet hpos')
      (e.rayEquiv (v 0))
  let : NeZero l' := hl'
  obtain ⟨W, w', hW, -, hw', hwpos'⟩ := hright Empty.elim
  have : (Iso.refl D[k₀,Δ,inferInstance]).hom.IsOver S := by
    rw [Iso.refl_hom]
    infer_instance
  have hlen := (Iso.refl D[k₀,Δ,inferInstance]).nodalCycleNumbering_length_eq W U
  subst l'
  have hsign := Fan.cycleOrientationSign_refl_of_positive_numberings k₀ b hΔ U W w w' hw hw'
    (fun j ↦ (hwpos j).1) (fun j ↦ (hwpos' j).1)
  have hUW := Iso.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one
    (Iso.refl D[k₀,Δ,inferInstance]) U W hsign
  exact ⟨Δ, hΔΦ, hΔΩ, hΔ, hpre, l, hl, U, hU,
    by simpa only [Iso.refl_hom, Category.id_comp, Iso.symm_hom] using (hUW.comp hW).comp hg⟩

end Common

end TauCeti.Toric
