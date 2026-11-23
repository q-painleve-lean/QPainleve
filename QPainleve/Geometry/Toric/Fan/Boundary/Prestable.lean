/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Node
public import TauCeti.AlgebraicGeometry.Curves.Prestable
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import TauCeti.Geometry.Toric.Algebraic.Fan.Over

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.Geometry.Toric.Fan.Boundary.Component
import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter
import QPainleve.Geometry.Toric.Fan.Boundary.Intersection
import QPainleve.Geometry.Toric.Fan.CyclicOrder
import TauCeti.AlgebraicGeometry.Geometrically.Irreducible
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.Pullback.Carrier

/-!
# Prestable toric boundaries

The reduced boundary of a complete regular rank-two fan is covered by split-node
charts. Its ray components meet along the cyclic ordering of the rays, and this
connectedness persists after field extension. For a proper toric surface these
facts provide the prestable curve needed for its normalization and boundary periods.
See [Stacks Project, §109.20](https://stacks.math.columbia.edu/tag/0E6S) for prestable
curves and [Gross, Hacking and Keel, §2](https://arxiv.org/html/1211.6367v5#S2)
for periods on the boundary cycle.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

variable [Nonempty Φ.cones]

local notation "D" => Φ.boundaryIdeal inferInstance
local notation "boundaryMap" => subschemeι D ≫ Φ.algebraicRealizationStructureMap

private theorem range_boundaryComponentι_inter_nonempty (hΦ : Φ.IsRegular)
    (hdim : Module.finrank ℤ N = 2) {ρ τ : Φ.Ray} (hne : ρ ≠ τ)
    (σ : Φ.cones) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ) :
    (Set.range (ρ.boundaryComponentι hΦ) ∩ Set.range (τ.boundaryComponentι hΦ)).Nonempty := by
  let p := Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ)
  have hp : p ∈ (Φ.rayBoundaryIdeal hΦ ρ ⊔ Φ.rayBoundaryIdeal hΦ τ).support := by
    rw [Φ.sup_rayBoundaryIdeal_eq_ker_distinguishedPoint hΦ hdim hne σ hρ hτ,
      ← Φ.distinguishedPointHom_def, ← SetLike.mem_coe, Scheme.Hom.support_ker]
    exact subset_closure (Set.mem_range_self _)
  rw [← SetLike.mem_coe, support_sup, Closeds.coe_inf] at hp
  obtain ⟨x, hx⟩ := (range_subschemeι (Φ.rayBoundaryIdeal hΦ ρ)).symm ▸ hp.1
  obtain ⟨y, hy⟩ := (range_subschemeι (Φ.rayBoundaryIdeal hΦ τ)).symm ▸ hp.2
  refine ⟨ρ.boundaryComponentι hΦ x, Set.mem_range_self _, y, ?_⟩
  apply (D).subschemeι.isClosedEmbedding.injective
  simpa only [← Scheme.Hom.comp_apply, Ray.boundaryComponentι_subschemeι] using hy.trans hx.symm

private theorem iUnion_range_boundaryComponentι (hΦ : Φ.IsRegular) :
    ⋃ ρ : Φ.Ray, Set.range (ρ.boundaryComponentι hΦ) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : (D).subschemeι x ∈ ((D).support : Set Φ.algebraicRealization) := by
    rw [← range_subschemeι]
    exact Set.mem_range_self _
  rw [Φ.support_boundaryIdeal_eq_iUnion_closure hΦ, Set.mem_iUnion] at hx
  obtain ⟨ρ, hρ⟩ := hx
  rw [← Φ.coe_support_rayBoundaryIdeal hΦ, ← range_subschemeι] at hρ
  obtain ⟨y, hy⟩ := hρ
  apply Set.mem_iUnion.mpr
  refine ⟨ρ, y, (D).subschemeι.isClosedEmbedding.injective ?_⟩
  simpa only [← Scheme.Hom.comp_apply, Ray.boundaryComponentι_subschemeι] using hy

private theorem isConnected_preimage_range_boundaryComponentι (hΦ : Φ.IsRegular)
    (hdim : Module.finrank ℤ N = 2) (b : Module.Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
    {K : Type} [Field K] (p : Spec (.of K) ⟶ Spec (.of ℂ))
    {Y : Scheme} {g : Y ⟶ (D).subscheme} {s : Y ⟶ Spec (.of K)}
    (sq : IsPullback g s boundaryMap p) :
    _root_.IsConnected (g ⁻¹' Set.range (ρ.boundaryComponentι hΦ)) := by
  let j := ρ.boundaryComponentι hΦ
  let t := ρ.orbitToComponent hΦ hdim (b.detDualEquiv_self _) (ρ.surjective_detCharacter b)
  have hLaurent : IrreducibleSpace (PrimeSpectrum (LaurentPolynomial ℂ)) := inferInstance
  have : Nonempty (Spec (.of (LaurentPolynomial ℂ))) := hLaurent.toNonempty
  have : IsOpenImmersion t := ρ.isOpenImmersion_orbitToComponent hΦ hdim _ _
  have : IsDominant t := isDominant_of_isOpenImmersion t
  have : GeometricallyIrreducible (t ≫ j ≫ boundaryMap) :=
    geometricallyIrreducible_Spec_of_isSepClosed
  have : GeometricallyIrreducible (j ≫ boundaryMap) :=
    GeometricallyIrreducible.of_comp_isDominant t _
  have : IrreducibleSpace (pullback j g : Scheme) :=
    GeometricallyIrreducible.irreducibleSpace_pullback_of_comp j boundaryMap sq
  rw [← Scheme.Pullback.range_snd j g, ← Set.image_univ]
  exact isConnected_univ.image _ (pullback.snd j g).continuous.continuousOn

/-- The reduced boundary of a complete regular rank-two fan is geometrically connected. -/
theorem geometricallyConnected_boundary (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hdim : Module.finrank ℤ N = 2) : GeometricallyConnected boundaryMap := by
  classical
  have := Φ.lattice.free
  have := Φ.lattice.finite
  let b : Module.Basis (Fin 2) ℤ N := hdim ▸ Module.finBasis ℤ N
  have : Nontrivial N := Module.nontrivial_of_finrank_eq_succ (n := 1) hdim
  have : Nonempty Φ.Ray := Φ.nonempty_ray_of_isComplete hc
  have : NeZero (Nat.card Φ.Ray) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨u, ⟨-, hu⟩, -⟩ := Φ.existsUnique_cyclicRayNumbering b hΦ hc (Nonempty.some ‹_›)
  refine ⟨fun K _ p Y g s sq ↦ connectedSpace_iff_univ.mpr ?_⟩
  have : Surjective g := MorphismProperty.of_isPullback sq.flip inferInstance
  let A (j : ZMod (Nat.card Φ.Ray)) := g ⁻¹' Set.range ((u j).boundaryComponentι hΦ)
  have hcover : (⋃ j, A j) = Set.univ := by
    simp only [A, ← Set.preimage_iUnion]
    rw [u.surjective.iUnion_comp (fun ρ ↦ Set.range (ρ.boundaryComponentι hΦ)),
      iUnion_range_boundaryComponentι hΦ, Set.preimage_univ]
  rw [← hcover]
  refine IsConnected.iUnion_of_reflTransGen
    (fun j ↦ isConnected_preimage_range_boundaryComponentι hΦ hdim b (u j) p sq) ?_
  have hA (j : ZMod (Nat.card Φ.Ray)) : (A j ∩ A (j + 1)).Nonempty := by
    obtain ⟨hdet, σ, h₀, h₁⟩ := hu j
    have hne : u j ≠ u (j + 1) := by
      intro he
      rw [← he, b.detDualEquiv_self] at hdet
      exact zero_ne_one hdet
    simp only [A, ← Set.preimage_inter]
    exact (range_boundaryComponentι_inter_nonempty hΦ hdim hne σ h₀ h₁).preimage g.surjective
  -- Moving forward along the cycle connects any pair of ray components.
  intro j k
  obtain ⟨m, hm⟩ := ZMod.natCast_zmod_surjective (k - j)
  have hk : k = j + (m : ZMod (Nat.card Φ.Ray)) := by rw [hm, add_sub_cancel]
  rw [hk]
  clear hm hk
  induction m with
  | zero => rw [Nat.cast_zero, add_zero]
  | succ m ih =>
    rw [Nat.cast_succ, ← add_assoc]
    exact ih.tail (hA _)

/-- The reduced boundary of a proper toric surface with a complete regular fan is
a prestable curve over `ℂ`. -/
theorem prestableFamily_boundary (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hdim : Module.finrank ℤ N = 2)
    [IsProper Φ.algebraicRealizationStructureMap] :
    PrestableFamily ((D).subscheme ↘ Spec (.of ℂ)) := by
  rw [over_eq_subschemeι_comp, Φ.algebraicRealization_over]
  exact {
    toIsProper := inferInstance
    toGeometricallyConnected := geometricallyConnected_boundary hΦ hc hdim
    atWorstNodalOfRelativeDimensionOne := atWorstNodalOfRelativeDimensionOne_boundary hΦ hc hdim }

end TauCeti.Toric.Fan
