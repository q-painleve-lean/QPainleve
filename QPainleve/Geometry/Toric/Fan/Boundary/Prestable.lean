/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Node
public import TauCeti.AlgebraicGeometry.Curves.Prestable
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import QPainleve.Geometry.Toric.BaseChange.FanMap

import QPainleve.Geometry.Toric.Fan.Boundary.Component
import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter
import QPainleve.Geometry.Toric.Fan.Boundary.Intersection
import QPainleve.Geometry.Toric.Fan.CyclicOrder.Basic
import TauCeti.AlgebraicGeometry.Geometrically.Irreducible
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.MonoidAlgebra.BaseChange
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
open TauCeti.AlgebraicGeometry TensorProduct
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

universe u

variable (k : Type u) [Field k] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

variable [Nonempty Φ.cones]

local notation "D" => Φ.toricBoundaryIdeal k inferInstance
local notation "boundaryMap" => subschemeι D ≫ (Φ.finiteFanSchemeToSpec k)

private theorem range_boundaryComponentι_inter_nonempty (hΦ : Φ.IsRegular)
    (hdim : Module.finrank ℤ N = 2) {ρ τ : Φ.Ray} (hne : ρ ≠ τ)
    (σ : Φ.cones) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ) :
    (Set.range (ρ.boundaryComponentι k hΦ) ∩ Set.range (τ.boundaryComponentι k hΦ)).Nonempty := by
  let p := Φ.distinguishedSection (R := k) σ (IsLocalRing.closedPoint k)
  have hp : p ∈ (Φ.rayDivisorIdeal k hΦ ρ ⊔ Φ.rayDivisorIdeal k hΦ τ).support := by
    rw [Φ.sup_rayBoundaryIdeal_eq_ker_distinguishedPoint k hΦ hdim hne σ hρ hτ,
      ← SetLike.mem_coe, Scheme.Hom.support_ker]
    exact subset_closure (Set.mem_range_self _)
  rw [← SetLike.mem_coe, support_sup, Closeds.coe_inf] at hp
  obtain ⟨x, hx⟩ := (range_subschemeι (Φ.rayDivisorIdeal k hΦ ρ)).symm ▸ hp.1
  obtain ⟨y, hy⟩ := (range_subschemeι (Φ.rayDivisorIdeal k hΦ τ)).symm ▸ hp.2
  refine ⟨ρ.boundaryComponentι k hΦ x, Set.mem_range_self _, y, ?_⟩
  apply (D).subschemeι.isClosedEmbedding.injective
  simpa only [← Scheme.Hom.comp_apply, Ray.boundaryComponentι_subschemeι] using hy.trans hx.symm

private theorem geometricallyIrreducible_laurentSpec :
    GeometricallyIrreducible (Spec.algebraMap k (LaurentPolynomial k)) := by
  rw [geometricallyIrreducible_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  let e : LaurentPolynomial k ⊗[k] K ≃+* LaurentPolynomial K :=
    (Algebra.TensorProduct.comm k (LaurentPolynomial k) K).toRingEquiv.trans
      (_root_.AddMonoidAlgebra.scalarTensorEquiv k K (M := ℤ)).toRingEquiv
  have h : IrreducibleSpace (PrimeSpectrum (LaurentPolynomial k ⊗[k] K)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv e).irreducibleSpace_iff.mpr inferInstance
  exact (pullbackSpecIso k (LaurentPolynomial k) K).inv.homeomorph.irreducibleSpace_iff.mp h

private theorem isConnected_preimage_range_boundaryComponentι (hΦ : Φ.IsRegular)
    (hdim : Module.finrank ℤ N = 2) (b : Module.Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
    {K : Type u} [Field K] (p : Spec (.of K) ⟶ Spec (.of k))
    {Y : Scheme.{u}} {g : Y ⟶ (D).subscheme} {s : Y ⟶ Spec (.of K)}
    (sq : IsPullback g s boundaryMap p) :
    _root_.IsConnected (g ⁻¹' Set.range (ρ.boundaryComponentι k hΦ)) := by
  let j := ρ.boundaryComponentι k hΦ
  let t := ρ.orbitToComponent k hΦ hdim (b.detDualEquiv_self _) (ρ.surjective_detCharacter b)
  have hLaurent : IrreducibleSpace (PrimeSpectrum (LaurentPolynomial k)) := inferInstance
  have : Nonempty (Spec (.of (LaurentPolynomial k))) := hLaurent.toNonempty
  have : IsOpenImmersion t := ρ.isOpenImmersion_orbitToComponent k hΦ hdim _ _
  have : IsDominant t := isDominant_of_isOpenImmersion t
  have : GeometricallyIrreducible (t ≫ j ≫ boundaryMap) := by
    have ht := ρ.orbitToComponent_boundaryComponentι k hΦ hdim
      (b.detDualEquiv_self _) (ρ.surjective_detCharacter b)
    change t ≫ j = _ at ht
    have hs := ρ.orbitToBoundary_comp_finiteFanSchemeToSpec k hdim
      (b.detDualEquiv_self _) (ρ.surjective_detCharacter b)
    rw [← Category.assoc t j, ht, hs]
    exact geometricallyIrreducible_laurentSpec k
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
  let A (j : ZMod (Nat.card Φ.Ray)) := g ⁻¹' Set.range ((u j).boundaryComponentι k hΦ)
  have hcover : (⋃ j, A j) = Set.univ := by
    simp only [A, ← Set.preimage_iUnion]
    rw [u.surjective.iUnion_comp (fun ρ ↦ Set.range (ρ.boundaryComponentι k hΦ)),
      iUnion_range_boundaryComponentι k hΦ, Set.preimage_univ]
  rw [← hcover]
  refine IsConnected.iUnion_of_reflTransGen
    (fun j ↦ isConnected_preimage_range_boundaryComponentι k hΦ hdim b (u j) p sq) ?_
  have hA (j : ZMod (Nat.card Φ.Ray)) : (A j ∩ A (j + 1)).Nonempty := by
    obtain ⟨hdet, σ, h₀, h₁⟩ := hu j
    have hne : u j ≠ u (j + 1) := by
      intro he
      rw [← he, b.detDualEquiv_self] at hdet
      exact zero_ne_one hdet
    simp only [A, ← Set.preimage_inter]
    exact (range_boundaryComponentι_inter_nonempty k hΦ hdim hne σ h₀ h₁).preimage g.surjective
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
a prestable curve over the coefficient field. -/
theorem prestableFamily_boundary (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hdim : Module.finrank ℤ N = 2)
    [IsProper (Φ.finiteFanSchemeToSpec k)] :
    PrestableFamily ((D).subscheme ↘ Spec (.of k)) := by
  rw [over_eq_subschemeι_comp, Φ.finiteFanScheme_over k]
  exact {
    toIsProper := inferInstance
    toGeometricallyConnected := geometricallyConnected_boundary k hΦ hc hdim
    atWorstNodalOfRelativeDimensionOne := atWorstNodalOfRelativeDimensionOne_boundary k hΦ hc hdim }

end TauCeti.Toric.Fan
