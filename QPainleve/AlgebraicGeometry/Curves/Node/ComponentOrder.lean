/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Order
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint

import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.IdealSheaf.Stalk
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Multiplicities of prime components at boundary nodes

A prime component has order zero away from its support, order one at a node shared
with another component, and order two at a self-node. These orders give the
exceptional corrections to the individual strict-transform classes.
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {X : Scheme.{u}}

local notation "P(" q ")" => vanishingIdeal (Closeds.mk (closure {(q : X)}) isClosed_closure)

open Classical in
/-- The order of a prime component at a node is determined by whether the component
contains the node and whether there is another component through the same node. -/
theorem stalkOrder_prime_eq_of_node
    {k : Type u} [Field k] {f : X ⟶ Spec (.of k)}
    [IsIntegral X] [QuasiCompact f] [SmoothOfRelativeDimension 2 f]
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ f))
    {x : X} (hx : D.IsNodeOfReducedBoundary f x)
    (q : CodimensionOnePoint X) (hq : (q : X) ∈ D.support) :
    (P(q)).stalkOrder x = if x ∈ closure {(q : X)} then
      if ∃ r : CodimensionOnePoint X, r ≠ q ∧ (r : X) ∈ D.support ∧
        x ∈ closure {(r : X)} then 1 else 2
      else 0 := by
  have hmem (r : CodimensionOnePoint X) : x ∈ (P(r)).support ↔ x ∈ closure {(r : X)} := by
    rw [← SetLike.mem_coe, coe_support_vanishingIdeal, Closeds.coe_mk]
  by_cases hqx : x ∉ closure {(q : X)}
  · rw [ite_eq_right hqx]
    exact ((P(q)).stalkOrder_eq_zero_iff x).mpr (fun h ↦ hqx ((hmem q).mp h))
  push Not at hqx
  rw [ite_eq_left hqx]
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsNoetherian X := isNoetherian_of_finiteType f
  have (y : X) : UniqueFactorizationMonoid (X.presheaf.stalk y) :=
    f.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two y
  have : IsRegular X := IsRegular.of_smooth f
  have : IsReduced D.subscheme := hnodal.isReduced
  let s := hD.toCartierDivisor.toWeilDivisor.support
  have hs (r : CodimensionOnePoint X) : r ∈ s ↔ (r : X) ∈ D.support := by
    have := CodimensionOnePoint.isDiscreteValuationRing_stalk r
    rw [Finsupp.mem_support_iff, ← WeilDivisor.coeff]
    simpa only [not_not] using not_congr (hD.coeff_toWeilDivisor_eq_zero_iff r)
  have hprod := hD.eq_prod_vanishingIdeal_of_isReduced s hs
  have htwo : D.stalkOrder x = 2 := by
    simpa only [ite_eq_left hx] using
      hD.stalkOrder_eq_if_isNodeOfReducedBoundary hnodal (mem_support_of_isNodeOfReducedBoundary hx)
  split_ifs with hr
  · obtain ⟨r, hrq, hr, hrx⟩ := hr
    have hle : D.stalkIdeal x ≤ (P(q)).stalkIdeal x * (P(r)).stalkIdeal x := by
      rw [hprod, stalkIdeal_prod]
      have hsub : {q, r} ⊆ s := Finset.insert_subset ((hs q).mpr hq)
        (Finset.singleton_subset_iff.mpr ((hs r).mpr hr))
      simpa only [Finset.prod_insert, Finset.mem_singleton, Ne.symm hrq, not_false_eq_true,
        Finset.prod_singleton] using Finset.prod_le_prod_of_subset_of_le_one
          (f := fun a : CodimensionOnePoint X ↦ (P(a)).stalkIdeal x) hsub
          (fun _ _ _ ↦ by rw [Ideal.one_eq_top]; exact le_top)
    have hsum := (Ideal.localOrder_add_le_localOrder_mul ((P(q)).stalkIdeal x)
      ((P(r)).stalkIdeal x)).trans (Ideal.localOrder_anti hle)
    simp only [← stalkOrder_def, htwo] at hsum
    have hr₁ := ((P(r)).one_le_stalkOrder_iff x).mpr ((hmem r).mpr hrx)
    have hq₁ := ((P(q)).one_le_stalkOrder_iff x).mpr ((hmem q).mpr hqx)
    exact le_antisymm ((ENat.add_le_add_iff_right (by decide : (1 : ℕ∞) ≠ ⊤)).mp
      ((add_le_add le_rfl hr₁).trans hsum)) hq₁
  · have hstalk : D.stalkIdeal x = (P(q)).stalkIdeal x := by
      rw [hprod, stalkIdeal_prod]
      refine Finset.prod_eq_single q (fun r hsr hrq ↦ ?_) (fun hn ↦ (hn ((hs q).mpr hq)).elim)
      rw [Ideal.one_eq_top]
      exact not_ne_iff.mp fun h ↦ hr ⟨r, hrq, (hs r).mp hsr,
        (hmem r).mp (((P(r)).mem_support_iff_stalkIdeal_ne_top x).mpr h)⟩
    rw [stalkOrder_def, ← hstalk, ← stalkOrder_def, htwo]

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
