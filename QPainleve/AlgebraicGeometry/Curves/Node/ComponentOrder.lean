/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
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

universe u v

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

namespace AlgebraicGeometry.Scheme.NodalCycleNumbering

open IdealSheafData

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {B : X.IdealSheafData} [PrestableFamily (B.subscheme ↘ Spec (.of k))]
  {ι : Type v} {p : ι → (B.subscheme ↘ Spec (.of k)).smoothLocus} {n : ℕ} [NeZero n]

local notation "s" => (X ↘ Spec (CommRingCat.of k))
local notation "prime(" A "," h "," l ")" =>
  (B.boundaryPrimeEmbedding (NodalCycleNumbering.boundaryPrimeEquiv A h l))
local notation "ideal(" q ")" => vanishingIdeal (Closeds.mk (closure {(q : X)}) isClosed_closure)

/-- The order of a numbered prime at a node counts how many of the node's two
branches lie on that component. Both branches count at a self-node. -/
theorem stalkOrder_prime_eq_branch_count [IsLocallyNoetherian X]
    (A : NodalCycleNumbering p n) (hB : B.IsEffectiveCartier) (j l : ZMod n) :
    (ideal(prime(A,hB,l))).stalkOrder (A.ambientNode j) =
      (((if l = j then 1 else 0) + (if l = j + 1 then 1 else 0) : ℕ) : ℕ∞) := by
  classical
  let e := B.boundaryPrimeEmbedding ∘ A.boundaryPrimeEquiv hB
  have hinj : Function.Injective e :=
    B.boundaryPrimeEmbedding.injective.comp (A.boundaryPrimeEquiv hB).injective
  have hmem (a : ZMod n) : A.ambientNode j ∈ closure {(e a : X)} ↔ a = j ∨ a = j + 1 := by
    simpa [e, Fin.exists_fin_two, eq_comm] using A.ambientNode_mem_closure_boundaryPrime_iff hB j a
  have hsupp (q : CodimensionOnePoint X) : (q : X) ∈ B.support ↔ q ∈ Set.range e := by
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ, range_boundaryPrimeEmbedding]
    exact Iff.rfl
  have hother :
      (∃ q : CodimensionOnePoint X, q ≠ e l ∧ (q : X) ∈ B.support ∧
        A.ambientNode j ∈ closure {(q : X)}) ↔ l ≠ j ∨ l ≠ j + 1 := by
    constructor
    · rintro ⟨q, hq, hBq, hjq⟩
      obtain ⟨a, rfl⟩ := (hsupp q).mp hBq
      rcases (hmem a).mp hjq with rfl | rfl
      · exact Or.inl (ne_of_apply_ne e hq).symm
      · exact Or.inr (ne_of_apply_ne e hq).symm
    · intro h
      rcases h with h | h
      · exact ⟨e j, hinj.ne h.symm, (hsupp _).mpr (Set.mem_range_self j), (hmem j).mpr (Or.inl rfl)⟩
      · exact ⟨e (j + 1), hinj.ne h.symm, (hsupp _).mpr (Set.mem_range_self (j + 1)),
          (hmem _).mpr (Or.inr rfl)⟩
  have hN : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ s) := by
    rw [← B.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  calc
    _ = if A.ambientNode j ∈ closure {(e l : X)} then
        if ∃ q : CodimensionOnePoint X, q ≠ e l ∧ (q : X) ∈ B.support ∧
            A.ambientNode j ∈ closure {(q : X)} then 1 else 2 else 0 :=
      hB.stalkOrder_prime_eq_of_node hN
        (A.isNodeOfReducedBoundary_ambientNode j B.over_eq_subschemeι_comp)
        (e l) ((hsupp _).mpr (Set.mem_range_self l))
    _ = _ := by
      rw [hmem l, hother]
      split_ifs <;> norm_num <;> grind

end AlgebraicGeometry.Scheme.NodalCycleNumbering
