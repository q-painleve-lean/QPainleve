/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
import Mathlib.Algebra.BigOperators.Fin
import TauCeti.AlgebraicGeometry.IdealSheaf.Product

/-!
# Products of closed point ideals

A product of Cartier ideals of reduced closed points determines the list of
points up to permutation, including the multiplicity of every point.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

private theorem mem_support_prod_pointIdeals_iff {l : List X}
    (hc : ∀ p ∈ l, IsClosed ({p} : Set X)) (q : X) :
    q ∈ ((l.map fun p ↦ (X.fromSpecResidueField p).ker).prod).support ↔ q ∈ l := by
  have hs : (l.map fun p ↦ (X.fromSpecResidueField p).ker).prod =
      ∏ j : Fin l.length, (X.fromSpecResidueField (l.get j)).ker := by
    rw [← List.prod_ofFn]
    exact congrArg List.prod
      (List.ofFn_getElem_eq_map l (fun p ↦ (X.fromSpecResidueField p).ker)).symm
  rw [hs, ← SetLike.mem_coe, IdealSheafData.coe_support_prod, Set.mem_iUnion, List.mem_iff_get]
  refine exists_congr fun j ↦ ?_
  rw [X.support_ker_fromSpecResidueField_of_isClosed (hc _ (List.get_mem _ _)),
    Set.mem_singleton_iff, eq_comm]

/-- Equality of products of reduced closed point ideals yields a permutation of the point lists
if each factor in the first product is effective Cartier. -/
theorem perm_of_prod_ker_fromSpecResidueField_eq {l l' : List X}
    (hc : ∀ p ∈ l, IsClosed ({p} : Set X))
    (hc' : ∀ p ∈ l', IsClosed ({p} : Set X))
    (hCartier : ∀ p ∈ l, (X.fromSpecResidueField p).ker.IsEffectiveCartier)
    (h : (l.map fun p ↦ (X.fromSpecResidueField p).ker).prod =
      (l'.map fun p ↦ (X.fromSpecResidueField p).ker).prod) :
    l.Perm l' := by
  classical
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => exact List.Perm.nil
    | cons p l' =>
      exfalso
      have hp := (mem_support_prod_pointIdeals_iff hc' p).mpr (List.mem_cons_self ..)
      rw [← h] at hp
      simp [← SetLike.mem_coe] at hp
  | cons p l ih =>
    have hp : p ∈ l' := by
      apply (mem_support_prod_pointIdeals_iff hc' p).mp
      rw [← h]
      exact (mem_support_prod_pointIdeals_iff hc p).mpr (List.mem_cons_self ..)
    have hsplit := List.perm_cons_erase hp
    have hprod := (hsplit.map fun p ↦ (X.fromSpecResidueField p).ker).prod_eq
    rw [← h, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons] at hprod
    have htail := (hCartier p (List.mem_cons_self ..)).mul_left_cancel hprod
    exact (ih (fun q hq ↦ hc q (List.mem_cons_of_mem _ hq))
      (fun q hq ↦ hc' q (List.mem_of_mem_erase hq))
      (fun q hq ↦ hCartier q (List.mem_cons_of_mem _ hq)) htail).cons p |>.trans hsplit.symm

end AlgebraicGeometry.Scheme
