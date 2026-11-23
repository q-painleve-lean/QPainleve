/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Cycle

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.ZMod.Basic

/-!
# Gluing constants around an oriented cycle

A trivialization on each component of the normalization of a nodal curve
represents the gluing at each node by a scalar. Changing the component
trivializations multiplies these scalars by the ratios of the vertex scalars
at the two branches of each edge. For an oriented cycle, their product
classifies the gluing constants up to such a change. Once the change at one
vertex is fixed to be one, the remaining changes are uniquely determined.

The edge labels preserve loops and parallel edges, so the same product
applies to cycles with one or two components. Reversing the orientation
inverts the product. This is the scalar calculation in
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
Lemma 2.1](https://arxiv.org/pdf/1211.6367#page=6).
-/

public section

open scoped BigOperators
open Finset

namespace TauCeti.DualGraph

variable {ι : Type*} (G : DualGraph ι) (A : Type*) [CommGroup A]

/-- The change of gluing scalars induced by rescaling the vertex trivializations.
The chosen orientation of each edge is from its zeroth branch to its first branch. -/
def gluingCoboundary : (G.Vertex → A) →* (G.Edge → A) :=
  MonoidHom.pi fun e ↦
    Pi.evalMonoidHom (fun _ ↦ A) (G.endpoint e 1) /
      Pi.evalMonoidHom (fun _ ↦ A) (G.endpoint e 0)

variable {G A}

@[simp]
theorem gluingCoboundary_apply (c : G.Vertex → A) (e : G.Edge) :
    G.gluingCoboundary A c e = c (G.endpoint e 1) / c (G.endpoint e 0) :=
  (rfl)

section Cycle

variable {n : ℕ} [NeZero n]

@[simp]
theorem gluingCoboundary_cycle_apply (c : ZMod n → A) (i : ZMod n) :
    (cycle n).gluingCoboundary A c i = c (i + 1) / c i :=
  (rfl)

/-- The product of the changes in gluing scalars around the cycle is one. -/
@[simp]
theorem prod_gluingCoboundary_cycle (c : ZMod n → A) :
    ∏ i : ZMod n, (cycle n).gluingCoboundary A c i = 1 := by
  calc
    _ = ∏ i : ZMod n, c (i + 1) / c i :=
      prod_congr rfl fun i _ ↦ gluingCoboundary_cycle_apply c i
    _ = 1 := by
      rw [prod_div_distrib, div_eq_one]
      exact Equiv.prod_comp (Equiv.addRight (1 : ZMod n)) c

/-- Gluing constants with product one have a unique vertex rescaling
whose scalar at vertex zero is one. -/
theorem existsUnique_gluingCoboundary_cycle (b : ZMod n → A)
    (hb : ∏ i : ZMod n, b i = 1) :
    ∃! c : ZMod n → A, c 0 = 1 ∧ (cycle n).gluingCoboundary A c = b := by
  let p (j : ℕ) := ∏ k ∈ range j, b (k : ZMod n)
  let c (i : ZMod n) := p i.val
  have hc : c 0 = 1 := by simp [c, p]
  have hprod : p n = ∏ i : ZMod n, b i := by
    dsimp only [p]
    rw [← Fin.prod_univ_eq_prod_range (fun j ↦ b (j : ZMod n)) n]
    refine Fintype.prod_equiv (ZMod.finEquiv n).toEquiv _ _ fun i ↦ congrArg b ?_
    have hi : ((ZMod.finEquiv n).toEquiv i).val = i.val := by
      cases n with
      | zero => exact i.elim0
      | succ n => rfl
    rw [← hi, ZMod.natCast_zmod_val]
  -- The final prefix product agrees with the value at vertex zero.
  have hcast (j : ℕ) (hj : j ≤ n) : c (j : ZMod n) = p j := by
    obtain h | rfl := lt_or_eq_of_le hj
    · simp [c, ZMod.val_natCast_of_lt h]
    · simp only [ZMod.natCast_self, hc, hprod, hb]
  refine ⟨c, ⟨hc, funext fun i ↦ ?_⟩, ?_⟩
  · have h := hcast (i.val + 1) (ZMod.val_lt i)
    rw [Nat.cast_succ, ZMod.natCast_zmod_val] at h
    rw [gluingCoboundary_cycle_apply, h]
    exact (prod_range_succ_div_prod (f := fun j ↦ b (j : ZMod n)) (n := i.val)).trans
      (congrArg b (ZMod.natCast_zmod_val i))
  · rintro d ⟨hd₀, hd⟩
    have h (j : ℕ) : d (j : ZMod n) = p j := by
      induction j with
      | zero => simpa [p] using hd₀
      | succ j ih =>
        have hstep := congrFun hd (j : ZMod n)
        rw [gluingCoboundary_cycle_apply] at hstep
        rw [Nat.cast_succ, ← div_mul_cancel (d ((j : ZMod n) + 1)) (d j), hstep, ih]
        exact (mul_comm _ _).trans (prod_range_succ _ _).symm
    funext i
    simpa only [ZMod.natCast_zmod_val] using h i.val

/-- Two assignments of gluing scalars have the same product precisely when a
unique rescaling normalized at vertex zero takes the first assignment to the second. -/
theorem prod_eq_prod_iff_exists_unique_rescaling (a b : ZMod n → A) :
    (∏ i, a i) = (∏ i, b i) ↔
      ∃! c : ZMod n → A, c 0 = 1 ∧ ∀ i, b i = a i * (c (i + 1) / c i) := by
  have hrel (c : ZMod n → A) :
      (c 0 = 1 ∧ (cycle n).gluingCoboundary A c = b / a) ↔
        (c 0 = 1 ∧ ∀ i, b i = a i * (c (i + 1) / c i)) := by
    refine and_congr_right fun _ ↦ funext_iff.trans (forall_congr' fun i ↦ ?_)
    rw [gluingCoboundary_cycle_apply, Pi.div_apply, eq_div_iff_mul_eq', mul_comm, eq_comm]
  rw [← existsUnique_congr hrel]
  constructor
  · intro h
    apply existsUnique_gluingCoboundary_cycle
    simp only [Pi.div_apply, Finset.prod_div_distrib, ← h, div_self']
  · rintro ⟨c, ⟨-, hc⟩, -⟩
    have h := prod_gluingCoboundary_cycle c
    rw [hc] at h
    simp only [Pi.div_apply, Finset.prod_div_distrib, div_eq_one] at h
    exact h.symm

private def edgeProduct (n : ℕ) [NeZero n] (A : Type*) [CommGroup A] :
    (ZMod n → A) →* A :=
  ∏ i : ZMod n, Pi.evalMonoidHom (fun _ ↦ A) i

private theorem edgeProduct_apply (a : ZMod n → A) :
    edgeProduct n A a = ∏ i, a i := by
  simp [edgeProduct]

/-- A gluing assignment is a vertex coboundary exactly when its product is one. -/
theorem mem_range_gluingCoboundary_cycle_iff (b : ZMod n → A) :
    b ∈ ((cycle n).gluingCoboundary A).range ↔ ∏ i, b i = 1 := by
  rw [MonoidHom.mem_range]
  exact ⟨fun ⟨c, hc⟩ ↦ hc ▸ prod_gluingCoboundary_cycle c, fun hb ↦ by
    obtain ⟨c, ⟨-, hc⟩, -⟩ := existsUnique_gluingCoboundary_cycle b hb
    exact ⟨c, hc⟩⟩

private theorem range_gluingCoboundary_cycle :
    ((cycle n).gluingCoboundary A).range = (edgeProduct n A).ker := by
  ext b
  rw [mem_range_gluingCoboundary_cycle_iff, MonoidHom.mem_ker, edgeProduct_apply]

/-- The product identifies gluing assignments modulo vertex rescaling with the coefficient group. -/
noncomputable def cycleGluingEquiv (n : ℕ) [NeZero n] (A : Type*) [CommGroup A] :
    ((ZMod n → A) ⧸ ((cycle n).gluingCoboundary A).range) ≃* A :=
  (QuotientGroup.quotientMulEquivOfEq range_gluingCoboundary_cycle).trans
    (QuotientGroup.quotientKerEquivOfSurjective (edgeProduct n A) (fun a ↦
      ⟨Pi.mulSingle 0 a, by rw [edgeProduct_apply]; simp⟩))

@[simp]
theorem cycleGluingEquiv_mk (a : ZMod n → A) :
    cycleGluingEquiv n A (QuotientGroup.mk a) = ∏ i, a i := by
  rw [cycleGluingEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  exact edgeProduct_apply a

/-- A product can be represented by placing it on any one edge and placing one on the others. -/
theorem cycleGluingEquiv_symm_apply (a : A) (i : ZMod n) :
    (cycleGluingEquiv n A).symm a = QuotientGroup.mk (Pi.mulSingle i a) := by
  apply (cycleGluingEquiv n A).injective
  rw [MulEquiv.apply_symm_apply, cycleGluingEquiv_mk]
  simp

/-- Choosing a different first vertex leaves the product unchanged. -/
theorem cycleGluingEquiv_rotate (a : ZMod n → A) (t : ZMod n) :
    cycleGluingEquiv n A (QuotientGroup.mk (fun i ↦ a (i + t))) =
      cycleGluingEquiv n A (QuotientGroup.mk a) := by
  rw [cycleGluingEquiv_mk, cycleGluingEquiv_mk]
  exact Equiv.prod_comp (Equiv.addRight t) a

/-- Reversing the orientation sends the edge from `i` to `i + 1` to the edge
from `t - 1 - i` to `t - i`, with its direction reversed. -/
theorem cycleGluingEquiv_reverse (a : ZMod n → A) (t : ZMod n) :
    cycleGluingEquiv n A (QuotientGroup.mk (fun i ↦ (a (t - 1 - i))⁻¹)) =
      (cycleGluingEquiv n A (QuotientGroup.mk a))⁻¹ := by
  rw [cycleGluingEquiv_mk, cycleGluingEquiv_mk, prod_inv_distrib]
  exact congrArg Inv.inv (Equiv.prod_comp (Equiv.subLeft (t - 1)) a)

end Cycle

end TauCeti.DualGraph
