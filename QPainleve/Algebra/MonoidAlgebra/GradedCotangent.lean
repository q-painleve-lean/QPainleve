/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

import Mathlib.Algebra.Group.Nat.Units
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.LinearAlgebra.Dimension.Finite
import TauCeti.RingTheory.GradedAlgebra.RegularLocalRing

/-!
# Cotangent classes of indecomposable monomials

A positive natural-number grading on an additive monoid makes its monoid algebra a
connected graded algebra. The classes of the indecomposable nonzero monomials
are linearly independent in the cotangent space of its irrelevant ideal.
-/

public section

namespace AddMonoidAlgebra

variable {M k : Type*} [AddCommMonoid M] (d : M →+ ℕ)
  (hd : ∀ m, d m = 0 → m = 0)

local notation "A" => AddMonoidAlgebra k M
local notation "P" => HomogeneousIdeal.toIdeal (HomogeneousIdeal.irrelevant (gradeBy k d))

section CommSemiring

variable [CommSemiring k]

include hd in
/-- A monoid grading supported only at zero in degree zero gives a connected algebra. -/
theorem mem_bot_of_mem_gradeBy_zero {x : A} (hx : x ∈ gradeBy k d 0) :
    x ∈ (⊥ : Subalgebra k A) := by
  have hgrade : x ∈ grade k (0 : M) := fun m hm ↦ hd _ (hx m hm)
  obtain ⟨c, rfl⟩ := (mem_grade_iff' k 0 x).mp hgrade
  exact Algebra.mem_bot.mpr ⟨c, by simp⟩

end CommSemiring

section CommRing

variable [CommRing k]

private theorem coeff_zero_of_mem_irrelevant {x : A} (hx : x ∈ P) : x.coeff 0 = 0 := by
  let l := (Finsupp.lapply (R := k) (M := k) (0 : M)).comp (coeffLinearEquiv k).toLinearMap
  have hle : (P).toAddSubmonoid ≤ l.ker.toAddSubmonoid := by
    apply (HomogeneousIdeal.toAddSubmonoid_irrelevant_le _).mpr
    intro j hj y hy
    apply Finsupp.notMem_support_iff.mp
    intro hz
    have := (mem_gradeBy_iff k d j y).mp hy hz
    exact hj.ne ((map_zero d).symm.trans this)
  exact hle hx

include hd in
private theorem coeff_eq_zero_of_mem_irrelevant_sq {m : M} (hm : AddIrreducible m)
    {x : A} (hx : x ∈ P ^ 2) : x.coeff m = 0 := by
  classical
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ ?_)
  · apply Finsupp.notMem_support_iff.mp
    intro h
    obtain ⟨u, hu, v, hv, he⟩ := Finset.mem_add.mp (support_coeff_mul_subset a b h)
    have hn {w : M} (h : IsAddUnit w) : w = 0 :=
      hd _ (Nat.isAddUnit_iff.mp (h.map d))
    rcases hm.isAddUnit_or_isAddUnit he.symm with h | h
    · exact Finsupp.mem_support_iff.mp (hn h ▸ hu) (coeff_zero_of_mem_irrelevant d ha)
    · exact Finsupp.mem_support_iff.mp (hn h ▸ hv) (coeff_zero_of_mem_irrelevant d hb)
  · simp [ha, hb]

include hd in
/-- Monomials of additive irreducibles give independent cotangent classes at the
vertex of the positively graded monoid algebra. -/
theorem linearIndependent_toCotangent_single :
    LinearIndependent k (fun m : {m : M // AddIrreducible m} ↦
      (P).toCotangent ⟨single m.val (1 : k), HomogeneousIdeal.mem_irrelevant_of_mem _
        (Nat.pos_of_ne_zero fun h ↦ m.property.ne_zero (hd _ h)) (single_mem_gradeBy d _ _)⟩) := by
  classical
  let v (m : {m : M // AddIrreducible m}) : P :=
    ⟨single m.val (1 : k), HomogeneousIdeal.mem_irrelevant_of_mem _
      (Nat.pos_of_ne_zero fun h ↦ m.property.ne_zero (hd _ h)) (single_mem_gradeBy d _ _)⟩
  rw [linearIndependent_iff']
  intro s g hg m hm
  have hsum : (∑ j ∈ s, g j • v j : P) ∈ LinearMap.ker (P).toCotangent := by
    rw [LinearMap.mem_ker]
    simpa only [map_sum, LinearMap.map_smul_of_tower] using hg
  let l : A →ₗ[k] k := (Finsupp.lapply m.val).comp (coeffLinearEquiv k).toLinearMap
  have h : l (∑ j ∈ s, g j • (v j : A)) = 0 := by
    have h' : l ((∑ j ∈ s, g j • v j : P) : A) = 0 :=
      coeff_eq_zero_of_mem_irrelevant_sq d hd m.property ((P).mem_toCotangent_ker.mp hsum)
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using h'
  have hl (j : {m : M // AddIrreducible m}) : l (v j) = if j = m then 1 else 0 := by
    simp [l, v, Finsupp.single_apply, Subtype.val_inj, eq_comm]
  simpa [hl, Finset.sum_ite_eq', hm] using h

end CommRing

variable [Field k]

include hd in
/-- If the local ring at the vertex is regular, the number of additive irreducibles
is bounded by the Krull dimension of that local ring. -/
theorem finite_addIrreducible_and_card_le_of_isRegularLocalRing
    [hP : (P).IsPrime] [IsRegularLocalRing (Localization.AtPrime (P))]
    {n : ℕ} (hn : ringKrullDim (Localization.AtPrime (P)) ≤ n) :
    Finite {m : M // AddIrreducible m} ∧ Nat.card {m : M // AddIrreducible m} ≤ n := by
  have hfg := IsNoetherian.noetherian (IsLocalRing.maximalIdeal (Localization.AtPrime (P)))
  have hconn (x : A) (hx : x ∈ gradeBy k d 0) := mem_bot_of_mem_gradeBy_zero d hd hx
  let := TauCeti.GradedAlgebra.finite_cotangent_of_fg (gradeBy k d) hconn (P) rfl hfg
  have hi := linearIndependent_toCotangent_single (k := k) d hd
  have hfinite := hi.finite
  let := Fintype.ofFinite {m : M // AddIrreducible m}
  refine ⟨hfinite, ?_⟩
  rw [Nat.card_eq_fintype_card]
  refine hi.fintype_card_le_finrank.trans
    ((TauCeti.GradedAlgebra.finrank_cotangent_le_spanFinrank (gradeBy k d)
      hconn (P) rfl hfg).trans ?_)
  have hdim := IsRegularLocalRing.spanFinrank_maximalIdeal (R := Localization.AtPrime (P))
  exact_mod_cast hdim.trans_le hn

end AddMonoidAlgebra
