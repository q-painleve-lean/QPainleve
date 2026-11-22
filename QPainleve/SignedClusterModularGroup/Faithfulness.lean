/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import QPainleve.LinearAlgebra.BilinearForm.Isometry
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange
public import Mathlib.Data.ZMod.Basic

/-!
# Faithfulness of boundary isometries

When the boundary span and its orthogonal complement rationally generate the orthogonal complement
of the total class, an isometry is determined by its action on the boundary and on its orthogonal
lattice. For a signed cyclic permutation of the boundary, the sign and the forward image of
component zero recover the entire boundary pullback.
-/

public section

open LinearMap Submodule TensorProduct

namespace QPainleve

/-- For a signed shift of the boundary, the index of the class pulled back to component zero
specifies the pullback of every component. -/
theorem boundary_pullback_eq_smul_sub_iff {L : Type*} {n : ℕ} {D : ZMod n → L}
    {g : L → L} {η : ℤˣ} {j : ZMod n}
    (hD : Function.Injective D) (hg : ∃ k : ZMod n, ∀ i, g (D i) = D (η • i + k)) :
    (∀ i, g (D i) = D (η • (i - j))) ↔ g (D j) = D 0 := by
  refine ⟨fun h ↦ by simpa using h j, ?_⟩
  obtain ⟨k, hk⟩ := hg
  intro hj i
  have hshift : η • j + k = 0 := hD ((hk j).symm.trans hj)
  simpa only [sub_eq_add_neg, smul_add, smul_neg, eq_neg_of_add_eq_zero_right hshift] using hk i

variable {L : Type*} [AddCommGroup L] [Module ℤ L] {B : LinearMap.BilinForm ℤ L}
  {n : ℕ} [NeZero n] {D : ZMod n → L}

local notation "M" => span ℤ (Set.range D)
local notation "δ" => ∑ i : ZMod n, D i

/-- Agreement on the boundary components and on the boundary orthogonal lattice determines the
whole isometry once those sublattices rationally span the orthogonal complement of the total
boundary class. -/
theorem boundary_isometry_ext {g h : B.IsometryEquiv B}
    (hSymm : B.IsSymm) (hsep : B.SeparatingLeft)
    (hspan : (M).baseChange ℚ ⊔ (B.orthogonal M).baseChange ℚ =
      (B.baseChange ℚ).orthogonal ((ℤ ∙ δ).baseChange ℚ))
    (hD : ∀ i, g (D i) = h (D i))
    (horth : Set.EqOn g h (B.orthogonal M)) :
    g = h := by
  let gQ := g.baseChange ℚ
  let hQ := h.baseChange ℚ
  let u := TensorProduct.mk ℤ ℚ L 1
  have hDspan : Set.EqOn g h M :=
    LinearMap.eqOn_span' (f := (g : L →ₗ[ℤ] L)) (g := (h : L →ₗ[ℤ] L))
      (by rintro _ ⟨i, rfl⟩; exact hD i)
  have hbase (W : Submodule ℤ L) (hW : Set.EqOn g h W) :
      Set.EqOn gQ hQ (W.baseChange ℚ) := by
    rw [baseChange_eq_span]
    refine LinearMap.eqOn_span'
      (f := (gQ : (ℚ ⊗[ℤ] L) →ₗ[ℚ] (ℚ ⊗[ℤ] L)))
      (g := (hQ : (ℚ ⊗[ℤ] L) →ₗ[ℚ] (ℚ ⊗[ℤ] L))) ?_
    rintro _ ⟨x, hx, rfl⟩
    simp [gQ, hQ, hW hx]
  have hδM : δ ∈ M := (M).sum_mem fun i _ ↦ subset_span (Set.mem_range_self i)
  have hline : (ℤ ∙ δ).baseChange ℚ = ℚ ∙ u δ := by simp [baseChange_span, u]
  have hδ : (B.baseChange ℚ) (u δ) (u δ) = 0 := by
    have hm : u δ ∈ (B.baseChange ℚ).orthogonal ((ℤ ∙ δ).baseChange ℚ) :=
      hspan ▸ (le_sup_left (a := (M).baseChange ℚ) (b := (B.orthogonal M).baseChange ℚ))
        (tmul_mem_baseChange_of_mem (1 : ℚ) hδM)
    exact BilinForm.mem_orthogonal_iff.mp hm _ (hline ▸ mem_span_singleton_self _)
  have heqQ : gQ = hQ := by
    refine BilinForm.IsometryEquiv.ext_of_eqOn_orthogonal_span_singleton
      (BilinForm.isSymm_iff.mpr (BilinForm.IsSymm.baseChange ℚ (BilinForm.isSymm_iff.mp hSymm)))
      (hsep.baseChange_of_isLocalization ℚ (nonZeroDivisors ℤ)) hδ ?_
    intro x hx
    rw [← hline, ← hspan] at hx
    exact LinearMap.eqOn_sup (hbase M hDspan) (hbase _ horth) hx
  refine DFunLike.ext _ _ fun x ↦ ?_
  apply (ker_eq_bot.mp (separatingLeft_iff_ker_eq_bot.mp hsep))
  refine LinearMap.ext fun y ↦ ?_
  have hx := DFunLike.congr_fun heqQ (u x)
  have hp := congrArg (fun z ↦ (B.baseChange ℚ) z (u y)) hx
  simpa [gQ, hQ, u] using hp

/-- Two signed boundary isometries are equal exactly when their signs, their sign-adjusted
restrictions to the boundary orthogonal lattice, and the forward indices of component zero
agree. The boundary formulas are for pullback, so the forward indices are the indices whose
classes pull back to the component of index zero. -/
theorem signed_boundary_isometry_eq_iff {g h : B.IsometryEquiv B}
    {η η' : ℤˣ} {j j' : ZMod n}
    (hSymm : B.IsSymm) (hsep : B.SeparatingLeft)
    (hspan : (M).baseChange ℚ ⊔ (B.orthogonal M).baseChange ℚ =
      (B.baseChange ℚ).orthogonal ((ℤ ∙ δ).baseChange ℚ))
    (hD : Function.Injective D)
    (hg : ∀ i, g (D i) = D (η • (i - j)))
    (hh : ∀ i, h (D i) = D (η' • (i - j'))) :
    (g, η) = (h, η') ↔
      η = η' ∧ (∀ κ ∈ B.orthogonal M, η • g κ = η' • h κ) ∧ j = j' := by
  constructor
  · intro heq
    obtain rfl : g = h := congrArg Prod.fst heq
    obtain rfl : η = η' := congrArg Prod.snd heq
    have hg0 : g (D j) = D 0 := by simpa using hg j
    have hh0 : g (D j') = D 0 := by simpa using hh j'
    exact ⟨rfl, fun _ _ ↦ rfl, hD (EquivLike.injective g (hg0.trans hh0.symm))⟩
  · rintro ⟨rfl, horth, rfl⟩
    exact Prod.ext (boundary_isometry_ext hSymm hsep hspan (fun i ↦ (hg i).trans (hh i).symm)
      (fun κ hκ ↦ smul_left_cancel η (horth κ hκ))) rfl

/-- A boundary rotation is determined by its restriction to the boundary orthogonal lattice and
the pullback of the component of index zero. -/
theorem boundary_rotation_isometry_eq_iff {g h : B.IsometryEquiv B} {k k' : ZMod n}
    (hSymm : B.IsSymm) (hsep : B.SeparatingLeft)
    (hspan : (M).baseChange ℚ ⊔ (B.orthogonal M).baseChange ℚ =
      (B.baseChange ℚ).orthogonal ((ℤ ∙ δ).baseChange ℚ))
    (hD : Function.Injective D)
    (hg : ∀ i, g (D i) = D (i + k)) (hh : ∀ i, h (D i) = D (i + k')) :
    g = h ↔ Set.EqOn g h (B.orthogonal M) ∧ g (D 0) = h (D 0) := by
  refine ⟨fun heq ↦ heq ▸ ⟨fun {_} _ ↦ rfl, rfl⟩, ?_⟩
  rintro ⟨horth, hzero⟩
  have hk : k = k' := hD (by simpa only [hg, hh, zero_add] using hzero)
  subst k'
  exact boundary_isometry_ext hSymm hsep hspan (fun i ↦ (hg i).trans (hh i).symm) horth

end QPainleve
