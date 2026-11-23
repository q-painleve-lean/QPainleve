/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Exponent
public import QPainleve.Algebra.Cluster.Word.Pullback

/-!
# Monomial pullback on exchange kernels

The pullback along a signed word takes a monomial in the terminal exchange kernel to the
monomial of its transported exponent. The monomial action uses the X mutation formula of
Fock and Goncharov, *Cluster ensembles, quantization and the dilogarithm*, §1.2.4.
Independence of the character monomials makes this exponent action intrinsic to the
function-field pullback and identifies the reversed action with its inverse.
-/

public section

open Quiver QPainleve

variable (k : Type*) [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "χ" => fun x : ι → ℤ ↦
  CharacterTorus.monomial k (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm x))

namespace QPainleve.Cluster.Step

open scoped Int

variable {B C : SkewExchangeMatrix ι}

private theorem xMutation_apply_monomial (B : SkewExchangeMatrix ι) (p : ι) {x : ι → ℤ}
    (hx : x ∈ (B.mutate p).matrix.mulVecLin.ker) :
    xMutation k p (fun i ↦ B.matrix i p) (χ x) =
      χ (chargeMutationEquiv B.matrix p x) := by
  have hx' : x ∈ (B.val.mutation p).matrix.mulVecLin.ker := by
    rw [← SkewExchangeMatrix.val_mutate]
    simpa [SkewExchangeMatrix.val_matrix, LinearMap.mem_ker] using hx
  have h := prod_zpow_xMutation_eq B.val p hx' (xCoordinate k)
    (xCoordinate_ne_zero k p) (one_add_xCoordinate_ne_zero k p)
  simp only [monomial_eq_prod_zpow_xCoordinate, map_prod, map_zpow₀]
  simp only [B.val_matrix_apply_swap] at h
  rw [B.val_matrix, neg_neg] at h
  refine .trans (Finset.prod_congr rfl fun i _ ↦ ?_) h
  by_cases hi : i = p
  · subst i
    simp
  · simp [hi, xMutation_apply_of_ne, posPart_def]

/-- A signed step pulls back an exchange-kernel monomial by its integral exponent substitution. -/
theorem xPullback_apply_monomial (s : B ⟶ C) (x : C.matrix.mulVecLin.ker) :
    s.xPullback k (χ (x : ι → ℤ)) = χ (s.exponentEquiv (x : ι → ℤ)) := by
  obtain ⟨g, rfl⟩ := s
  have hs : g.toStep B = (⟨g, rfl⟩ : Step B (g.target B)) :=
    Step.ext (g.toStep_generator B)
  rw [← hs]
  cases g with
  | mutate p =>
    simpa only [xPullback_toStep, Generator.xPullback_mutate, exponentEquiv_mutate] using
      xMutation_apply_monomial k B p (by simpa only [Generator.target_mutate] using x.property)
  | permute σ =>
    simp only [xPullback_toStep, Generator.xPullback_permute, exponentEquiv_permute,
      xReindex_apply_monomial]
    congr 2
    ext i
    simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, LinearEquiv.funCongrLeft_apply]
  | invert =>
    simp only [xPullback_toStep, Generator.xPullback_invert, exponentEquiv_invert,
      xInversion_apply_monomial]
    congr 2
    ext i
    simp

end QPainleve.Cluster.Step

namespace Quiver.Path

open QPainleve.Cluster

variable {B C : SkewExchangeMatrix ι}

/-- The pulled-back monomial of a terminal exchange relation is the monomial of its
transported exponent, over any coefficient field. -/
theorem xPullback_apply_monomial (w : Word B C) (x : C.matrix.mulVecLin.ker) :
    w.xPullback k (χ (x : ι → ℤ)) = χ (w.exchangeKernelEquiv x : ι → ℤ) := by
  induction w with
  | nil => simp
  | cons w s ih =>
    rw [xPullback_cons, AlgEquiv.mul_apply, Step.xPullback_apply_monomial]
    simpa only [coe_exchangeKernelEquiv_apply, exponentEquiv_toPath, exponentEquiv_cons,
      LinearEquiv.trans_apply] using ih (s.toPath.exchangeKernelEquiv x)

/-- Words with the same endpoints and the same X pullback induce the same integral
equivalence on the exchange kernels. -/
theorem exchangeKernelEquiv_eq_of_xPullback_eq {w v : Word B C}
    (h : w.xPullback k = v.xPullback k) : w.exchangeKernelEquiv = v.exchangeKernelEquiv := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  apply Finsupp.equivFunOnFinite.symm.injective
  apply (CharacterTorus.linearIndependent_monomial (B := ι →₀ ℤ) k).injective
  rw [← xPullback_apply_monomial, ← xPullback_apply_monomial, h]

/-- Reversing a word inverts its transport on the exchange kernels. -/
@[simp]
theorem exchangeKernelEquiv_reverse (w : Word B C) :
    w.reverse.exchangeKernelEquiv = w.exchangeKernelEquiv.symm := by
  have h : (w.comp w.reverse).xPullback ℚ = (Path.nil : Word B B).xPullback ℚ := by simp
  have he := exchangeKernelEquiv_eq_of_xPullback_eq ℚ h
  rw [exchangeKernelEquiv_comp, exchangeKernelEquiv_nil] at he
  simpa only [LinearEquiv.trans_symm_cancel_right, LinearEquiv.refl_trans] using
    congrArg (fun e ↦ e.trans w.exchangeKernelEquiv.symm) he

end Quiver.Path
