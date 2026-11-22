/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Basic
public import QPainleve.Algebra.Cluster.XMutation.Monomial

/-!
# Integral exponents of signed cluster words

A cluster step acts on the exchange-matrix kernel by the integral substitution of exponents
from target to source. The mutation congruence uses the right factor of Tau Ceti's
`matrixMutation_eq_mul`. The kernel action is defined for any skew exchange matrix.
-/

public section

open Quiver
open scoped Matrix

namespace QPainleve.Cluster.Step

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {B C : SkewExchangeMatrix ι}

/-- The integral exponent substitution of a cluster step. For a mutation this gives the
monomial part of the pullback, before accounting for the binomial factor. -/
def exponentEquiv (s : B ⟶ C) : (ι → ℤ) ≃ₗ[ℤ] (ι → ℤ) :=
  match s.generator with
  | .mutate j => chargeMutationEquiv B.matrix j
  | .permute σ => LinearEquiv.funCongrLeft ℤ ℤ σ.symm
  | .invert => LinearEquiv.neg ℤ

@[simp]
theorem exponentEquiv_mutate (B : SkewExchangeMatrix ι) (j : ι) :
    exponentEquiv ((Generator.mutate j).toStep B) = chargeMutationEquiv B.matrix j := by
  rw [exponentEquiv, Generator.toStep_generator]

@[simp]
theorem exponentEquiv_permute (B : SkewExchangeMatrix ι) (σ : Equiv.Perm ι) :
    exponentEquiv ((Generator.permute σ).toStep B) =
      LinearEquiv.funCongrLeft ℤ ℤ σ.symm := by
  rw [exponentEquiv, Generator.toStep_generator]

@[simp]
theorem exponentEquiv_invert (B : SkewExchangeMatrix ι) :
    exponentEquiv (Generator.invert.toStep B) = LinearEquiv.neg ℤ := by
  rw [exponentEquiv, Generator.toStep_generator]

private theorem ker_mutate (B : SkewExchangeMatrix ι) (p : ι) :
    (B.mutate p).matrix.mulVecLin.ker =
      B.matrix.mulVecLin.ker.comap (chargeMutationEquiv B.matrix p).toLinearMap := by
  let F := TauCeti.matrixMutationRight (Function.Embedding.refl ι) (-B.matrix) p 1
  have hmut : (B.mutate p).matrix = Fᵀ * B.matrix * F :=
    (B.mutate_matrix p).trans
      (B.matrix.matrixMutation_eq_transpose_mul_right B.isSkewSymmetrizer p)
  have hFF : Fᵀ * Fᵀ = 1 := by
    rw [← Matrix.transpose_mul, TauCeti.matrixMutationRight_mul_self, Matrix.transpose_one]
  have hinj : Function.Involutive (Fᵀ).mulVecLin := fun x ↦ by
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hFF, Matrix.one_mulVec]
  have hF : F.mulVecLin = (chargeMutationEquiv B.matrix p).toLinearMap :=
    LinearMap.ext fun x ↦ (chargeMutationEquiv_apply B.matrix p x).symm
  rw [hmut, Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.comp_assoc,
    LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hinj.injective),
    LinearMap.ker_comp, hF]

/-- The exchange kernel at the target is the preimage of the exchange kernel at the source
under the exponent substitution of the step. -/
theorem exchangeKernel_comap (s : B ⟶ C) :
    C.matrix.mulVecLin.ker = B.matrix.mulVecLin.ker.comap (exponentEquiv s).toLinearMap := by
  obtain ⟨g, rfl⟩ := s
  cases g with
  | mutate p => simpa [exponentEquiv] using ker_mutate B p
  | permute σ =>
    have h := Matrix.mulVecLin_reindex σ.symm σ.symm B.matrix
    simp only [Matrix.reindex_apply, Equiv.symm_symm] at h
    simp only [exponentEquiv, Generator.target_permute, SkewExchangeMatrix.reindex_matrix,
      Equiv.symm_symm]
    rw [h, LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot.mpr (LinearEquiv.funCongrLeft ℤ ℤ σ).injective),
      LinearMap.ker_comp]
  | invert =>
    ext x
    simp [exponentEquiv, Submodule.mem_comap, LinearMap.mem_ker]

end QPainleve.Cluster.Step

namespace Quiver.Path

open QPainleve.Cluster

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {B C D : SkewExchangeMatrix ι}

/-- Compose the integral exponent substitutions in pullback order. -/
def exponentEquiv : {C : SkewExchangeMatrix ι} → Word B C → (ι → ℤ) ≃ₗ[ℤ] (ι → ℤ)
  | _, .nil => LinearEquiv.refl ℤ _
  | _, .cons w s => (Step.exponentEquiv s).trans w.exponentEquiv

@[simp]
theorem exponentEquiv_nil :
    (Path.nil : Word B B).exponentEquiv = LinearEquiv.refl ℤ _ :=
  (rfl)

@[simp]
theorem exponentEquiv_cons (w : Word B C) (s : C ⟶ D) :
    (w.cons s).exponentEquiv = (Step.exponentEquiv s).trans w.exponentEquiv :=
  (rfl)

@[simp]
theorem exponentEquiv_toPath (s : B ⟶ C) : s.toPath.exponentEquiv = Step.exponentEquiv s := by
  simp [Hom.toPath]

/-- The exponent substitution of a concatenation is the composition in pullback order. -/
@[simp]
theorem exponentEquiv_comp (w : Word B C) (w' : Word C D) :
    (w.comp w').exponentEquiv = w'.exponentEquiv.trans w.exponentEquiv := by
  induction w' with
  | nil => simp
  | cons _ _ ih =>
    simp only [comp_cons, exponentEquiv_cons, ih]
    ext x i
    simp

/-- The terminal exchange kernel is the preimage of the initial exchange kernel under
the composite exponent substitution. -/
theorem exchangeKernel_comap (w : Word B C) :
    C.matrix.mulVecLin.ker = B.matrix.mulVecLin.ker.comap w.exponentEquiv.toLinearMap := by
  induction w with
  | nil => simp
  | cons w s ih =>
    rw [exponentEquiv_cons, LinearEquiv.coe_trans, Submodule.comap_comp, ← ih]
    exact Step.exchangeKernel_comap s

/-- The exponent substitution of a signed word restricts to a linear equivalence
from its terminal exchange kernel to its initial exchange kernel. -/
def exchangeKernelEquiv (w : Word B C) :
    C.matrix.mulVecLin.ker ≃ₗ[ℤ] B.matrix.mulVecLin.ker :=
  (LinearEquiv.ofEq _ _ w.exchangeKernel_comap).trans
    (w.exponentEquiv.ofSubmodule' B.matrix.mulVecLin.ker)

@[simp]
theorem coe_exchangeKernelEquiv_apply (w : Word B C) (x : C.matrix.mulVecLin.ker) :
    (w.exchangeKernelEquiv x : ι → ℤ) = w.exponentEquiv (x : ι → ℤ) :=
  (rfl)

@[simp]
theorem coe_exchangeKernelEquiv_symm_apply (w : Word B C) (x : B.matrix.mulVecLin.ker) :
    (w.exchangeKernelEquiv.symm x : ι → ℤ) = w.exponentEquiv.symm (x : ι → ℤ) :=
  (rfl)

@[simp]
theorem exchangeKernelEquiv_nil :
    (Path.nil : Word B B).exchangeKernelEquiv = LinearEquiv.refl ℤ _ := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  simp

@[simp]
theorem exchangeKernelEquiv_comp (w : Word B C) (v : Word C D) :
    (w.comp v).exchangeKernelEquiv = v.exchangeKernelEquiv.trans w.exchangeKernelEquiv := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  simp

end Quiver.Path
