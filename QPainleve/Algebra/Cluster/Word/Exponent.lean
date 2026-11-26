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

namespace QPainleve.Cluster.SkewExchangeMatrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The exchange kernel in the new labeling is the preimage of the old kernel
under the coordinate permutation back to the old labels. -/
theorem exchangeKernel_reindex (B : SkewExchangeMatrix ι) (e : ι ≃ κ) :
    (B.reindex e).matrix.mulVecLin.ker =
      B.matrix.mulVecLin.ker.comap (LinearEquiv.funCongrLeft ℤ ℤ e).toLinearMap := by
  rw [reindex_matrix, ← Matrix.reindex_apply e e,
    Matrix.mulVecLin_reindex,
    LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr
      (LinearEquiv.funCongrLeft ℤ ℤ e.symm).injective), LinearMap.ker_comp]

variable [DecidableEq ι] [DecidableEq κ]

/-- Transport exponents in a relabeled exchange kernel back to the original labels. -/
def exchangeKernelReindex (B : SkewExchangeMatrix ι) (e : ι ≃ κ) :
    ((reindexPrefunctor e).obj B).matrix.mulVecLin.ker ≃ₗ[ℤ] B.matrix.mulVecLin.ker :=
  (LinearEquiv.ofEq _ _ (by
    simpa only [reindexPrefunctor_obj] using B.exchangeKernel_reindex e)).trans
    ((LinearEquiv.funCongrLeft ℤ ℤ e).ofSubmodule' B.matrix.mulVecLin.ker)

/-- The kernel equivalence reads the exponent at the new label for each old label. -/
@[simp]
theorem coe_exchangeKernelReindex_apply (B : SkewExchangeMatrix ι) (e : ι ≃ κ)
    (x : ((reindexPrefunctor e).obj B).matrix.mulVecLin.ker) :
    (B.exchangeKernelReindex e x : ι → ℤ) = (x : κ → ℤ) ∘ e :=
  (rfl)

/-- The inverse kernel equivalence reads the original exponents at the new labels. -/
@[simp]
theorem coe_exchangeKernelReindex_symm_apply (B : SkewExchangeMatrix ι) (e : ι ≃ κ)
    (x : B.matrix.mulVecLin.ker) :
    ((B.exchangeKernelReindex e).symm x : κ → ℤ) = (x : ι → ℤ) ∘ e.symm :=
  (rfl)

end QPainleve.Cluster.SkewExchangeMatrix

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

/-- The exponent substitution depends on the generator and source exchange matrix. -/
theorem exponentEquiv_eq (s : Step B C) :
    s.exponentEquiv = match s.generator with
      | .mutate j => chargeMutationEquiv B.matrix j
      | .permute σ => LinearEquiv.funCongrLeft ℤ ℤ σ.symm
      | .invert => LinearEquiv.neg ℤ :=
  (rfl)

@[simp]
theorem exponentEquiv_mutate (B : SkewExchangeMatrix ι) (j : ι) :
    exponentEquiv ((Generator.mutate j).toStep B) = chargeMutationEquiv B.matrix j := by
  rw [exponentEquiv_eq, Generator.toStep_generator]

@[simp]
theorem exponentEquiv_permute (B : SkewExchangeMatrix ι) (σ : Equiv.Perm ι) :
    exponentEquiv ((Generator.permute σ).toStep B) =
      LinearEquiv.funCongrLeft ℤ ℤ σ.symm := by
  rw [exponentEquiv_eq, Generator.toStep_generator]

@[simp]
theorem exponentEquiv_invert (B : SkewExchangeMatrix ι) :
    exponentEquiv (Generator.invert.toStep B) = LinearEquiv.neg ℤ := by
  rw [exponentEquiv_eq, Generator.toStep_generator]

/-- A relabeled step transports the relabeled exponents. -/
theorem exponentEquiv_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (s : B ⟶ C) (e : ι ≃ κ) (x : ι → ℤ) :
    exponentEquiv ((SkewExchangeMatrix.reindexPrefunctor e).map s) (x ∘ e.symm) =
      exponentEquiv s x ∘ e.symm := by
  simp only [exponentEquiv_eq, SkewExchangeMatrix.reindexPrefunctor_map_generator,
    SkewExchangeMatrix.reindexPrefunctor_obj]
  cases s.generator with
  | mutate j => simpa only [Generator.reindex_mutate, SkewExchangeMatrix.reindex_matrix] using
      chargeMutationEquiv_reindex B.matrix e j x
  | permute σ =>
    funext i
    simp [LinearEquiv.funCongrLeft_apply, Function.comp_def, Equiv.symm_trans]
  | invert =>
    funext i
    simp [Generator.reindex_invert]

/-- Casting the endpoints of a step does not change its exponent substitution. -/
@[simp]
theorem exponentEquiv_cast {B' C' : SkewExchangeMatrix ι} (s : B ⟶ C)
    (hB : B = B') (hC : C = C') :
    exponentEquiv (s.cast hB hC) = exponentEquiv s := by
  subst B' C'
  rfl

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
    simpa only [exponentEquiv, Generator.target_permute] using B.exchangeKernel_reindex σ.symm
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

/-- The exponent substitution of a word commutes with changing its labels. -/
theorem exponentEquiv_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (w : Word B C) (e : ι ≃ κ) (x : ι → ℤ) :
    ((SkewExchangeMatrix.reindexPrefunctor e).mapPath w).exponentEquiv (x ∘ e.symm) =
      w.exponentEquiv x ∘ e.symm := by
  induction w generalizing x with
  | nil => simp
  | cons w s ih =>
    rw [Prefunctor.mapPath_cons, exponentEquiv_cons, exponentEquiv_cons, LinearEquiv.trans_apply,
      LinearEquiv.trans_apply, Step.exponentEquiv_reindex, ih]

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

/-- Returning to the old labels commutes with transport along a relabeled word. -/
theorem exchangeKernelEquiv_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (w : Word B C) (e : ι ≃ κ) :
    (((SkewExchangeMatrix.reindexPrefunctor e).mapPath w).exchangeKernelEquiv).trans
      (B.exchangeKernelReindex e) = (C.exchangeKernelReindex e).trans w.exchangeKernelEquiv := by
  ext x i
  simp only [LinearEquiv.trans_apply, SkewExchangeMatrix.coe_exchangeKernelReindex_apply,
    coe_exchangeKernelEquiv_apply]
  have h := w.exponentEquiv_reindex e ((x : κ → ℤ) ∘ e)
  have hx : ((x : κ → ℤ) ∘ e) ∘ e.symm = x := by
    funext j
    simp
  rw [hx] at h
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using congrFun h (e i)

/-- Equality of exchange-kernel transports is independent of the labels. -/
theorem exchangeKernelEquiv_reindex_eq_iff {κ : Type*} [Fintype κ] [DecidableEq κ]
    (w v : Word B C) (e : ι ≃ κ) :
    ((SkewExchangeMatrix.reindexPrefunctor e).mapPath w).exchangeKernelEquiv =
      ((SkewExchangeMatrix.reindexPrefunctor e).mapPath v).exchangeKernelEquiv ↔
      w.exchangeKernelEquiv = v.exchangeKernelEquiv := by
  constructor
  · intro h
    have he := congrArg (fun f ↦ f.trans (B.exchangeKernelReindex e)) h
    rw [w.exchangeKernelEquiv_reindex, v.exchangeKernelEquiv_reindex] at he
    simpa only [LinearEquiv.symm_trans_cancel_left] using
      congrArg (fun f ↦ (C.exchangeKernelReindex e).symm.trans f) he
  · intro h
    have he := (w.exchangeKernelEquiv_reindex e).trans
      ((congrArg ((C.exchangeKernelReindex e).trans) h).trans
        (v.exchangeKernelEquiv_reindex e).symm)
    simpa only [LinearEquiv.trans_symm_cancel_right] using
      congrArg (fun f ↦ f.trans (B.exchangeKernelReindex e).symm) he

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
