/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Basic
public import QPainleve.Algebra.Cluster.Word.Exponent

/-!
# Charge-kernel transport along signed cluster words

A realization of an exchange matrix consists of a charge map and an alternating form on its
target. A signed word determines a terminal realization and a contravariant linear equivalence
on the charge kernels. Inversion negates the form and leaves the charges fixed, while its
pullback on exponents negates them.

The mutation basis change follows Fock and Goncharov, *Cluster ensembles, quantization
and the dilogarithm*, §1.2.2. No spanning condition is needed for kernel transport.
-/

public section

open Quiver

namespace QPainleve.Cluster

open LinearMap (BilinForm)

variable {ι N : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup N]

/-- An alternating charge realization of a skew exchange matrix. -/
@[ext]
structure ChargeSeed (B : SkewExchangeMatrix ι) (N : Type*) [AddCommGroup N] where
  /-- The alternating pairing of charges. -/
  form : BilinForm ℤ N
  /-- The total charge of an exponent vector. -/
  charge : (ι → ℤ) →ₗ[ℤ] N
  /-- The form is alternating. -/
  isAlt : form.IsAlt
  /-- Pairing the basis charges gives the exchange matrix. -/
  matrix_eq : chargeExchangeMatrix form charge = B.matrix

/-- Every charge relation is an exchange relation of the realized matrix. -/
theorem ChargeSeed.ker_le_exchangeKernel {B : SkewExchangeMatrix ι} (P : ChargeSeed B N) :
    P.charge.ker ≤ B.matrix.mulVecLin.ker := by
  rw [← P.matrix_eq]
  exact ker_le_ker_chargeExchangeMatrix P.form P.charge

/-- A charge seed with rationally spanning charges and a right-separating form has
the same charge and exchange kernels. -/
theorem ChargeSeed.exchangeKernel_eq {B : SkewExchangeMatrix ι}
    [Module.Free ℤ N] [Module.Finite ℤ N] (P : ChargeSeed B N)
    (hω : P.form.SeparatingRight) (hrank : Module.finrank ℤ P.charge.range = Module.finrank ℤ N) :
    B.matrix.mulVecLin.ker = P.charge.ker := by
  rw [← P.matrix_eq]
  exact ker_chargeExchangeMatrix P.form P.charge hω hrank

namespace Step

variable {B C : SkewExchangeMatrix ι}

omit [Fintype ι] in
private theorem toStep_eq_mk (g : Generator ι) (B : SkewExchangeMatrix ι) :
    g.toStep B = ⟨g, rfl⟩ :=
  Step.ext (Generator.toStep_generator g B)

/-- Realize the target exchange matrix by mutation of charges, permutation of charges,
or negation of the alternating form. -/
def chargeTarget (s : B ⟶ C) (P : ChargeSeed B N) : ChargeSeed C N := by
  rcases s with ⟨g, rfl⟩
  cases g with
  | mutate j =>
    exact ⟨P.form, chargeMutation P.form P.charge j, P.isAlt, by
      simp only [chargeExchangeMatrix_chargeMutation _ P.isAlt, P.matrix_eq,
        Generator.target_mutate, SkewExchangeMatrix.mutate_matrix]⟩
  | permute σ =>
    refine ⟨P.form, P.charge.comp (LinearEquiv.funCongrLeft ℤ ℤ σ.symm).toLinearMap,
      P.isAlt, ?_⟩
    have hs (i : ι) :
        LinearEquiv.funCongrLeft ℤ ℤ σ.symm (Pi.single i 1) = Pi.single (σ i) 1 := by
      ext j
      simp [LinearEquiv.funCongrLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]
    ext i j
    rw [chargeExchangeMatrix_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, hs, hs, ← chargeExchangeMatrix_apply, P.matrix_eq]
    simp
  | invert =>
    refine ⟨-P.form, P.charge, fun x ↦ by simp [P.isAlt.self_eq_zero], ?_⟩
    ext i j
    rw [Generator.target_invert, SkewExchangeMatrix.neg_matrix, Matrix.neg_apply, ← P.matrix_eq]
    simp

@[simp]
theorem chargeTarget_mutate_form (P : ChargeSeed B N) (j : ι) :
    (chargeTarget ((Generator.mutate j).toStep B) P).form = P.form := by
  rw [toStep_eq_mk]
  rfl

@[simp]
theorem chargeTarget_mutate_charge (P : ChargeSeed B N) (j : ι) :
    (chargeTarget ((Generator.mutate j).toStep B) P).charge =
      chargeMutation P.form P.charge j := by
  rw [toStep_eq_mk]
  rfl

@[simp]
theorem chargeTarget_permute_form (P : ChargeSeed B N) (σ : Equiv.Perm ι) :
    (chargeTarget ((Generator.permute σ).toStep B) P).form = P.form := by
  rw [toStep_eq_mk]
  rfl

@[simp]
theorem chargeTarget_permute_charge (P : ChargeSeed B N) (σ : Equiv.Perm ι) :
    (chargeTarget ((Generator.permute σ).toStep B) P).charge =
      P.charge.comp (LinearEquiv.funCongrLeft ℤ ℤ σ.symm).toLinearMap := by
  rw [toStep_eq_mk]
  rfl

@[simp]
theorem chargeTarget_invert_form (P : ChargeSeed B N) :
    (chargeTarget (Generator.invert.toStep B) P).form = -P.form := by
  rw [toStep_eq_mk]
  rfl

@[simp]
theorem chargeTarget_invert_charge (P : ChargeSeed B N) :
    (chargeTarget (Generator.invert.toStep B) P).charge = P.charge := by
  rw [toStep_eq_mk]
  rfl

/-- The kernel of the new charges is the preimage of the old kernel under exponent transport. -/
theorem chargeTarget_ker (s : B ⟶ C) (P : ChargeSeed B N) :
    (chargeTarget s P).charge.ker = P.charge.ker.comap (exponentEquiv s).toLinearMap := by
  obtain ⟨g, rfl⟩ := s
  rw [← toStep_eq_mk]
  cases g with
  | mutate j =>
    ext x
    simp [Submodule.mem_comap, chargeMutation_apply, P.matrix_eq]
  | permute σ => rw [chargeTarget_permute_charge, exponentEquiv_permute, LinearMap.ker_comp]
  | invert =>
    ext x
    simp [Submodule.mem_comap]

/-- Each cluster step preserves the image of the charges in the ambient lattice. -/
@[simp]
theorem range_chargeTarget (s : B ⟶ C) (P : ChargeSeed B N) :
    (chargeTarget s P).charge.range = P.charge.range := by
  obtain ⟨g, rfl⟩ := s
  rw [← toStep_eq_mk]
  cases g with
  | mutate j => simp
  | permute σ =>
    rw [chargeTarget_permute_charge]
    exact (LinearEquiv.funCongrLeft ℤ ℤ σ.symm).range_comp P.charge
  | invert => simp

end Step

end QPainleve.Cluster

namespace Quiver.Path

open QPainleve.Cluster

variable {ι N : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup N]
variable {B C D : SkewExchangeMatrix ι}

/-- Transport a charge realization through a signed word in execution order. -/
def chargeTarget : {C : SkewExchangeMatrix ι} → Word B C → ChargeSeed B N → ChargeSeed C N
  | _, .nil, P => P
  | _, .cons w s, P => Step.chargeTarget s (w.chargeTarget P)

@[simp]
theorem chargeTarget_nil (P : ChargeSeed B N) :
    (Path.nil : Word B B).chargeTarget P = P :=
  (rfl)

@[simp]
theorem chargeTarget_cons (w : Word B C) (s : C ⟶ D) (P : ChargeSeed B N) :
    (w.cons s).chargeTarget P = Step.chargeTarget s (w.chargeTarget P) :=
  (rfl)

/-- The realization of the endpoint of a concatenation is obtained by transporting in stages. -/
@[simp]
theorem chargeTarget_comp (w : Word B C) (w' : Word C D) (P : ChargeSeed B N) :
    (w.comp w').chargeTarget P = w'.chargeTarget (w.chargeTarget P) := by
  induction w' with
  | nil => simp
  | cons _ _ ih => simp [ih]

/-- Exponent transport pulls the initial charge kernel back to the terminal charge kernel. -/
theorem chargeTarget_ker (w : Word B C) (P : ChargeSeed B N) :
    (w.chargeTarget P).charge.ker = P.charge.ker.comap w.exponentEquiv.toLinearMap := by
  induction w with
  | nil => simp
  | cons w s ih =>
    simp only [chargeTarget_cons, Step.chargeTarget_ker, exponentEquiv_cons,
      LinearEquiv.coe_trans, Submodule.comap_comp, ih]

/-- Equality of the charge and exchange kernels is preserved by every signed word. -/
theorem exchangeKernel_eq_chargeTarget_ker (P : ChargeSeed B N) (w : Word B C)
    (h : B.matrix.mulVecLin.ker = P.charge.ker) :
    C.matrix.mulVecLin.ker = (w.chargeTarget P).charge.ker := by
  rw [w.exchangeKernel_comap, w.chargeTarget_ker, h]

/-- In particular, a word preserves the charge image and its index in the ambient lattice. -/
@[simp]
theorem range_chargeTarget (w : Word B C) (P : ChargeSeed B N) :
    (w.chargeTarget P).charge.range = P.charge.range := by
  induction w with
  | nil => simp
  | cons _ _ ih => simp [ih]

/-- A signed word transports integral charge relations from its target to its source. -/
def chargeKernelEquiv (w : Word B C) (P : ChargeSeed B N) :
    (w.chargeTarget P).charge.ker ≃ₗ[ℤ] P.charge.ker :=
  (LinearEquiv.ofEq _ _ (w.chargeTarget_ker P)).trans
    (w.exponentEquiv.ofSubmodule' P.charge.ker)

@[simp]
theorem coe_chargeKernelEquiv_apply (w : Word B C) (P : ChargeSeed B N)
    (x : (w.chargeTarget P).charge.ker) :
    (w.chargeKernelEquiv P x : ι → ℤ) = w.exponentEquiv (x : ι → ℤ) :=
  (rfl)

@[simp]
theorem coe_chargeKernelEquiv_symm_apply (w : Word B C) (P : ChargeSeed B N)
    (x : P.charge.ker) :
    ((w.chargeKernelEquiv P).symm x : ι → ℤ) = w.exponentEquiv.symm (x : ι → ℤ) :=
  (rfl)

/-- For concatenated words, transport relations through the second word and then the first. -/
theorem chargeKernelEquiv_comp (w : Word B C) (w' : Word C D) (P : ChargeSeed B N) :
    (w.comp w').chargeKernelEquiv P =
      (LinearEquiv.ofEq _ _
        (congrArg (fun Q : ChargeSeed D N ↦ Q.charge.ker) (w.chargeTarget_comp w' P))).trans
        ((w'.chargeKernelEquiv (w.chargeTarget P)).trans (w.chargeKernelEquiv P)) := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  simp

end Quiver.Path
