/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Word
public import QPainleve.Algebra.Cluster.Word.Monomial

/-!
# Signed cluster words on charge monomials

The Laurent monomial of a charge relation pulls back to the monomial of the transported
relation. This is the restriction of the monomial action on the exchange kernel.
The restriction along a reversed word is the inverse on the charge kernel.
-/

public noncomputable section

open Quiver

namespace QPainleve.Cluster

open CharacterTorus

variable (k : Type*) [Field k] {ι : Type*} [Fintype ι]
variable [DecidableEq ι] {N : Type*} [AddCommGroup N] {B : SkewExchangeMatrix ι}

/-- Pulling a monomial from the mutated charge kernel back to the original torus
uses the same exponent substitution as the integral change of basis. -/
theorem xMutation_apply_chargeMonomial (P : ChargeSeed B N) (j : ι)
    (x : (Step.chargeTarget ((Generator.mutate j).toStep B) P).charge.ker) :
    xMutation k j (fun i ↦ B.matrix i j)
      (monomial k (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (x : ι → ℤ)))) =
    monomial k (Multiplicative.ofAdd
      (Finsupp.equivFunOnFinite.symm (Step.exponentEquiv ((Generator.mutate j).toStep B)
        (x : ι → ℤ)))) := by
  let step := (Generator.mutate j).toStep B
  simpa only [step, Step.xPullback_toStep, Generator.xPullback_mutate, Submodule.coe_inclusion]
    using Step.xPullback_apply_monomial k step
      (Submodule.inclusion (Step.chargeTarget step P).ker_le_exchangeKernel x)

end QPainleve.Cluster

namespace Quiver.Path

open QPainleve QPainleve.Cluster CharacterTorus

variable (k : Type*) [Field k] {ι N : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup N]
variable {B C : SkewExchangeMatrix ι}

/-- A signed word pulls back the monomial of a terminal charge relation by the integral
transport on the charge kernel. -/
theorem xPullback_apply_chargeMonomial (w : Word B C) (P : ChargeSeed B N)
    (x : (w.chargeTarget P).charge.ker) :
    w.xPullback k (monomial k (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (x : ι → ℤ)))) =
      monomial k (Multiplicative.ofAdd
        (Finsupp.equivFunOnFinite.symm (w.chargeKernelEquiv P x : ι → ℤ))) := by
  simpa only [coe_exchangeKernelEquiv_apply, Submodule.coe_inclusion, coe_chargeKernelEquiv_apply]
    using w.xPullback_apply_monomial k
      (Submodule.inclusion (w.chargeTarget P).ker_le_exchangeKernel x)

/-- Going along a word and back restores the original charge kernel. -/
@[simp]
theorem chargeTarget_reverse_ker (w : Word B C) (P : ChargeSeed B N) :
    (w.reverse.chargeTarget (w.chargeTarget P)).charge.ker = P.charge.ker := by
  rw [← chargeTarget_comp]
  ext x
  have hcomp : (w.comp w.reverse).exchangeKernelEquiv = LinearEquiv.refl ℤ _ := by simp
  have h (hx : x ∈ B.matrix.mulVecLin.ker) : (w.comp w.reverse).exponentEquiv x = x := by
    simpa only [coe_exchangeKernelEquiv_apply, LinearEquiv.refl_apply] using
      congrArg Subtype.val (DFunLike.congr_fun hcomp ⟨x, hx⟩)
  constructor
  · intro hx
    simpa only [chargeTarget_ker, Submodule.mem_comap, LinearEquiv.coe_coe,
      h (((w.comp w.reverse).chargeTarget P).ker_le_exchangeKernel hx)] using hx
  · intro hx
    simpa only [chargeTarget_ker, Submodule.mem_comap, LinearEquiv.coe_coe,
      h (P.ker_le_exchangeKernel hx)] using hx

/-- Under the identification of the charge kernels at the two ends of a round trip,
transport along the reverse word is the inverse transport. -/
theorem chargeKernelEquiv_reverse (w : Word B C) (P : ChargeSeed B N) :
    w.reverse.chargeKernelEquiv (w.chargeTarget P) =
      (LinearEquiv.ofEq _ _ (w.chargeTarget_reverse_ker P)).trans (w.chargeKernelEquiv P).symm := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  have hx := (w.reverse.chargeTarget (w.chargeTarget P)).ker_le_exchangeKernel x.property
  simpa only [coe_exchangeKernelEquiv_apply, coe_exchangeKernelEquiv_symm_apply,
    coe_chargeKernelEquiv_apply, LinearEquiv.trans_apply, coe_chargeKernelEquiv_symm_apply,
    LinearEquiv.coe_ofEq_apply] using
    congrArg Subtype.val (DFunLike.congr_fun (exchangeKernelEquiv_reverse w) ⟨x, hx⟩)

end Quiver.Path
