/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.ModularGroup
import QPainleve.Algebra.Cluster.Tropical.ExchangeForm
import QPainleve.Algebra.Cluster.Tropical.Pullback

/-!
# Inversion parity of cluster X maps

For a nonzero exchange matrix over a field of characteristic zero, the parity of
simultaneous inversions descends to the signed cluster modular group. Tropical
evaluation transports the exchange form with the sign of the word. Equality of
X pullbacks gives equality of these tropical evaluations, so the signed terminal
exchange matrix can be read from the pullback.

The unsigned group embeds as the kernel of the resulting sign homomorphism.
-/

public noncomputable section

open CategoryTheory Quiver QPainleve.Cluster

namespace Quiver.Path

variable {k : Type*} [Field k] [CharZero k] {ι : Type*} [Finite ι] [DecidableEq ι]
  {B C D : SkewExchangeMatrix ι}

/-- Words with equal X pullbacks have equal signed terminal exchange matrices. -/
theorem signed_exchangeMatrix_eq_of_xPullback_eq
    {w : Word B C} {v : Word B D} (h : w.xPullback k = v.xPullback k) :
    ((-1 : ℤ) ^ w.inversionCount) • C.matrix = ((-1 : ℤ) ^ v.inversionCount) • D.matrix := by
  let : Fintype ι := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  let : LinearOrder ι := LinearOrder.lift' e e.injective
  have ht := tropical_eq_of_xPullback_eq (A := Lex (ι → ℤ)) h
  have hw := w.tropical_exchangeForm
  dsimp only at hw
  rw [ht] at hw
  exact hw.symm.trans v.tropical_exchangeForm

/-- Equal X pullbacks of words with the same nonzero terminal exchange matrix have
the same inversion parity. -/
theorem even_inversionCount_iff_of_xPullback_eq
    {w v : Word B C} (hC : C.matrix ≠ 0) (h : w.xPullback k = v.xPullback k) :
    Even w.inversionCount ↔ Even v.inversionCount := by
  obtain ⟨i, j, hij⟩ : ∃ i j, C.matrix i j ≠ 0 := by
    by_contra! hzero
    exact hC (Matrix.ext fun i j ↦ by simp [hzero i j])
  have he := congrArg (fun M : Matrix ι ι ℤ ↦ M i j) (signed_exchangeMatrix_eq_of_xPullback_eq h)
  simp only [Matrix.smul_apply] at he
  have hs := smul_left_injective ℤ hij he
  rw [← neg_one_pow_eq_one_iff_even (n := w.inversionCount) (by decide : (-1 : ℤ) ≠ 1),
    hs, neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤ) ≠ 1)]

end Quiver.Path

namespace QPainleve.Cluster

variable (k : Type*) [Field k] [CharZero k] {ι : Type*} [Finite ι] [DecidableEq ι]
  (B : SkewExchangeMatrix ι)

local notation "Loops" => End (Prefunctor.obj (Paths.of (SkewExchangeMatrix ι)) B)

private def loopInversionSign : Loops →* ℤˣ where
  toFun w := (-1 : ℤˣ) ^ w.asHom.inversionCount
  map_one' := (congrArg ((-1 : ℤˣ) ^ ·) Path.inversionCount_nil).trans (pow_zero _)
  map_mul' w v :=
    (congrArg ((-1 : ℤˣ) ^ ·) (Path.inversionCount_comp v.asHom w.asHom)).trans
      ((pow_add _ _ _).trans (mul_comm _ _))

private theorem ker_signedClusterModularGroupMap_le (hB : B.matrix ≠ 0) :
    Con.ker (signedClusterModularGroupMap k B) ≤ Con.ker (loopInversionSign B) := by
  intro w v h
  have he := (signedClusterModularGroupMap_eq_iff k B w v).mp ((Con.ker_rel _).mp h)
  exact (Con.ker_rel _).mpr (neg_one_pow_congr (Path.even_inversionCount_iff_of_xPullback_eq hB he))

/-- The sign of a signed cluster X map at a nonzero exchange matrix is one for
even words and minus one for odd words. -/
def signedInversionSign (hB : B.matrix ≠ 0) : SignedClusterModularGroup k B →* ℤˣ :=
  ((Con.ker (signedClusterModularGroupMap k B)).lift (loopInversionSign B)
    (ker_signedClusterModularGroupMap_le k B hB)).comp
      (signedLoopQuotientMulEquiv k B).symm.toMonoidHom

@[simp]
theorem signedInversionSign_apply (hB : B.matrix ≠ 0) (w : Loops) :
    signedInversionSign k B hB (signedClusterModularGroupMap k B w) =
      (-1 : ℤˣ) ^ w.asHom.inversionCount := by
  have h := (signedLoopQuotientMulEquiv k B).symm_apply_apply
    (w : (Con.ker (signedClusterModularGroupMap k B)).Quotient)
  rw [signedLoopQuotientMulEquiv_mk] at h
  simp only [signedInversionSign, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, Con.lift_coe]
  rfl

/-- The kernel of the sign is the unsigned subgroup inside the signed point-map group. -/
theorem ker_signedInversionSign (hB : B.matrix ≠ 0) :
    (signedInversionSign k B hB).ker =
      ((unsignedLoopPullbacks k B).subgroupOf (signedLoopPullbacks k B)).op := by
  ext f
  obtain ⟨w, rfl⟩ := signedClusterModularGroupMap_surjective k B f
  simp only [MonoidHom.mem_ker, signedInversionSign_apply, Subgroup.mem_op, Subgroup.mem_subgroupOf,
    signedClusterModularGroupMap_unop_coe, mem_unsignedLoopPullbacks_iff_exists_even]
  rw [neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)]
  exact ⟨fun h ↦ ⟨w.asHom, h, rfl⟩, fun ⟨v, hv, he⟩ ↦
    (Path.even_inversionCount_iff_of_xPullback_eq hB he).mp hv⟩

end QPainleve.Cluster
