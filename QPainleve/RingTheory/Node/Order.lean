/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.Unramified.Basic
public import TauCeti.RingTheory.FittingIdeal.BaseChange
public import TauCeti.RingTheory.Ideal.Order
import TauCeti.RingTheory.LocalRing.Coordinates
import TauCeti.RingTheory.Node.Cotangent.Basic
import TauCeti.RingTheory.Node.Hessian

/-!
# Order of a nodal hypersurface

An intrinsic node of a hypersurface in a smooth surface has order two in the ambient
local ring. The first Fitting ideal of the curve differentials detects the node.
Tau Ceti's Hessian criterion computes its quadratic part in ambient coordinates.

See [Stacks Project, Lemma 53.19.7](https://stacks.math.columbia.edu/tag/0C46) for
the intrinsic Fitting-ideal criterion for nodes.
-/

public section

open IsLocalRing KaehlerDifferential TauCeti

namespace QPainleve

/-- A hypersurface in a local algebra with a basis of two differentials has order two
at a node, detected by a proper first Fitting ideal with formally unramified quotient. -/
theorem localOrder_ker_eq_two_of_fittingIdeal
    {k P A : Type*} [Field k] [CommRing P] [IsLocalRing P] [Algebra k P]
    [CommRing A] [IsLocalRing A] [Algebra k A]
    [Algebra.EssFiniteType k A]
    [Algebra.FormallyUnramified k (A ⧸ fittingIdeal A Ω[A⁄k] 1)]
    (hfg : (maximalIdeal P).FG) (b : Module.Basis (Fin 2) P Ω[P⁄k])
    (π : P →ₐ[k] A) (hπ : Function.Surjective π)
    {f : P} (hker : RingHom.ker π = Ideal.span {f})
    (hnode : fittingIdeal A Ω[A⁄k] 1 ≠ ⊤) :
    (RingHom.ker π).localOrder = 2 := by
  let e := (Ideal.quotientEquivAlgOfEq k hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hπ)
  have : Algebra.EssFiniteType k (P ⧸ Ideal.span {f}) :=
    .of_surjective e.symm.toAlgHom e.symm.surjective
  have hfit := fittingIdeal_kaehlerDifferential_eq_map_algEquiv e 1
  have hcard : Fintype.card (Fin 2) - 1 = 1 := by simp
  have : Algebra.FormallyUnramified k
      ((P ⧸ Ideal.span {f}) ⧸
        fittingIdeal _ Ω[(P ⧸ Ideal.span {f})⁄k] (Fintype.card (Fin 2) - 1)) :=
    hcard ▸ .of_equiv (Ideal.quotientEquivAlg _ _ e hfit).symm
  have hfitProper : fittingIdeal (P ⧸ Ideal.span {f}) Ω[(P ⧸ Ideal.span {f})⁄k] 1 ≠ ⊤ := by
    intro h
    exact hnode (by rw [hfit, h, Ideal.map_top])
  have : IsLocalHom π := ⟨(IsLocalHom.of_surjective (π : P →+* A) hπ).map_nonunit⟩
  have : Algebra.FormallyEtale k (ResidueField A) :=
    formallyEtale_residueField_of_fittingIdeal_ne_top hnode
  have hbij : Function.Bijective (ResidueField.mapAlgHom π) := by
    refine ⟨RingHom.injective _, fun z ↦ ?_⟩
    obtain ⟨p, rfl⟩ := (residue_surjective.comp hπ) z
    exact ⟨residue P p, ResidueField.mapAlgHom_residue π p⟩
  have : Algebra.FormallyEtale k (ResidueField P) :=
    .of_equiv (AlgEquiv.ofBijective _ hbij).symm
  obtain ⟨x, b', hx, hb⟩ := exists_coordinates hfg b
  obtain ⟨hf₂, hHessian⟩ :=
    mem_maximalIdeal_sq_and_isUnit_det_hessian_of_formallyUnramified b' hx hb
      (by simpa only [hcard] using hfitProper)
  have hf₃ : f ∉ maximalIdeal P ^ 3 := by
    intro hf
    let d (i : Fin 2) := (b'.coord i).compDer (D k P)
    have hentry (i j : Fin 2) : residue P (d i (d j f)) = 0 := by
      apply (residue_eq_zero_iff _).mpr
      apply (d i).apply_mem_of_mem_sq
      simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using
        (d j).apply_mem_pow_smul_top_of_mem_pow_succ (n := 2) hf
    have hzero : (residue P).mapMatrix (hessian d f) = 0 := by
      ext i j
      simp [RingHom.mapMatrix_apply, hessian_apply, hentry]
    have hunit : IsUnit ((residue P) (hessian d f).det) := hHessian.map (residue P)
    rw [RingHom.map_det, hzero, Matrix.det_zero] at hunit
    exact not_isUnit_zero hunit
  rw [hker]
  apply le_antisymm
  · by_contra! h
    have h₃ : (3 : ℕ∞) ≤ (Ideal.span {f}).localOrder := by
      rw [show (3 : ℕ∞) = (2 : ℕ∞) + 1 by decide]
      exact ENat.natCast_add_one_le_iff.mpr h
    exact hf₃ ((Ideal.natCast_le_localOrder_iff (Ideal.span {f}) 3).mp h₃
      (Ideal.mem_span_singleton_self f))
  · exact (Ideal.natCast_le_localOrder_iff (Ideal.span {f}) 2).mpr
      ((Ideal.span_singleton_le_iff_mem _).mpr hf₂)

end QPainleve
