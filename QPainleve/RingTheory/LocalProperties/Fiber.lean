/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Surjectivity from fibers at maximal ideals

For a map into a finite module, surjectivity can be checked over the residue
fields at maximal ideals. This is the closed-point form of the fiber criterion
in `TauCeti.RingTheory.LocalProperties.Fiber`.
-/

public section

open scoped TensorProduct

namespace LinearMap

/-- A linear map into a finite module is surjective if it is surjective after
tensoring with the residue field of each maximal ideal. -/
theorem surjective_of_lTensor_residueField_maximal {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Finite R N]
    (f : M →ₗ[R] N) (h : ∀ (m : Ideal R) [m.IsMaximal],
      Function.Surjective (f.lTensor m.ResidueField)) :
    Function.Surjective f := by
  rw [← range_eq_top, ← Submodule.Quotient.subsingleton_iff,
    ← Module.support_eq_empty_iff (R := R)]
  refine Set.eq_empty_iff_forall_notMem.mpr fun p hp ↦ ?_
  obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
  let := hm
  have hmem := Module.mem_support_mono (M := N ⧸ range f) (q := ⟨m, hm.isPrime⟩) hpm hp
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hmem
  have hzero (z : m.ResidueField ⊗[R] (N ⧸ range f)) : z = 0 := by
    obtain ⟨y, rfl⟩ := lTensor_surjective m.ResidueField (range f).mkQ_surjective z
    obtain ⟨x, rfl⟩ := h m y
    rw [← comp_apply, ← lTensor_comp, range_mkQ_comp, lTensor_zero, LinearMap.zero_apply]
  obtain ⟨x, y, hxy⟩ := hmem.exists_pair_ne
  exact hxy ((hzero x).trans (hzero y).symm)

end LinearMap
