/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Unramified.Basic

import Mathlib.RingTheory.LocalRing.Module
import TauCeti.RingTheory.Kaehler.Hypersurface

/-!
# Differential bases from local equations

A set of local equations for an unramified closed subscheme gives a basis
of differentials when its size is the rank of the free module of ambient
differentials. The residue-field calculation uses the conormal sequence
in `span_one_tmul_D_eq_top_of_formallyUnramified`.
-/

public section

open KaehlerDifferential IsLocalRing TauCeti TensorProduct

namespace Module.Basis

/-- In a local algebra with free differentials, equations vanishing at the closed
point whose common quotient is formally unramified have basic differentials if
there are as many equations as the rank of the differential module. -/
theorem exists_basis_kaehlerDifferential_of_formallyUnramified_quotient
    {k R ι : Type*} [CommRing k] [CommRing R] [IsLocalRing R] [Algebra k R]
    [Finite ι] (b : Basis ι R Ω[R⁄k]) (x : ι → R)
    (hx : ∀ i, x i ∈ maximalIdeal R)
    [Algebra.FormallyUnramified k (R ⧸ Ideal.span (Set.range x))] :
    ∃ b' : Basis ι R Ω[R⁄k], ∀ i, b' i = D k R (x i) := by
  classical
  let := Fintype.ofFinite ι
  let K := ResidueField R
  let v : ι → Ω[R⁄k] := D k R ∘ x
  have hv : Submodule.span K (Set.range (TensorProduct.mk R K Ω[R⁄k] 1 ∘ v)) = ⊤ := by
    rw [Set.range_comp, Set.range_comp]
    simpa only [Set.image_image, TensorProduct.mk_apply] using
      span_one_tmul_D_eq_top_of_formallyUnramified (K := k) (Set.range x) K (by
        rintro _ ⟨i, rfl⟩
        exact (residue_eq_zero_iff _).mpr (hx i))
  let f := Finsupp.linearCombination K (TensorProduct.mk R K Ω[R⁄k] 1 ∘ v)
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hv
  have hd : Module.finrank K (ι →₀ K) = Module.finrank K (K ⊗[R] Ω[R⁄k]) := by
    rw [Module.finrank_eq_card_basis (Finsupp.basisSingleOne : Basis ι K (ι →₀ K)),
      Module.finrank_eq_card_basis (b.baseChange K)]
  let := Module.Finite.of_basis b
  let := Module.Free.of_basis b
  let e := LinearEquiv.ofBijective _ (IsLocalRing.linearCombination_bijective_of_flat v
    ⟨(f.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hf, hf⟩)
  exact ⟨(Finsupp.basisSingleOne : Basis ι R (ι →₀ R)).map e, fun i ↦ by simp [e, v]⟩

end Module.Basis
