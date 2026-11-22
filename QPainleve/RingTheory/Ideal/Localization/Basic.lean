/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
import TauCeti.RingTheory.Support.Basic

/-!
# Spreading out ideal inclusions

An inclusion of ideals at a prime holds after inverting a single element outside the prime
when the smaller ideal is finitely generated. The proof uses the finite-module argument in
`Ideal.exists_notMem_smul_le_span_singleton_of_map_le` from Tau Ceti.
-/

public section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- An ideal inclusion that holds after localization at a prime holds after inverting one
element outside the prime, provided the smaller ideal is finitely generated. -/
theorem exists_notMem_map_le_of_map_le_atPrime {P I J : Ideal R} [P.IsPrime] (hI : I.FG)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S P]
    (h : I.map (algebraMap R S) ≤ J.map (algebraMap R S)) :
    ∃ r ∉ P, ∀ {B : Type*} [CommRing B] (f : R →+* B), IsUnit (f r) → I.map f ≤ J.map f := by
  have : Module.Finite R I := Module.Finite.iff_fg.mpr hI
  obtain ⟨r, hr, hkill⟩ := Module.exists_notMem_forall_smul_eq_zero (P := P)
      (I ⧸ Submodule.comap I.subtype J) fun z ↦ by
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨s, hs, hsx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl S J x).mp
      (h (Ideal.mem_map_of_mem _ hx))
    exact ⟨s, hs, by simpa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, smul_eq_mul] using hsx⟩
  refine ⟨r, hr, fun f hu ↦ Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_⟩
  have hx' : r * x ∈ J := by
    simpa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, smul_eq_mul] using hkill (Submodule.Quotient.mk ⟨x, hx⟩)
  exact (unit_mul_mem_iff_mem _ hu).mp (map_mul f r x ▸ mem_map_of_mem f hx')

end Ideal
