/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.CharacterTorus.Scheme

/-!
# Separation of torus characters on open sets

The values on the rational points of a nonempty open of a split torus distinguish
character exponents, even when an unknown constant factor multiplies one character.
-/

public section

open AlgebraicGeometry Multiplicative TopologicalSpace
open TauCeti DiagonalizableGroup

namespace QPainleve.CharacterTorus

universe u

/-- Two characters that are proportional at every rational point of a nonempty open
of a split torus have the same exponent. -/
theorem exponent_eq_of_proportional_on_open {k ι : Type u} [Field k] [IsSepClosed k] [Finite ι]
    {U : (scheme k (ι → ℤ)).Opens} (hU : (U : Set (scheme k (ι → ℤ))).Nonempty)
    {x y : ι → ℤ} {a : kˣ}
    (h : ∀ c : Multiplicative (ι → ℤ) →* kˣ, ((pointsEquiv k (ι → ℤ)).symm c).val default ∈ U →
      c (ofAdd x) = a * c (ofAdd y)) : x = y := by
  classical
  let A := ι → ℤ
  let f : AddMonoidAlgebra k A := AddMonoidAlgebra.single x 1 - AddMonoidAlgebra.single y a.val
  by_contra hxy
  have hf : f ≠ 0 := by
    intro hz
    have hcoeff := congrArg (fun p : AddMonoidAlgebra k A ↦ p.coeff x) hz
    simp [f, hxy] at hcoeff
  let : HasUniqueDiv A := hasUniqueDiv_of_free_int
  let : IrreducibleSpace (scheme k A) := inferInstanceAs (IrreducibleSpace (PrimeSpectrum _))
  let V : (scheme k A).Opens := PrimeSpectrum.basicOpen f
  have hV : (V : Set (scheme k A)).Nonempty :=
    ⟨⟨⊥, Ideal.isPrime_bot⟩, (PrimeSpectrum.mem_basicOpen f _).mpr (by simpa using hf)⟩
  obtain ⟨c, hcU, hcV⟩ := (denseRange_centerPoints k ι).exists_mem_open
    (U.isOpen.inter V.isOpen) (nonempty_preirreducible_inter U.isOpen V.isOpen hU hV)
  have hc := h c hcU
  rw [pointsEquiv_symm_apply_val] at hcV
  let e := (DiagonalizableGroup.point c).comp
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k A).toAlgHom
  let p : PrimeSpectrum k := (default : Spec (CommRingCat.of k))
  let := p.isPrime
  have hp : p.asIdeal = ⊥ := Ideal.eq_bot_of_prime p.asIdeal
  have hv := (PrimeSpectrum.mem_basicOpen f _).mp hcV
  rw [Spec.map_apply] at hv
  apply hv
  -- The comap of the affine point tests membership after evaluation.
  change e f ∈ p.asIdeal
  simp [e, f, hp, DiagonalizableGroup.point_single, hc]

end QPainleve.CharacterTorus
