/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.MonoidAlgebra.FiniteIndex

/-!
# Translations over a finite-index charge sublattice

An automorphism of the function field of a character torus that fixes the
monomials of a finite-index sublattice acts by a unique translation character.
The character is trivial on that sublattice. The result applies over any field
with enough roots of unity for the quotient, including the complex numbers.
The group-algebra result used here is
`MonoidAlgebra.existsUnique_quotient_character_of_fixes_monomials`.
-/

public section

namespace QPainleve.CharacterTorus

open AddMonoidAlgebra Multiplicative

variable (k : Type*) [Field k]
variable {N : Type*} [AddCommGroup N] [HasUniqueDiv N] (H : AddSubgroup N) [Finite (N ⧸ H)]
variable [HasEnoughRootsOfUnity k (Monoid.exponent (Multiplicative (N ⧸ H)))]

local notation "CoordinateRing" => AddMonoidAlgebra k N
local notation "Functions" => FractionRing (AddMonoidAlgebra k N)

/-- An automorphism that fixes the charge monomials acts on every monomial by a unique
character of the quotient of the exponent lattice by the charge sublattice. -/
theorem existsUnique_translation_of_fixes_charge_monomials
    (σ : Functions ≃ₐ[k] Functions)
    (hσ : ∀ n ∈ H, σ (algebraMap CoordinateRing Functions (single n 1)) =
      algebraMap CoordinateRing Functions (single n 1)) :
    ∃! χ : Multiplicative (N ⧸ H) →* kˣ, ∀ n : N,
      σ (algebraMap CoordinateRing Functions (single n 1)) =
        algebraMap CoordinateRing Functions
          (single n (χ (ofAdd (QuotientAddGroup.mk' H n)) : k)) := by
  let e : Functions ≃ₐ[k] FractionRing (MonoidAlgebra k (Multiplicative N)) :=
    IsFractionRing.algEquivOfAlgEquiv (toMultiplicativeAlgEquiv k k N)
  have he (n : N) (a : k) : e (algebraMap CoordinateRing Functions (single n a)) =
      algebraMap (MonoidAlgebra k (Multiplicative N)) _ (MonoidAlgebra.single (ofAdd n) a) := by
    simp [e]
  let τ := (e.symm.trans σ).trans e
  have hfix (n : Multiplicative N) (hn : n ∈ H.toSubgroup) :
      τ (algebraMap (MonoidAlgebra k (Multiplicative N)) _ (MonoidAlgebra.single n 1)) =
        algebraMap (MonoidAlgebra k (Multiplicative N)) _ (MonoidAlgebra.single n 1) := by
    have hn' := he n.toAdd 1
    rw [ofAdd_toAdd] at hn'
    rw [← hn']
    simp only [τ, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, hσ n.toAdd hn]
  let : Finite (Multiplicative N ⧸ H.toSubgroup) := inferInstanceAs (Finite (N ⧸ H))
  let : HasEnoughRootsOfUnity k (Monoid.exponent (Multiplicative N ⧸ H.toSubgroup)) :=
    inferInstanceAs (HasEnoughRootsOfUnity k (Monoid.exponent (Multiplicative (N ⧸ H))))
  obtain ⟨χ, hχ, huniq⟩ :=
    MonoidAlgebra.existsUnique_quotient_character_of_fixes_monomials k H.toSubgroup τ hfix
  have htranslate (ψ : Multiplicative (N ⧸ H) →* kˣ) (n : N) :
      σ (algebraMap CoordinateRing Functions (single n 1)) =
        algebraMap CoordinateRing Functions (single n (ψ (ofAdd (QuotientAddGroup.mk' H n)) : k)) ↔
      τ (algebraMap (MonoidAlgebra k (Multiplicative N)) _ (MonoidAlgebra.single (ofAdd n) 1)) =
        algebraMap (MonoidAlgebra k (Multiplicative N)) _
          (MonoidAlgebra.single (ofAdd n)
            (ψ (QuotientGroup.mk' H.toSubgroup (ofAdd n)) : k)) := by
    rw [← e.injective.eq_iff, he, ← he n 1]
    simp only [τ, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
    rfl
  exact ⟨χ, fun n ↦ (htranslate χ n).mpr (hχ (ofAdd n)),
    fun ψ hψ ↦ huniq ψ fun n ↦ (htranslate ψ n.toAdd).mp (hψ n.toAdd)⟩

end QPainleve.CharacterTorus
