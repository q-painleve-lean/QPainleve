/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import QPainleve.Geometry.Toric.CharacterTorus.Injective

/-!
# Period characters avoiding root translates

An injective period character avoids the value one on every class of square `-2`.
Adding multiples of the total boundary class leaves the square unchanged on the
boundary orthogonal lattice. A primitive total boundary class can be assigned the value
`1/2` by the same injective character.
-/

public section

namespace QPainleve

open LinearMap

variable {K : Type*} [AddCommGroup K] [Module ℤ K]

/-- An injective character avoids one on every translate of a root by a multiple of a
radical vector. The character may be a transported period, since composing an injective
character with a lattice equivalence or taking its inverse preserves injectivity. -/
theorem period_ne_one_on_root_translate {G : Type*} [Monoid G] {a : Multiplicative K →* G}
    (ha : Function.Injective a) (B : LinearMap.BilinForm ℤ K) (hB : B.IsSymm)
    {δ x : K} (hδ : δ ∈ B.orthogonal ⊤) (hx : B x x = -2) (n : ℤ) :
    a (Multiplicative.ofAdd (x + n • δ)) ≠ 1 := by
  obtain rfl : ‹Module ℤ K› = AddCommGroup.toIntModule K := Subsingleton.elim _ _
  have hn : n • δ ∈ B.orthogonal ⊤ := (B.orthogonal ⊤).smul_mem n hδ
  have hright (y : K) : B y (n • δ) = 0 :=
    BilinForm.mem_orthogonal_iff.mp hn y Submodule.mem_top
  have hleft (y : K) : B (n • δ) y = 0 := (hB.eq _ _).trans (hright y)
  have hsq : B (x + n • δ) (x + n • δ) = -2 := by
    simp only [B.add_left, B.add_right, hright, hleft, add_zero, hx]
  intro h
  have hzero : x + n • δ = 0 :=
    Multiplicative.ofAdd.injective (ha (h.trans a.map_one.symm))
  simp [hzero] at hsq

/-- Transporting an injective period by a lattice equivalence and either orientation
still avoids one on every radical translate of a root. -/
theorem period_zpow_ne_one_on_root_translate {G : Type*} [Group G]
    {a : Multiplicative K →* G} (ha : Function.Injective a) (B : LinearMap.BilinForm ℤ K)
    (hB : B.IsSymm) {δ x : K} (hδ : δ ∈ B.orthogonal ⊤) (hx : B x x = -2)
    (n : ℤ) (g : K ≃ₗ[ℤ] K) (η : ℤˣ) :
    a (Multiplicative.ofAdd (g (x + n • δ))) ^ (η : ℤ) ≠ 1 := by
  let e := g.toAddEquiv.toMultiplicative
  have h : a (Multiplicative.ofAdd (g (x + n • δ))) ≠ 1 :=
    period_ne_one_on_root_translate (a := a.comp e.toMonoidHom)
      (ha.comp e.injective) B hB hδ hx n
  rcases Int.units_eq_one_or η with rfl | rfl
  · simpa only [Units.val_one, zpow_one] using h
  · simpa only [Units.val_neg, Units.val_one, zpow_neg, zpow_one, inv_ne_one] using h

/-- A finite free lattice with a primitive radical vector admits an injective period character
over any characteristic-zero field. It takes the value `1/2` on that vector and avoids one on all
translated roots. -/
theorem exists_root_avoiding_period {k : Type*} [Field k] [CharZero k]
    [Module.Free ℤ K] [Module.Finite ℤ K]
    (B : LinearMap.BilinForm ℤ K) (hB : B.IsSymm) {δ : K} (hδ : δ ∈ B.orthogonal ⊤)
    (f : K →ₗ[ℤ] ℤ) (hf : f δ = 1) :
    ∃ a : Multiplicative K →* kˣ, Function.Injective a ∧
      (a (Multiplicative.ofAdd δ) : k) = (2 : k)⁻¹ ∧
      ∀ x : K, B x x = -2 → ∀ n : ℤ, a (Multiplicative.ofAdd (x + n • δ)) ≠ 1 := by
  obtain ⟨a, -, -, -, ha, -, hval, -⟩ :=
    CharacterTorus.exists_injective_character_of_primitive (k := k) f hf
  exact ⟨a, ha, hval, fun _ hx n ↦ period_ne_one_on_root_translate ha B hB hδ hx n⟩

end QPainleve
