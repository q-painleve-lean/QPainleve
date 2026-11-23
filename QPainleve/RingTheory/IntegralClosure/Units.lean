/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Characters with values in the base field

If a character into an extension field takes values in the base field on a finite-index
subgroup, its values are integral over the base field. When the base field is relatively
algebraically closed, the character descends uniquely.
-/

public section

namespace MonoidHom

variable {G k L : Type*} [Group G] [Field k] [Field L] [Algebra k L]

/-- A character with values in a relatively algebraically closed base field on a
finite-index subgroup has a unique factorization through the base-field units. -/
theorem existsUnique_units_lift_of_finiteIndex [IsIntegrallyClosedIn k L]
    (f : G →* Lˣ) (H : Subgroup G) (hindex : H.index ≠ 0)
    (h : ∀ g ∈ H, f g ∈ (Units.map (algebraMap k L).toMonoidHom).range) :
    ∃! χ : G →* kˣ, (Units.map (algebraMap k L).toMonoidHom).comp χ = f := by
  let ι := Units.map (algebraMap k L).toMonoidHom
  have hinj : Function.Injective ι := Units.map_injective (algebraMap k L).injective
  have hr (g : G) : f g ∈ ι.range := by
    obtain ⟨n, hn, -, hmem⟩ := H.exists_pow_mem_of_index_ne_zero hindex g
    obtain ⟨a, ha⟩ := h (g ^ n) hmem
    have he : algebraMap k L (a : k) = (f g : L) ^ n := by
      rw [map_pow] at ha
      exact congrArg (fun x : Lˣ ↦ (x : L)) ha
    obtain ⟨b, hb⟩ := IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow
      hn (he ▸ isIntegral_algebraMap (x := (a : k)))
    have hb₀ : b ≠ 0 := by
      intro hz
      exact (f g).ne_zero (by simpa [hz] using hb.symm)
    exact ⟨Units.mk0 b hb₀, Units.ext hb⟩
  let χ := (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (f.codRestrict ι.range hr)
  refine ⟨χ, MonoidHom.ext (fun g ↦ ?_), fun ψ hψ ↦ MonoidHom.ext fun g ↦ ?_⟩
  · exact MonoidHom.apply_ofInjective_symm hinj ⟨f g, hr g⟩
  · apply hinj
    exact (DFunLike.congr_fun hψ g).trans
      (MonoidHom.apply_ofInjective_symm hinj ⟨f g, hr g⟩).symm

end MonoidHom
