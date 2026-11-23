/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence

/-!
# Cohomology of a sequence with acyclic quotient

Vanishing for the quotient in two consecutive degrees makes the first arrow of a
short exact sequence an isomorphism on cohomology in the higher degree.
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The first arrow of a short exact sequence induces a bijection in degree `q`
if the quotient has zero cohomology in degree `q` and, when `q > 0`, in degree `q - 1`. -/
theorem bijective_cohomologyMap_of_subsingleton_quotient {X : Scheme.{u}}
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (q : ℕ)
    (h₃ : Subsingleton (Cohomology S.X₃ q))
    (hprev : q ≠ 0 → Subsingleton (Cohomology S.X₃ (q - 1))) :
    Function.Bijective (cohomologyMap S.f q) := by
  refine ⟨?_, fun y ↦ (exact_cohomologyMap_cohomologyMap hS q y).mp (Subsingleton.elim _ _)⟩
  cases q with
  | zero =>
    have := hS.mono_f
    exact cohomologyMap_injective S.f
  | succ q =>
    have : Subsingleton (Cohomology S.X₃ q) := hprev (Nat.succ_ne_zero q)
    refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
    obtain ⟨y, rfl⟩ := (exact_cohomologyδ_cohomologyMap hS q (q + 1) rfl x).mp hx
    have hy : y = 0 := Subsingleton.elim _ _
    simp [hy]

end AlgebraicGeometry.Scheme.Modules
