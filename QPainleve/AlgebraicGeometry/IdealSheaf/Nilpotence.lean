/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Noetherian

import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# Nilpotent ideal sheaves on Noetherian schemes

The local nilpotence bounds on a finite affine cover give a single exponent for
an ideal sheaf supported on the entire scheme.
-/

public section

open TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}}

/-- Each member of a list of ideal sheaves vanishes only where the product also vanishes. -/
theorem support_le_support_list_prod_of_mem {l : List X.IdealSheafData} {J : X.IdealSheafData}
    (hJ : J ∈ l) : J.support ≤ l.prod.support := by
  induction l with
  | nil => simp at hJ
  | cons K l ih =>
    rw [List.prod_cons, support_mul]
    rcases List.mem_cons.mp hJ with rfl | h
    · exact le_sup_left
    · exact (ih h).trans le_sup_right

variable [IsNoetherian X]

/-- An ideal sheaf whose vanishing set is the whole Noetherian scheme is nilpotent. -/
theorem isNilpotent_of_support_eq_top (I : X.IdealSheafData) (hI : I.support = ⊤) :
    IsNilpotent I := by
  classical
  have hle : I ≤ X.nilradical := by
    rw [← vanishingIdeal_top, ← hI]
    exact I.le_radical.trans_eq vanishingIdeal_support.symm
  have htop : IsCompactElement (⊤ : X.Opens) :=
    (Opens.isCompactElement_iff _).mpr (by simpa using isCompact_univ)
  obtain ⟨s, hs⟩ := htop.exists_finset_of_le_iSup (fun U : X.affineOpens ↦ U.val)
    (by rw [iSup_affineOpens_eq_top X])
  have hs' : (⨆ U : s, (U.val : X.affineOpens).val) = ⊤ := by
    rw [iSup_subtype]
    exact top_unique hs
  have hnil (U : s) : ∃ n : ℕ, (I.ideal U.val) ^ n = ⊥ := by
    have := IsLocallyNoetherian.component_noetherian (X := X) U.val
    obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical Γ(X, U.val)
    have hpow : I.ideal U.val ^ n ≤ (_root_.nilradical Γ(X, U.val)) ^ n :=
      pow_le_pow_left' (le_def.mp hle U.val) n
    rw [hn] at hpow
    exact ⟨n, le_bot_iff.mp hpow⟩
  choose n hn using hnil
  let N := Finset.univ.sup n
  refine ⟨N, ?_⟩
  apply ext_of_iSup_eq_top (fun U : s ↦ U.val) hs'
  intro U
  rw [show (0 : X.IdealSheafData) = ⊥ from rfl, ideal_bot, ideal_pow, Pi.pow_apply]
  have hbound : n U ≤ N := Finset.le_sup (Finset.mem_univ U)
  have hone : I.ideal U.val ≤ 1 := by rw [Ideal.one_eq_top]; exact le_top
  exact le_bot_iff.mp ((pow_le_pow_right_of_le_one' hone hbound).trans_eq (hn U))

end AlgebraicGeometry.Scheme.IdealSheafData
