/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch

import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Marking the retained fiber of a Hirzebruch fan

A Hirzebruch fan can be marked with either invariant fiber in position one,
keeping the same signed Hirzebruch parameter and Picard basis. This lets the
toric preparation to the quadric take place away from a prescribed center,
as in Case C of Proposition 8.11 of [Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open Module

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (e : ℤ) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

include hr in
private theorem exists_hirzebruch_marking_swap_fibers :
    ∃ (d : Basis (Fin 2) ℤ N),
      (fun j ↦ (r (Equiv.swap 1 3 j)).primitiveGenerator) =
        ![d 0, d 1, -d 0, e • d 0 - d 1] := by
  let d := (b.map (LinearEquiv.transvection (f := (-e) • b.coord 1) (v := b 0)
    (by simp [Basis.coord_apply]))).unitsSMul (fun j ↦ if j = 1 then (-1 : ℤˣ) else 1)
  have h₀ : d 0 = b 0 := by
    simp [d, Basis.unitsSMul_apply, LinearMap.transvection.apply, Basis.coord_apply]
  have h₁ : d 1 = e • b 0 - b 1 := by
    simp [d, Basis.unitsSMul_apply, LinearMap.transvection.apply, Basis.coord_apply,
      sub_eq_add_neg, add_comm]
  refine ⟨d, funext fun j ↦ ?_⟩
  fin_cases j <;> simp [Equiv.swap_apply_def, h₀, h₁, congrFun hr]

include hr in
/-- Either invariant fiber can be placed first among the fiber rays in a
Hirzebruch marking. The section at index zero and the entire Picard basis are
unchanged, so every fiber degree and section coefficient is preserved. -/
theorem exists_hirzebruch_picardBasis_of_fiber [Nonempty Φ.cones] (hΦ : Φ.IsRegular)
    (t : Fin 2) :
    ∃ (d : Basis (Fin 2) ℤ N) (s : Fin 4 ≃ Φ.Ray)
      (hs : (fun j ↦ (s j).primitiveGenerator) = ![d 0, d 1, -d 0, e • d 0 - d 1]),
      s 0 = r 0 ∧ s 1 = r ((![1, 3] : Fin 2 → Fin 4) t) ∧
      hirzebruchPicardBasis d e hΦ s hs = hirzebruchPicardBasis b e hΦ r hr := by
  classical
  fin_cases t
  · exact ⟨b, r, hr, rfl, rfl, rfl⟩
  obtain ⟨d, hd⟩ := exists_hirzebruch_marking_swap_fibers b e r hr
  let s := (Equiv.swap 1 3).trans r
  have hs : (fun j ↦ (s j).primitiveGenerator) = ![d 0, d 1, -d 0, e • d 0 - d 1] := hd
  have h₀ : s 0 = r 0 := by simp [s, Equiv.swap_apply_def]
  have h₁ : s 1 = r 3 := by simp [s]
  refine ⟨d, s, hs, h₀, h₁, DFunLike.ext _ _ (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩
  · simp only [hirzebruchPicardBasis_apply_zero d, h₁,
      hirzebruchPicardBasis_apply_zero_eq_ray_three b]
  · simp only [hirzebruchPicardBasis_apply_one, h₀]

end TauCeti.Toric.Fan
