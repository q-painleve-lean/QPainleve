/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Ample
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard

/-!
# Matched ample classes on blowup towers

Given ample classes on the bases of two blowup towers, the same positive base exponent
and the same negative total exceptional coefficients give ample classes on both final
schemes. The one-step construction is the ample twist used in the proof of Theorem 4.7
of [Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*][GHK].

[GHK]: https://paulhacking.github.io/mlp.pdf#page=18
-/

public section

open AlgebraicGeometry Filter TauCeti.AlgebraicGeometry
open LineBundleClass

universe u

namespace QPainleve.BlowupTower

variable {X Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Z]
  {H : LineBundleClass X} {G : LineBundleClass Z}

/-- Two blowup towers of equal length admit simultaneous ample twists of given ample
base classes, with a common positive power and identical strictly negative coefficients
of all total exceptional classes. -/
theorem exists_isAmple_picardHom (hH : H.IsAmple) (hG : G.IsAmple)
    {n : ℕ} {Y W : Scheme.{u}} (T : BlowupTower X n Y) (U : BlowupTower Z n W) :
    ∃ (N : ℕ) (b : Fin n → ℤ), 0 < N ∧ (∀ j, b j < 0) ∧
      (T.picardHom (Additive.ofMul (H ^ N), b)).toMul.IsAmple ∧
      (U.picardHom (Additive.ofMul (G ^ N), b)).toMul.IsAmple := by
  induction T generalizing W with
  | nil =>
    cases U
    exact ⟨1, 0, Nat.one_pos, (fun j ↦ j.elim0), by simpa using hH, by simpa using hG⟩
  | @snoc n Y T I ih =>
    cases U with
    | @snoc _ W U J =>
      obtain ⟨N, b, hN, hb, hT, hU⟩ := ih U
      have : IsNoetherian Y := T.isNoetherian
      have : IsNoetherian W := U.isNoetherian
      obtain ⟨M, hTI, hUJ, hM⟩ := ((I.eventually_isAmple_pullback_pow_mul_inv_blowupExceptionalClass
        hT).and ((J.eventually_isAmple_pullback_pow_mul_inv_blowupExceptionalClass
        hU).and (eventually_gt_atTop 0))).exists
      let c : Fin (n + 1) → ℤ := Fin.lastCases (-1) (M • b)
      have hc (j : Fin (n + 1)) : c j < 0 := by
        refine Fin.lastCases (by simp [c]) (fun i ↦ ?_) j
        have hcast : (0 : ℤ) < M := by exact_mod_cast hM
        have hneg : M • b i < 0 := by
          rw [nsmul_eq_mul]
          exact mul_neg_of_pos_of_neg hcast (hb i)
        simpa only [c, Fin.lastCases_castSucc, Pi.smul_apply] using hneg
      refine ⟨N * M, c, Nat.mul_pos hN hM, hc, ?_, ?_⟩
      all_goals
        rw [picardHom_snoc_apply_toMul]
        simp only [c, Fin.lastCases_castSucc, Fin.lastCases_last, zpow_neg_one, pow_mul]
        rw [ofMul_pow M, ← Prod.smul_mk, map_nsmul, toMul_nsmul, pullback_pow]
      · exact hTI
      · exact hUJ

end QPainleve.BlowupTower
