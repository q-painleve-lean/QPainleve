/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import QPainleve.RingTheory.LocalRing.Cotangent
import QPainleve.RingTheory.MvPowerSeries.KrullDimension
import QPainleve.RingTheory.MvPowerSeries.Truncation
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import TauCeti.Algebra.Module.SpanRank
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.KrullDimension.Fiber
import TauCeti.RingTheory.MvPowerSeries.Evaluation

/-!
# Adic completions with the Hilbert function of a power series ring

The dimensions of the maximal-ideal quotients determine when the completion of a
Noetherian local algebra over a field is a formal power series ring. Lifts of a
basis of the cotangent space give the variables of the power series ring.
The evaluation map comes from `MvPowerSeries.exists_surjective_ringHom_of_isAdicComplete`.
-/

public section

open IsLocalRing

namespace AdicCompletion

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R] [IsLocalRing R] [IsNoetherianRing R]

local notation "𝔪" => maximalIdeal R
local notation "R̂" => AdicCompletion 𝔪 R

private theorem injective_of_quotient_finrank_eq {d : ℕ}
    (φ : MvPowerSeries (Fin d) k →ₐ[k] R̂) (hφ : Function.Surjective φ)
    (hmap : (Ideal.span (Set.range MvPowerSeries.X)).map φ.toRingHom = maximalIdeal R̂)
    (hdim : ∀ n : ℕ, Module.finrank k (R ⧸ 𝔪 ^ (n + 1)) = (n + d).choose d) :
    Function.Injective φ := by
  let A := MvPowerSeries (Fin d) k
  let m : Ideal A := Ideal.span (Set.range MvPowerSeries.X)
  have hmem {a : A} (ha : φ a = 0) (n : ℕ) : a ∈ m ^ (n + 1) := by
    let J := (𝔪 ^ (n + 1)).map (algebraMap R R̂)
    have hm : (m ^ (n + 1)).map φ.toRingHom = J := by
      rw [Ideal.map_pow, hmap, maximalIdeal_eq_map]
      exact (Ideal.map_pow _ _ _).symm
    have hle : m ^ (n + 1) ≤ J.comap φ.toRingHom := Ideal.map_le_iff_le_comap.mp hm.le
    let q := Ideal.quotientMapₐ (R₁ := k) J φ hle
    have hq : Function.Surjective q := Ideal.quotientMap_surjective (H := hle) hφ
    let e := (quotientMapPowAlgEquiv (Ideal.fg_of_isNoetherianRing 𝔪) (n + 1)).restrictScalars k
    have hr : Module.finrank k (A ⧸ m ^ (n + 1)) = (n + d).choose d := by
      simpa only [Fintype.card_fin] using
        MvPowerSeries.finrank_quotient_span_range_X_pow (Fin d) k n
    have : Module.Finite k (A ⧸ m ^ (n + 1)) :=
      Module.finite_of_finrank_pos (hr.symm ▸ Nat.choose_pos (Nat.le_add_left d n))
    have heq : Module.finrank k (A ⧸ m ^ (n + 1)) = Module.finrank k (R̂ ⧸ J) :=
      hr.trans ((hdim n).symm.trans e.toLinearEquiv.finrank_eq.symm)
    have : Module.Finite k (R̂ ⧸ J) := Module.Finite.of_surjective q.toLinearMap hq
    -- The two finite-dimensional truncations have equal dimension.
    have hi : Function.Injective q :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := q.toLinearMap) heq).mpr hq
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((map_eq_zero_iff q hi).mp (by
        exact (Ideal.quotient_map_mkₐ J φ hle).trans
          (ha ▸ _root_.map_zero (Ideal.Quotient.mkₐ k J))))
  -- A series vanishing in every positive truncation is zero.
  refine (injective_iff_map_eq_zero φ).mpr fun a ha ↦ ?_
  apply IsHausdorff.haus' (I := m) (M := A) a
  intro n
  cases n with
  | zero => simp
  | succ n => exact SModEq.zero.mpr (by simpa using hmem ha n)

private theorem exists_powerSeries_parameters (d : ℕ)
    (hres : Module.finrank k (ResidueField R) = 1)
    (h₂ : Module.finrank k (R ⧸ 𝔪 ^ 2) = d + 1) :
    ∃ x : Fin d → R, Ideal.span (Set.range x) = 𝔪 := by
  have : Module.Finite k (R ⧸ 𝔪 ^ 2) := Module.finite_of_finrank_pos (by rw [h₂]; omega)
  have hc := finrank_quotient_maximalIdeal_sq k R
  have hcot : Module.finrank k (CotangentSpace R) = d := by omega
  have hm := spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_residue_surjective k R
    (Ideal.fg_of_isNoetherianRing 𝔪)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hres).surjective
  have hfg : (𝔪 : Submodule R R).FG := IsNoetherian.noetherian _
  exact (Submodule.FG.spanFinrank_le_iff_exists_fin_generating_family hfg d).mp (hm.trans hcot).le

/-- If all the maximal-ideal quotients of a Noetherian local `k`-algebra have the
dimensions of the corresponding quotients of `k⟦X₁, …, X_d⟧`, its completion is
isomorphic to that power series ring as a `k`-algebra. The variables map to the images
of a family of generators of the maximal ideal of the original local ring. -/
theorem exists_algEquiv_mvPowerSeries_of_finrank_quotient_pow (d : ℕ)
    (hdim : ∀ n : ℕ, Module.finrank k (R ⧸ 𝔪 ^ (n + 1)) = (n + d).choose d) :
    ∃ (e : MvPowerSeries (Fin d) k ≃ₐ[k] R̂) (x : Fin d → R),
      Ideal.span (Set.range x) = 𝔪 ∧ ∀ i, e (MvPowerSeries.X i) = algebraMap R R̂ (x i) := by
  have h₁ : Module.finrank k (R ⧸ 𝔪 ^ 1) = 1 := by
    simpa only [Nat.zero_add, Nat.choose_self] using hdim 0
  have hres : Module.finrank k (ResidueField R) = 1 :=
    (Ideal.quotientEquivAlgOfEq k (pow_one 𝔪)).toLinearEquiv.finrank_eq.symm.trans h₁
  have h₂ : Module.finrank k (R ⧸ 𝔪 ^ 2) = d + 1 := by
    simpa [Nat.add_comm] using hdim 1
  obtain ⟨x, hx⟩ := exists_powerSeries_parameters d hres h₂
  let y : Fin d → R̂ := algebraMap R R̂ ∘ x
  have hy : Ideal.span (Set.range y) = maximalIdeal R̂ := by
    calc
      Ideal.span (Set.range y) = (Ideal.span (Set.range x)).map (algebraMap R R̂) := by
        rw [Ideal.map_span, ← Set.range_comp]
      _ = maximalIdeal R̂ :=
        (congrArg (Ideal.map (algebraMap R R̂)) hx).trans maximalIdeal_eq_map.symm
  let e := (quotientMapPowAlgEquiv (Ideal.fg_of_isNoetherianRing 𝔪) 1).restrictScalars k
  have he : (maximalIdeal R̂) = (𝔪 ^ 1).map (algebraMap R R̂) := by
    rw [pow_one, maximalIdeal_eq_map]
  let e' := (Ideal.quotientEquivAlgOfEq k he).trans e
  have hres' : Module.finrank k (ResidueField R̂) = 1 := e'.toLinearEquiv.finrank_eq.trans h₁
  obtain ⟨φ, hφ, hC, hX⟩ := MvPowerSeries.exists_surjective_ringHom_of_isAdicComplete
    (algebraMap k R̂) (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hres').surjective y hy
  let ψ : MvPowerSeries (Fin d) k →ₐ[k] R̂ :=
    ⟨φ, fun c ↦ RingHom.congr_fun hC c⟩
  have hmap : (Ideal.span (Set.range MvPowerSeries.X)).map φ = maximalIdeal R̂ := by
    rw [Ideal.map_span, ← Set.range_comp]
    simpa only [Function.comp_def, hX] using hy
  exact ⟨AlgEquiv.ofBijective ψ ⟨injective_of_quotient_finrank_eq ψ hφ hmap hdim, hφ⟩, x, hx, hX⟩

/-- A Noetherian local algebra whose maximal-ideal quotients have the dimensions of a
formal power series ring in `d` variables is regular of dimension `d`. -/
theorem isRegularLocalRing_and_ringKrullDim_eq_of_finrank_quotient_pow (d : ℕ)
    (hdim : ∀ n : ℕ, Module.finrank k (R ⧸ 𝔪 ^ (n + 1)) = (n + d).choose d) :
    IsRegularLocalRing R ∧ ringKrullDim R = d := by
  obtain ⟨e, x, hx, -⟩ := exists_algEquiv_mvPowerSeries_of_finrank_quotient_pow d hdim
  have hdimR : ringKrullDim R̂ = ringKrullDim R :=
    TauCeti.ringKrullDim_eq_of_hasGoingDown_of_map_maximalIdeal_eq maximalIdeal_eq_map.symm
  have hlo : (d : WithBot ℕ∞) ≤ ringKrullDim R :=
    (MvPowerSeries.le_ringKrullDim_fin k d).trans_eq (e.toRingEquiv.ringKrullDim.trans hdimR)
  have hgen : (maximalIdeal R).spanFinrank ≤ d :=
    ((IsNoetherian.noetherian (𝔪 : Submodule R R)).spanFinrank_le_iff_exists_fin_generating_family
      d).mpr ⟨x, hx⟩
  have hle : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ ringKrullDim R :=
    (Nat.cast_le.mpr hgen).trans hlo
  have hreg := IsRegularLocalRing.of_spanFinrank_maximalIdeal_le R hle
  exact ⟨hreg, le_antisymm ((ringKrullDim_le_spanFinrank_maximalIdeal R).trans
    (Nat.cast_le.mpr hgen)) hlo⟩

end AdicCompletion
