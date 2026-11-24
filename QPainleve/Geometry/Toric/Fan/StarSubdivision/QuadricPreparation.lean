/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Factorization

import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Transvection.Basic
import QPainleve.Geometry.Toric.Fan.CommonRefinement
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Hirzebruch

/-!
# Toric preparation of a Hirzebruch surface

A Hirzebruch fan can be reduced to the quadric by elementary transformations on
one invariant fiber. The ray of the other fiber stays fixed. A common regular
subdivision dominates the Hirzebruch fans and both projections of every link.

This is the toric preparation in Case C of Proposition 8.11 in
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open Module PointedCone

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "rays[" Δ "]" => Set.range (Ray.primitiveGenerator (Phi := Δ))

/-- A chain from the Hirzebruch fan of index `e` to the quadric, numbered by
decreasing Hirzebruch index when traversed from the source. The corner cones
specify the point blowup and blowdown of each link. Only the ray opposite the
fiber of `b 1` changes, and all link fans admit a common regular subdivision. -/
structure HirzebruchQuadricPreparation (b : Basis (Fin 2) ℤ N) (e : ℕ) (Φ : Fan i) where
  /-- The Hirzebruch fan at each index, with the quadric at index zero. -/
  model : Fin (e + 1) → Fan i
  /-- The fan of the common blowup at each elementary transformation. -/
  link : Fin e → Fan i
  /-- A single fan refining all the models and link fans. -/
  common : Fan i
  source_eq : model (Fin.last e) = Φ
  model_regular : ∀ j, (model j).IsRegular
  model_complete : ∀ j, (model j).IsComplete
  model_rays : ∀ j, rays[model j] = {b 0, b 1, -b 0, (j.val : ℤ) • b 0 - b 1}
  link_regular : ∀ j, (link j).IsRegular
  link_corners : ∀ j, ∃ (σ : (model j.succ).cones) (τ : (model j.castSucc).cones)
    (hσ : (model j.succ).IsRegular) (hτ : (model j.castSucc).IsRegular),
    Nat.card (ToricRay σ.val) = 2 ∧ Nat.card (ToricRay τ.val) = 2 ∧
    σ.val = hull ℝ {i (-b 0), i ((j.succ.val : ℤ) • b 0 - b 1)} ∧
    τ.val = hull ℝ {i ((j.val : ℤ) • b 0 - b 1), i (b 0)} ∧
    (model j.succ).starSubdivisionAlong hσ σ.property = link j ∧
    (model j.castSucc).starSubdivisionAlong hτ τ.property = link j
  common_regular : common.IsRegular
  common_model : ∀ j, common.IsSubdivision (model j)
  common_link : ∀ j, common.IsSubdivision (link j)

attribute [simp] HirzebruchQuadricPreparation.source_eq

/-- The common subdivision also refines the specified starting fan. -/
theorem HirzebruchQuadricPreparation.common_source {b : Basis (Fin 2) ℤ N} {e : ℕ} {Φ : Fan i}
    (P : HirzebruchQuadricPreparation b e Φ) : P.common.IsSubdivision Φ :=
  Eq.mp (congrArg P.common.IsSubdivision P.source_eq) (P.common_model (Fin.last e))

private theorem hirzebruch_quadric_step (b : Basis (Fin 2) ℤ N) (e : ℕ) {Φ : Fan i}
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hrays : rays[Φ] = {b 0, b 1, -b 0, ((e + 1 : ℕ) : ℤ) • b 0 - b 1}) :
    ∃ (Ψ F : Fan i) (hΨ : Ψ.IsRegular), Ψ.IsComplete ∧ F.IsRegular ∧
      rays[Ψ] = {b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1} ∧
      ∃ (σ : Φ.cones) (τ : Ψ.cones),
        Nat.card (ToricRay σ.val) = 2 ∧ Nat.card (ToricRay τ.val) = 2 ∧
        σ.val = hull ℝ {i (-b 0), i (((e + 1 : ℕ) : ℤ) • b 0 - b 1)} ∧
        τ.val = hull ℝ {i ((e : ℤ) • b 0 - b 1), i (b 0)} ∧
        Φ.starSubdivisionAlong hΦ σ.property = F ∧ Ψ.starSubdivisionAlong hΨ τ.property = F := by
  let a : ℤ := (e : ℤ) + 1
  let c := (b.map (LinearEquiv.transvection (f := (-a) • b.coord 1) (v := b 0)
    (by simp [Basis.coord_apply]))).unitsSMul (fun _ ↦ (-1 : ℤˣ))
  have hc₀ : c 0 = -b 0 := by
    simp [c, Basis.unitsSMul_apply, LinearMap.transvection.apply, Basis.coord_apply]
  have hc₁ : c 1 = a • b 0 - b 1 := by
    simp [c, Basis.unitsSMul_apply, LinearMap.transvection.apply, Basis.coord_apply, sub_eq_add_neg,
      add_comm]
  have hsection : (-a) • c 0 - c 1 = b 1 := by
    rw [hc₀, hc₁, smul_neg, neg_smul, neg_neg]
    abel
  have hrays' : rays[Φ] = {c 0, c 1, -c 0, (-a) • c 0 - c 1} := by
    rw [hsection, hc₀, hc₁, neg_neg, hrays, Nat.cast_add, Nat.cast_one]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, a]
    tauto
  obtain ⟨Ψ, hΨ, σ, τ, hσ, hτ, d, hcΨ, hσcone, hd₀, hd₁, hΨrays, hstar, _, _, hτcone⟩ :=
    Φ.exists_hirzebruch_toric_elementary_transformation c hΦ hc (-a) hrays'
  have hd₁' : d 1 = (e : ℤ) • b 0 - b 1 := by
    rw [hd₁, hc₀, hc₁]
    dsimp only [a]
    rw [add_smul, one_smul]
    abel
  have hdsection : (-a + 1) • d 0 - d 1 = b 1 := by
    rw [hd₀, hc₀, hd₁', smul_neg, ← neg_smul]
    have : -(-a + 1) = (e : ℤ) := by simp [a]
    rw [this]
    abel
  refine ⟨Ψ, Φ.starSubdivisionAlong hΦ σ.property, hΨ, hcΨ,
    Φ.isRegular_starSubdivisionAlong hΦ σ.property, ?_, σ, τ, hσ, hτ, ?_, ?_, rfl, hstar⟩
  · rw [hΨrays, hdsection, hd₀, hc₀, hd₁', neg_neg]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · simp [hσcone, Fin.range_fin_succ, Set.range_unique, Fin.tail, hc₀, hc₁, a]
  · rw [hτcone, hd₀, hc₀, hd₁', neg_neg]

/-- Starting from a complete regular Hirzebruch fan, perform exactly `e`
elementary transformations on the fiber opposite the ray `b 1` to reach the
quadric. Every intermediate model and both sides of every link are dominated
by a single regular fan. -/
theorem exists_hirzebruch_quadric_preparation (b : Basis (Fin 2) ℤ N) (e : ℕ) {Φ : Fan i}
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hrays : rays[Φ] = {b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1}) :
    Nonempty (HirzebruchQuadricPreparation b e Φ) := by
  induction e generalizing Φ with
  | zero =>
    refine ⟨⟨fun _ ↦ Φ, Fin.elim0, Φ, rfl, fun _ ↦ hΦ, fun _ ↦ hc, ?_,
      (fun j ↦ Fin.elim0 j), (fun j ↦ Fin.elim0 j), hΦ, fun _ ↦ IsSubdivision.refl Φ,
      (fun j ↦ Fin.elim0 j)⟩⟩
    intro j
    have hj : j.val = 0 := Fin.val_eq_zero j
    rw [hj]
    exact hrays
  | succ e ih =>
    obtain ⟨Ψ, F, hΨ, hcΨ, hF, hΨrays, σ, τ, hσ, hτ, hσcone, hτcone, hstar, hstar'⟩ :=
      hirzebruch_quadric_step b e hΦ hc hrays
    obtain ⟨P⟩ := ih hΨ hcΨ hΨrays
    let s : F.IsSubdivision Φ :=
      hstar ▸ (.along hΦ σ hσ : IsTwoRayStarSubdivision _ _).isSubdivision
    let t : F.IsSubdivision Ψ :=
      hstar' ▸ (.along hΨ τ hτ : IsTwoRayStarSubdivision _ _).isSubdivision
    have hN : Module.finrank ℤ N = 2 := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
    have hs : P.common.support = F.support :=
      ((P.common_model (Fin.last e)).support_eq.trans (congrArg Fan.support P.source_eq)).trans
        t.support_eq.symm
    obtain ⟨Ω, u, v, hΩ⟩ :=
      P.common.exists_regular_common_subdivision F P.common_regular hF hN hs
    refine ⟨⟨Fin.snoc P.model Φ, Fin.snoc P.link F, Ω, Fin.snoc_last ..,
      Fin.lastCases (by simpa using hΦ) (fun j ↦ by simpa using P.model_regular j),
      Fin.lastCases (by simpa using hc) (fun j ↦ by simpa using P.model_complete j),
      Fin.lastCases (by rw [Fin.snoc_last, Fin.val_last]; exact hrays)
        (fun j ↦ by rw [Fin.snoc_castSucc, Fin.val_castSucc]; exact P.model_rays j),
      Fin.lastCases (by simpa using hF) (fun j ↦ by simpa using P.link_regular j),
      ?_, hΩ, Fin.lastCases (by simpa using v.trans s)
        (fun j ↦ by simpa using u.trans (P.common_model j)),
      Fin.lastCases (by simpa using v) (fun j ↦ by simpa using u.trans (P.common_link j))⟩⟩
    refine Fin.lastCases ?_ (fun j ↦ ?_)
    · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, P.source_eq, Fin.val_last, Fin.snoc_last]
      exact ⟨σ, τ, hΦ, hΨ, hσ, hτ, hσcone, hτcone, hstar, hstar'⟩
    · rw [← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact P.link_corners j

end TauCeti.Toric.Fan
