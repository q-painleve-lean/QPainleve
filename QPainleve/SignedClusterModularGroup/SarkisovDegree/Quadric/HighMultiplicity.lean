/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Quadric.PlanePath
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Quadric.TwoCenterPath

import QPainleve.Geometry.Toric.Fan.Picard.Quadric

/-!
# Sarkisov decrease at smooth points of the quadric fibers

When the high base orders are over the interiors of distinct invariant fibers,
the one-center and two-center links apply in the exchanged ruling. In both cases
the path starts at the specified projection, and its terminal point tower resolves
the same map to the plane with strictly smaller bidegree.

The link blocks are the smooth-center cases of Proposition 8.11 in
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public section

open AlgebraicGeometry CategoryTheory Module TauCeti.Toric
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData TauCeti.SymmetricAlgebra
open Fan Fan.LogarithmicProjection
open scoped Sarkisov

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular)
  (hc : Φ.IsComplete) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "f[" Δ "]" => (X[Δ] ↘ S)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "fP" => (P ↘ S)
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "degree" => Basis.picardTwistEquiv (Pi.basisFun ℂ (Fin 3))
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "B[" Δ "," h "]" => Fan.boundaryIdeal Δ (Fan.IsComplete.nonempty_cones h)
local notation "Π[" d "]" => Fan.projectiveSpace d (Fan.lattice Φ)
local notation "hcΠ[" d "]" => Fan.isComplete_projectiveSpace d (Fan.lattice Φ)
local notation "planeIso[" d "]" =>
  Fan.projectivePlaneIso d (Fan.lattice Φ) ≪≫ Basis.polynomialProjIso (Pi.basisFun ℂ (Fin 3))
local notation "fiberRay[" t "]" => r ((![1, 3] : Fin 2 → Fin 4) t)
local notation "center[" a "," ρ "," c "]" => Fan.Ray.binomialCenter ρ
  (Eq.trans (finrank_eq_card_basis a) (Fintype.card_fin 2))
  (Basis.detDualEquiv_self a (Fan.Ray.primitiveGenerator ρ)) (Fan.Ray.surjective_detCharacter ρ a)
  c (IsLocalRing.closedPoint ℂ)
local notation "mark[" U "," hU "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking U hU f) (Additive.ofMul (pullback g H))

variable {Y : Scheme} {n : ℕ} {T : BlowupTower X[Φ] n Y}
  (hT : IsClosedPointTower X[Φ] T) (g : Y ⟶ P)

/-- Suppose the high base orders of a logarithmic quadric-to-plane resolution
are first centers over the interiors of distinct invariant fibers and there is
at least one such center. There is a resolved Sarkisov path from the specified
projection to a plane or quadric resolution of strictly smaller Sarkisov degree.
The endpoint is identified with its ordered point tower, with the same map to
the target plane and the transported pole factorization. -/
theorem exists_sarkisov_path_decrease_of_quadric_high_fiber_centers
    (hg : g ≫ fP = T.toBase ≫ f[Φ]) (hbir : Scheme.BirationalOver g (𝟙 P))
    {D : Y.IdealSheafData} :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : IsIntegral Y := hT.isIntegral f[Φ]
    let x := mark[T,hT,f[Φ],g]
    let β := (Φ.hirzebruchPicardBasis b 0 hΦ r hr).repr x.1 1
    let m := fun j ↦ -x.2 j
    let high := Finset.univ.filter (fun j ↦ β < 2 * m j)
    B[Φ,hc].comap T.toBase = D * hT.ramificationIdealSheafToBase ℂ →
    high.Nonempty →
    (∃ fiber : (↑high : Type) ↪ Fin 2, ∀ j : high,
      (∀ k < j.val, hT.baseCenter k ≠ hT.baseCenter j) ∧
      ∃ c : ℂˣ, hT.baseCenter j = center[b,fiberRay[fiber j],c]) →
    ∃ (A B : LogarithmicProjection i D) (_ : SarkisovPath A B),
      A.fan = Φ ∧ A.hom ≍ T.toBase ∧
      ((∃ (d : Basis (Fin 2) ℤ N) (Z : Scheme) (l : ℕ) (U : BlowupTower P l Z)
        (hU : IsClosedPointTower P U) (e : Y ≅ Z),
        B.fan = Π[d] ∧ B.hom ≍ e.hom ≫ U.toBase ≫ (planeIso[d]).inv ∧
        (e.inv ≫ g) ≫ fP = U.toBase ≫ fP ∧ Scheme.BirationalOver (e.inv ≫ g) (𝟙 P) ∧
        (B[Π[d],hcΠ[d]].comap (planeIso[d]).inv).comap U.toBase =
          D.comap e.inv * hU.ramificationIdealSheafToBase ℂ ∧
        let y := mark[U,hU,fP,e.inv ≫ g]
        0 < degree y.1 ∧ ∀ M' M, planeSarkisovBidegree (degree y.1).toNat M' <
          hirzebruchSarkisovBidegree β.toNat M) ∨
      (∃ (Ω : Fan i) (hΩ : Ω.IsRegular) (hcΩ : Ω.IsComplete) (d : Basis (Fin 2) ℤ N)
        (s : Fin 4 ≃ Ω.Ray)
        (hs : (fun j ↦ (s j).primitiveGenerator) = ![d 0, d 1, -d 0, (0 : ℤ) • d 0 - d 1])
        (Z : Scheme) (l : ℕ) (U : BlowupTower X[Ω] l Z)
        (hU : IsClosedPointTower X[Ω] U) (e : Y ≅ Z),
        B.fan = Ω ∧ B.hom ≍ e.hom ≫ U.toBase ∧ X[Ω].IsProjectiveOver ℂ ∧
        (e.inv ≫ g) ≫ fP = U.toBase ≫ f[Ω] ∧ Scheme.BirationalOver (e.inv ≫ g) (𝟙 P) ∧
        let : Nonempty Ω.cones := hcΩ.nonempty_cones
        let : SmoothOfRelativeDimension 2 f[Ω] :=
          rankTwo ▸ Ω.smoothOfRelativeDimension_algebraicRealizationStructureMap hΩ
        B[Ω,hcΩ].comap U.toBase = D.comap e.inv * hU.ramificationIdealSheafToBase ℂ ∧
        let y := mark[U,hU,f[Ω],e.inv ≫ g]
        let β' := (Ω.hirzebruchPicardBasis d 0 hΩ s hs).repr y.1 1
        0 < β' ∧ ∀ M' M, hirzebruchSarkisovBidegree β'.toNat M' <
          hirzebruchSarkisovBidegree β.toNat M)) := by
  classical
  intro hcones hdim hY hSmooth hIntegral x β m high hpole hhigh
  rintro ⟨fiber, hfiber⟩
  let : X[Φ].IsProjectiveOver ℂ := Φ.isProjectiveOver_quadric b hΦ hc r hr
  obtain ⟨j, hj⟩ := hhigh
  let j₀ : high := ⟨j, hj⟩
  -- The exchanged frame places the first pivot on section zero and keeps the
  -- old degree threshold as the coefficient read by the quadric link lemmas.
  obtain ⟨d, s, hs, h₀, h₂, hpic⟩ :=
    Φ.exists_quadric_picardBasis_of_fiber b hΦ r hr (fiber j₀)
  have hβ : (Φ.hirzebruchPicardBasis d 0 hΦ s hs).repr x.1 0 = β := by
    rw [hpic, Basis.repr_reindex_apply]
    rfl
  have hcenter (k : high) {ρ : Φ.Ray} (hρ : ρ = fiberRay[fiber k]) :
      ∃ a : ℂˣ, hT.baseCenter k = center[d,ρ,a] := by
    obtain ⟨c, hc⟩ := (hfiber k).2
    obtain ⟨a, ha⟩ := ρ.exists_binomialCenter_eq_of_basis d b c
    exact ⟨a, by rw [ha, hρ, hc]⟩
  obtain ⟨a, hjc⟩ := hcenter j₀ h₀
  have hlarge (k : high) : β < 2 * m k := (Finset.mem_filter.mp k.property).2
  have hsmall (k : Fin n) (hk : k ∉ high) : 2 * m k ≤ β := by
    simpa only [high, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hk
  by_cases hex : ∃ l : high, l.val ≠ j
  · obtain ⟨l, hne⟩ := hex
    -- Any second high order lies on the opposite fiber. The embedding excludes
    -- a third high order.
    have opposite : ∀ a b : Fin 2, a ≠ b → a = Equiv.swap 0 1 b := by decide
    have hfl (k : high) (hk : k.val ≠ j) : fiber k = Equiv.swap 0 1 (fiber j₀) :=
      opposite _ _ (fun he ↦ hk (congrArg Subtype.val (fiber.injective he)))
    obtain ⟨a', hlc⟩ := hcenter l ((hfl l hne).symm ▸ h₂)
    have hnothigh (k : Fin n) (hkj : k ≠ j) (hkl : k ≠ l) : k ∉ high := by
      intro hk
      exact hkl (congrArg Subtype.val (fiber.injective ((hfl ⟨k, hk⟩ hkj).trans (hfl l hne).symm)))
    have hn : 2 ≤ n := by
      have hcard := Finset.one_lt_card.mpr ⟨j, hj, l.val, l.property, Ne.symm hne⟩
      exact hcard.trans_le (by simpa only [Fintype.card_fin] using Finset.card_le_univ high)
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq_iff.mpr hne
    obtain ⟨e, hs', Z, U, hU, f, A, A₁, A₂, B, p, hA, hAh, hB, hBh, -, -, -, -,
      hProj, hg', hbir', hpole', hpos, hlt⟩ :=
      hT.exists_sarkisov_path_decrease_of_quadric_two_smooth_centers d hΦ hc s hs g hg hbir
        a a' j k hjc (hk.symm ▸ hlc) (hjc ▸ (hfiber j₀).1) (hk.symm ▸ (hlc ▸ (hfiber l).1)) D
        ((hT.ramificationIdealSheafToBase_def ℂ) ▸ hpole)
        (hβ.symm ▸ hlarge j₀) (hβ.symm ▸ (hk.symm ▸ hlarge l))
        (fun u hu hu' ↦ hβ.symm ▸ hsmall u (hnothigh u hu (hk ▸ hu')))
    refine ⟨A, B, p, hA, hAh, Or.inr ⟨_, hB ▸ B.isRegular, hB ▸ B.isComplete, e, _, hs',
      Z, _, U, hU, f, hB, hBh, hProj, hg', hbir', hpole', hpos, ?_⟩⟩
    rwa [← hβ]
  · have hnothigh (k : Fin n) (hkj : k ≠ j) : k ∉ high := fun hk ↦ hex ⟨⟨k, hk⟩, hkj⟩
    have hn : 1 ≤ n := by have := j.isLt; omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
    obtain ⟨e, -, A, B, p, Z, U, hU, f, hA, hAh, hB, hBh, -, -, hg', hbir', hpole',
      -, -, -, -, hpos, hlt⟩ :=
      hT.exists_sarkisov_path_decrease_of_quadric_single_high_center d hΦ hc s hs g hg hbir
        a j hjc (hjc ▸ (hfiber j₀).1) D hpole (hβ.symm ▸ hlarge j₀)
        (fun u hu ↦ hβ.symm ▸ hsmall u (hnothigh u hu))
    refine ⟨A, B, p, hA, hAh, Or.inl ⟨e, Z, _, U, hU, f, hB, hBh, hg', hbir', hpole', hpos, ?_⟩⟩
    rwa [← hβ]

end QPainleve.BlowupTower.IsClosedPointTower
