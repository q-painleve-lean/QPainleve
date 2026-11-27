/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Quadric.TwoCenterPath

import QPainleve.Geometry.Toric.Fan.Picard.Quadric

/-!
# Sarkisov exit at two selected smooth quadric fiber centers

Two first centers on opposite invariant fibers give a quadric-to-quadric
Sarkisov path when their total base order exceeds the transverse degree. This
allows additional high base orders after preparing a Hirzebruch surface for
the two-center exit in [Lutz, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory Module TauCeti.Toric
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData TauCeti.SymmetricAlgebra
open Fan Fan.LogarithmicProjection
open scoped Sarkisov

namespace QPainleve.BlowupTower.IsClosedPointTower

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular)
  (hc : Φ.IsComplete) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "S" => Spec (CommRingCat.of k₀)
local notation "X[" coeff "," Δ "]" => Fan.finiteFanScheme coeff Δ
local notation "f[" Δ "]" => (X[k₀,Δ] ↘ S)
local notation "P" => Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))
local notation "fP" => (P ↘ S)
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k₀ (Fin 3 → k₀) 1)
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "B[" Δ "," h "]" => Fan.toricBoundaryIdeal k₀ Δ (Fan.IsComplete.nonempty_cones h)
local notation "fiberRay[" t "]" => r ((![1, 3] : Fin 2 → Fin 4) t)
local notation "center[" a "," ρ "," c "]" => Fan.Ray.binomialCenter ρ k₀
  (Eq.trans (finrank_eq_card_basis a) (Fintype.card_fin 2))
  (Basis.detDualEquiv_self a (Fan.Ray.primitiveGenerator ρ)) (Fan.Ray.surjective_detCharacter ρ a)
  c (IsLocalRing.closedPoint k₀)
local notation "mark[" U "," hU "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking U hU f) (Additive.ofMul (pullback g H))

variable {Y : Scheme} {n : ℕ} {T : BlowupTower X[k₀,Φ] n Y}
  (hT : IsClosedPointTower X[k₀,Φ] T) (g : Y ⟶ (Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))))

/-- Two first centers on the open orbits of opposite invariant quadric fibers
give a resolved path to a quadric of smaller fiber degree if their orders sum
to more than the transverse degree. The terminal tower carries the same
plane morphism and pole factorization. Its fiber degree equals the sum of the
original two ruling degrees minus the two selected orders. -/
theorem exists_sarkisov_path_of_quadric_two_smooth_fiber_centers
    (hg : g ≫ fP = T.toBase ≫ f[Φ]) (hbir : Scheme.BirationalOver g (𝟙 P))
    (j l : Fin n) (hjl : j ≠ l) (t : Fin 2) (c d : k₀ˣ)
    (hj : hT.baseCenter j = center[b,fiberRay[t],c])
    (hl : hT.baseCenter l = center[b,fiberRay[Equiv.swap 0 1 t],d])
    (hjfirst : ∀ k < j, hT.baseCenter k ≠ hT.baseCenter j)
    (hlfirst : ∀ k < l, hT.baseCenter k ≠ hT.baseCenter l)
    {D : Y.IdealSheafData} :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : IsIntegral Y := hT.isIntegral f[Φ]
    let x := mark[T,hT,f[Φ],g]
    let α := (Φ.hirzebruchPicardBasis k₀ b 0 hΦ r hr).repr x.1 0
    let β := (Φ.hirzebruchPicardBasis k₀ b 0 hΦ r hr).repr x.1 1
    B[Φ,hc].comap T.toBase = D * hT.ramificationIdealSheafToBase k₀ →
    α < -x.2 j + -x.2 l →
    ∃ (A Q : LogarithmicProjection k₀ i D) (_ : SarkisovPath A Q)
      (a : Basis (Fin 2) ℤ N) (s : Fin 4 ≃ Q.fan.Ray)
      (hs : (fun k ↦ (s k).primitiveGenerator) = ![a 0, a 1, -a 0, (0 : ℤ) • a 0 - a 1])
      (Z : Scheme) (m : ℕ) (U : BlowupTower X[k₀,Q.fan] m Z)
      (hU : IsClosedPointTower X[k₀,Q.fan] U) (e : Y ≅ Z),
      m = n ∧ A.fan = Φ ∧ A.hom ≍ T.toBase ∧ Q.hom = e.hom ≫ U.toBase ∧
      X[k₀,Q.fan].IsProjectiveOver k₀ ∧
      (e.inv ≫ g) ≫ fP = U.toBase ≫ f[Q.fan] ∧ Scheme.BirationalOver (e.inv ≫ g) (𝟙 P) ∧
      let : SmoothOfRelativeDimension 2 f[Q.fan] :=
        rankTwo ▸ Q.fan.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ Q.isRegular
      B[Q.fan,Q.isComplete].comap U.toBase = D.comap e.inv * hU.ramificationIdealSheafToBase k₀ ∧
      let y := mark[U,hU,f[Q.fan],e.inv ≫ g]
      let β' := (Q.fan.hirzebruchPicardBasis k₀ a 0 Q.isRegular s hs).repr y.1 1
      0 < β' ∧ β' = α + β + x.2 j + x.2 l ∧ β' < β := by
  intro hcones hdim hOver hSmooth hIntegral x α β hpole hsum
  let := hcones
  let := hdim
  let := hOver
  let := hSmooth
  let := hIntegral
  let : X[k₀,Φ].IsProjectiveOver k₀ := Φ.isProjectiveOver_quadric k₀ b hΦ hc r hr
  have hn : 2 ≤ n := by
    have hcard : 1 < Fintype.card (Fin n) := Fintype.one_lt_card_iff.mpr ⟨j, l, hjl⟩
    exact Nat.succ_le_of_lt (by simpa only [Fintype.card_fin] using hcard)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq_iff.mpr hjl.symm
  obtain ⟨a, s, hs, h₀, h₂, hpic⟩ := Φ.exists_quadric_picardBasis_of_fiber k₀ b hΦ r hr t
  obtain ⟨c', hc'⟩ := (fiberRay[t]).exists_binomialCenter_eq_of_basis k₀ a b c
  obtain ⟨d', hd'⟩ := (fiberRay[Equiv.swap 0 1 t]).exists_binomialCenter_eq_of_basis k₀ a b d
  have hj' : hT.baseCenter j = center[a,s 0,c'] := by rw [h₀, hc', hj]
  have hl' : hT.baseCenter (j.succAbove k) = center[a,s 2,d'] := by rw [h₂, hd', hl]
  have hβ : (Φ.hirzebruchPicardBasis k₀ a 0 hΦ s hs).repr x.1 0 = β := by
    rw [hpic, Basis.repr_reindex_apply]
    rfl
  have hα : (Φ.hirzebruchPicardBasis k₀ a 0 hΦ s hs).repr x.1 1 = α := by
    rw [hpic, Basis.repr_reindex_apply]
    rfl
  obtain ⟨a', hs', Z, U, hU, e, A, A₁, A₂, Q, p, hA, hAh, hQ, hQh, -, -, -, -,
    hproj, hg', hbir', hpole', hpos, hdegree, -⟩ :=
    hT.exists_sarkisov_path_of_quadric_two_smooth_centers k₀ a hΦ hc s hs g hg hbir c' d' j k
      hj' hl' (hj' ▸ hjfirst) (hl' ▸ hlfirst) D
      (hT.ramificationIdealSheafToBase_def k₀ ▸ hpole) (hα.symm ▸ hsum)
  -- The path lemma names the terminal fan explicitly. Align its tower with the projection.
  rcases Q with ⟨Ω, hΩ, hcΩ, q, hqOver, hqDom, hqPole⟩
  dsimp only at hQ hQh
  subst Ω
  rw [hβ, hα] at hdegree
  refine ⟨A, _, p, a', _, hs', Z, _, U, hU, e, by omega, hA, hAh, eq_of_heq hQh, hproj,
    hg', hbir', hpole', hpos, ?_, ?_⟩
  · exact hdegree.trans (by ring)
  · rw [hdegree]
    linarith only [hsum]

end QPainleve.BlowupTower.IsClosedPointTower
