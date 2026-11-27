/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Quadric.HighMultiplicity

import QPainleve.SignedClusterModularGroup.SarkisovDegree.NoHighMultiplicity.Path
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Path.Corner
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Pivots
import QPainleve.SignedClusterModularGroup.SarkisovDegree.ResolvedSection

/-!
# Resolved Sarkisov decreases from a quadric

Every logarithmic resolution of a birational map from a quadric to the plane
admits a decreasing block on the given resolving surface. A high order above
a corner or a section gives an elementary transformation. Otherwise the high orders
lie in the interiors of distinct invariant fibers and the one- and two-center
blocks apply. If there are no high orders, exchanging rulings decreases the
degree. The target retains a marked tower resolving the specified plane map.

These are the quadric cases of [Lutz, Proposition 8.11][HKL], with the
no-high-order case from Lemma 8.8.

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public section

open AlgebraicGeometry CategoryTheory Module TauCeti.Toric
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData TauCeti.SymmetricAlgebra
open Fan Fan.LogarithmicProjection
open scoped Sarkisov

namespace QPainleve.BlowupTower.IsClosedPointTower

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "S" => Spec (CommRingCat.of k₀)
local notation "X[" coeff "," Δ "]" => Fan.finiteFanScheme coeff Δ
local notation "f[" Δ "]" => (X[k₀,Δ] ↘ S)
local notation "P" => Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))
local notation "fP" => (P ↘ S)
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k₀ (Fin 3 → k₀) 1)
local notation "degree" => Basis.picardTwistEquiv (Pi.basisFun k₀ (Fin 3))
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "B[" Δ "," h "]" => Fan.toricBoundaryIdeal k₀ Δ (Fan.IsComplete.nonempty_cones h)
local notation "Π[" d "]" => Fan.projectiveSpace d (Fan.lattice Φ)
local notation "hcΠ[" d "]" => Fan.isComplete_projectiveSpace d (Fan.lattice Φ)
local notation "planeIso[" d "]" =>
  Fan.projectivePlaneIso k₀ d (Fan.lattice Φ) ≪≫ Basis.polynomialProjIso (Pi.basisFun k₀ (Fin 3))
local notation "mark[" U "," hU "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking U hU f) (Additive.ofMul (pullback g H))

variable {Y : Scheme} {n : ℕ} {T : BlowupTower X[k₀,Φ] n Y}
  (hT : IsClosedPointTower X[k₀,Φ] T) (g : Y ⟶ (Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))))
  (hg : g ≫ (Proj (homogeneousSubmodule k₀ (Fin 3 → k₀)) ↘ Spec (.of k₀)) =
    T.toBase ≫ (X[k₀,Φ] ↘ Spec (.of k₀))) (hbir : Scheme.BirationalOver g (𝟙 (Proj
    (homogeneousSubmodule k₀ (Fin 3 → k₀)))))
  {D : Y.IdealSheafData}

-- The Hirzebruch conclusion is shared by the corner, section, and fiber cases.
local macro "hirzebruchTarget[" Q:term "," Y:term "," g:term "," D:term "," old:term "]" :
    term =>
  `(let Δ := ($Q).fan
    let hΔ := ($Q).isRegular
    let hcΔ := ($Q).isComplete
    ∃ (e : ℕ) (d : Basis (Fin 2) ℤ _) (s : Fin 4 ≃ Δ.Ray)
      (hs : (fun j ↦ (s j).primitiveGenerator) = ![d 0, d 1, -d 0, (e : ℤ) • d 0 - d 1])
      (Z : Scheme) (l : ℕ) (U : BlowupTower X[k₀,Δ] l Z)
      (hU : IsClosedPointTower X[k₀,Δ] U) (k : $Y ≅ Z),
      ($Q).hom = k.hom ≫ U.toBase ∧ X[k₀,Δ].IsProjectiveOver k₀ ∧
      (k.inv ≫ $g) ≫ fP = U.toBase ≫ f[Δ] ∧ Scheme.BirationalOver (k.inv ≫ $g) (𝟙 P) ∧
      let : SmoothOfRelativeDimension 2 f[Δ] := by
        rw [Fan.finiteFanScheme_over k₀]
        exact ((finrank_eq_card_basis d).trans (Fintype.card_fin 2)) ▸
          Δ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΔ
      B[Δ,hcΔ].comap U.toBase = ($D).comap k.inv * hU.ramificationIdealSheafToBase k₀ ∧
      let y := mark[U,hU,f[Δ],k.inv ≫ $g]
      let β' := (Δ.hirzebruchPicardBasis k₀ d e hΔ s hs).repr y.1 1
      0 < β' ∧ hirzebruchSarkisovBidegree β'.toNat (∑ j, -y.2 j).toNat < $old)

section

variable [Nonempty Φ.cones] [SmoothOfRelativeDimension 2 (X[k₀,Φ] ↘ Spec (.of k₀))]

local notation "β" =>
  Basis.repr (Fan.hirzebruchPicardBasis k₀ b 0 hΦ r hr) (Prod.fst (mark[T,hT,f[Φ],g])) 1
local notation "old" =>
  hirzebruchSarkisovBidegree (Int.toNat β) (Int.toNat (∑ j, -(Prod.snd (mark[T,hT,f[Φ],g])) j))

include hg hbir in
private theorem exists_quadric_corner_decrease
    (hpole : B[Φ,hc].comap T.toBase = D * hT.ramificationIdealSheafToBase k₀)
    (j : Fin n) (hfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
    (hhigh : β < 2 * (-(mark[T,hT,f[Φ],g]).2 j))
    (σ : Φ.cones) (hj : hT.baseCenter j = (Φ.distinguishedSection (R :=
      k₀) σ) (IsLocalRing.closedPoint k₀))
    (d : Basis (Fin 2) ℤ N) (e : ℤ) (s : Fin 4 ≃ Φ.Ray)
    (hs : (fun l ↦ (s l).primitiveGenerator) = ![d 0, d 1, -d 0, e • d 0 - d 1])
    (hcone : σ.val = PointedCone.hull ℝ (Set.range (i ∘ d)))
    (hβ : (Φ.hirzebruchPicardBasis k₀ d e hΦ s hs).repr (mark[T,hT,f[Φ],g]).1 1 = β) :
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : IsIntegral Y := hT.isIntegral f[Φ]
    ∃ (A Q : LogarithmicProjection k₀ i D) (_ : SarkisovPath A Q),
      A.fan = Φ ∧ A.hom ≍ T.toBase ∧ hirzebruchTarget[Q,Y,g,D,old] := by
  intro hOver hSmooth hIntegral
  let := hOver
  let := hSmooth
  let := hIntegral
  let : X[k₀,Φ].IsProjectiveOver k₀ := Φ.isProjectiveOver_quadric k₀ b hΦ hc r hr
  have hn : 1 ≤ n := by have := j.isLt; omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨Q, p, d', s', hs', Z, U, hU, k, -, -, hQ, hproj, hg', hbir', hpole', -, -, -, -, -,
    hβ', -, -, hlt, -⟩ :=
    exists_sarkisov_path_of_toric_corner k₀ d e hΦ hc s hs hT g hg hbir σ hcone j hj hfirst
      D ((hT.ramificationIdealSheafToBase_def k₀) ▸ hpole)
  let : Nonempty Q.fan.cones := Q.isComplete.nonempty_cones
  obtain ⟨d₀, t, ht, -, -, -, hrepr⟩ :=
    Fan.exists_hirzebruchPicardBasis_natAbs k₀ d' (e + 1) Q.isRegular s' hs'
  have hpos := (hirzebruch_resolution_degree_bounds k₀ b 0 hΦ hc r hr hT g hg hbir).1
  refine ⟨_, Q, p, rfl, HEq.rfl, _, d₀, t, ht, Z, _, U, hU, k, hQ, hproj, hg', hbir',
    hpole', ?_⟩
  simpa only [hrepr] using And.intro (hβ'.symm ▸ hβ.symm ▸ hpos) (hβ ▸ hlt (hβ.symm ▸ hhigh))

include hg hbir in
private theorem exists_quadric_section_decrease
    (hpole : B[Φ,hc].comap T.toBase = D * hT.ramificationIdealSheafToBase k₀)
    (j : Fin n) (hfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
    (hhigh : β < 2 * (-(mark[T,hT,f[Φ],g]).2 j))
    (s : Fin 2) (c : k₀ˣ)
    (hj : let ρ := r ((![0, 2] : Fin 2 → Fin 4) s)
      hT.baseCenter j = ρ.binomialCenter k₀ rankTwo (b.detDualEquiv_self ρ.primitiveGenerator)
        (ρ.surjective_detCharacter b) c (IsLocalRing.closedPoint k₀)) :
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : IsIntegral Y := hT.isIntegral f[Φ]
    ∃ (A Q : LogarithmicProjection k₀ i D) (_ : SarkisovPath A Q),
      A.fan = Φ ∧ A.hom ≍ T.toBase ∧ hirzebruchTarget[Q,Y,g,D,old] := by
  intro hOver hSmooth hIntegral
  let := hOver
  let := hSmooth
  let := hIntegral
  let : X[k₀,Φ].IsProjectiveOver k₀ := Φ.isProjectiveOver_quadric k₀ b hΦ hc r hr
  have hn : 1 ≤ n := by have := j.isLt; omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨hproj, Z, U, hU, k, d, t, ht, hg', hbir', hpole', ⟨A, Q, p, hA, hAh, hQ, hQh,
    -, -⟩, -, -, -, -, -, -, hβ', -, hlt⟩ :=
    hT.exists_sarkisov_path_of_smooth_section k₀ b 0 hΦ hc r hr s g hg hbir
      c j hj hfirst D hpole
  have hpos := (hirzebruch_resolution_degree_bounds k₀ b 0 hΦ hc r hr hT g hg hbir).1
  rcases Q with ⟨Ω, hreg, hcomp, q, hqOver, hqDom, hqPole⟩
  dsimp only at hQ hQh
  subst Ω
  exact ⟨A, _, p, hA, hAh, _, d, t, ht, Z, _, U, hU, k, eq_of_heq hQh, hproj, hg', hbir',
    hpole', hβ'.symm ▸ hpos, hlt hhigh⟩

include hg hbir in
private theorem exists_quadric_decrease_of_no_high_order
    (hpole : B[Φ,hc].comap T.toBase = D * hT.ramificationIdealSheafToBase k₀)
    (hlow : ∀ j, 2 * (-(mark[T,hT,f[Φ],g]).2 j) ≤ β) :
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : IsIntegral Y := hT.isIntegral f[Φ]
    ∃ (A Q : LogarithmicProjection k₀ i D) (_ : SarkisovPath A Q),
      A.fan = Φ ∧ A.hom ≍ T.toBase ∧ hirzebruchTarget[Q,Y,g,D,old] := by
  intro hOver hSmooth hIntegral
  let := hOver
  let := hSmooth
  let := hIntegral
  let : X[k₀,Φ].IsProjectiveOver k₀ := Φ.isProjectiveOver_quadric k₀ b hΦ hc r hr
  let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f[Φ]
  let A : LogarithmicProjection k₀ i D := ⟨Φ, hΦ, hc, T.toBase, ⟨rfl⟩, inferInstance,
    (hT.ramificationIdealSheafToBase_def k₀) ▸ hpole⟩
  obtain ⟨Q, p, h⟩ :=
    hT.exists_sarkisov_path_decrease_of_no_high_multiplicity k₀ b 0 hΦ hc r hr g hg hbir
      A rfl HEq.rfl hlow
  rcases h with ⟨hr₀, Z, U, hU, k, -, hQ, -, hQh, hg', hbir', hpos, hlt⟩ |
    ⟨d, s, Z, U, hU, k, he, -⟩
  · rcases Q with ⟨Ω, hreg, hcomp, q, hqOver, hqDom, hqPole⟩
    dsimp only at hQ hQh
    subst Ω
    obtain rfl : q = k.hom ≫ U.toBase := eq_of_heq hQh
    let : Z.Over S := ⟨U.toBase ≫ f[Φ]⟩
    let : k.hom.IsOver S := ⟨by
      have h : Z ↘ S = (k.inv ≫ g) ≫ fP := hg'.symm
      rw [h, ← Category.assoc, k.hom_inv_id_assoc]
      exact hg⟩
    let : U.toBase.IsOver S := ⟨rfl⟩
    let : SmoothOfRelativeDimension 2 (Z ↘ S) := hU.smoothOfRelativeDimension f[Φ]
    have hp := (comap_eq_mul_ramificationIdealSheaf_comp_iff_of_isIso k₀ k.hom U.toBase 2
      (D := B[Φ,hc]) (Q := D)).mp hqPole
    rw [IsIso.inv_eq_of_hom_inv_id k.hom_inv_id, ← hU.ramificationIdealSheafToBase_def k₀] at hp
    exact ⟨A, _, p, rfl, HEq.rfl, 0, b, r, hr₀, Z, n, U, hU, k, rfl, inferInstance,
      hg', hbir', hp, hpos, hlt _⟩
  · exact (Nat.zero_ne_one he).elim

end

include hg hbir in
/-- A specified logarithmic quadric-to-plane resolution admits a resolved
Sarkisov path to a plane or Hirzebruch surface of strictly smaller bidegree.
The path uses the original resolving surface and pole ideal at every vertex.
The terminal projection is identified with a marked closed-point tower, which
retains the given map to the plane and its pole factorization. -/
theorem exists_sarkisov_path_decrease_of_quadric :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : IsIntegral Y := hT.isIntegral f[Φ]
    let x := mark[T,hT,f[Φ],g]
    let β := (Φ.hirzebruchPicardBasis k₀ b 0 hΦ r hr).repr x.1 1
    let δ := hirzebruchSarkisovBidegree β.toNat (∑ j, -x.2 j).toNat
    B[Φ,hc].comap T.toBase = D * hT.ramificationIdealSheafToBase k₀ →
    ∃ (A Q : LogarithmicProjection k₀ i D) (_ : SarkisovPath A Q),
      A.fan = Φ ∧ A.hom ≍ T.toBase ∧
      ((∃ (d : Basis (Fin 2) ℤ N) (Z : Scheme) (l : ℕ) (U : BlowupTower P l Z)
        (hU : IsClosedPointTower P U) (k : Y ≅ Z),
        Q.fan = Π[d] ∧ Q.hom ≍ k.hom ≫ U.toBase ≫ (planeIso[d]).inv ∧
        (k.inv ≫ g) ≫ fP = U.toBase ≫ fP ∧ Scheme.BirationalOver (k.inv ≫ g) (𝟙 P) ∧
        (B[Π[d],hcΠ[d]].comap (planeIso[d]).inv).comap U.toBase =
          D.comap k.inv * hU.ramificationIdealSheafToBase k₀ ∧
        let y := mark[U,hU,fP,k.inv ≫ g]
        0 < degree y.1 ∧ planeSarkisovBidegree (degree y.1).toNat (∑ j, -y.2 j).toNat < δ) ∨
      hirzebruchTarget[Q,Y,g,D,δ]) := by
  classical
  intro hcones hdim hOver hSmooth hInt x β δ hpole
  let := hcones
  let := hdim
  let := hOver
  let := hSmooth
  let := hInt
  let : X[k₀,Φ].IsProjectiveOver k₀ := Φ.isProjectiveOver_quadric k₀ b hΦ hc r hr
  let high := Finset.univ.filter (fun j ↦ β < 2 * (-x.2 j))
  by_cases hhigh : high.Nonempty
  · have hle : B[Φ,hc].comap T.toBase ≤ hT.ramificationIdealSheafToBase k₀ :=
      hpole.le.trans (mul_le_of_le_one_left' le_top)
    rcases hT.hirzebruch_high_baseCenter_cases k₀ b 0 hΦ hc r hr g hg hle hhigh with
      ⟨j, hj, hfirst, hcorner | hsection⟩ | ⟨-, fiber, hfiber⟩
    · obtain ⟨σ, ⟨-, hpoint, d, e, s, hs, hcone, hβ⟩, -⟩ := hcorner
      obtain ⟨A, Q, p, hA, hAh, ht⟩ :=
        exists_quadric_corner_decrease k₀ b hΦ hc r hr hT g hg hbir hpole j hfirst
          (Finset.mem_filter.mp hj).2 σ hpoint.symm d e s hs hcone hβ
      exact ⟨A, Q, p, hA, hAh, Or.inr ht⟩
    · obtain ⟨s, c, hpoint⟩ := hsection
      obtain ⟨A, Q, p, hA, hAh, ht⟩ :=
        exists_quadric_section_decrease k₀ b hΦ hc r hr hT g hg hbir hpole j hfirst
          (Finset.mem_filter.mp hj).2 s c hpoint
      exact ⟨A, Q, p, hA, hAh, Or.inr ht⟩
    · obtain ⟨A, Q, p, hA, hAh, ht⟩ :=
        hT.exists_sarkisov_path_decrease_of_quadric_high_fiber_centers k₀ b hΦ hc r hr g hg hbir
          hpole hhigh ⟨fiber, fun j ↦ ⟨(hfiber j).2.1, (hfiber j).2.2.1⟩⟩
      refine ⟨A, Q, p, hA, hAh, ?_⟩
      rcases ht with ⟨d, Z, l, U, hU, k, hQ, hQh, hg', hbir', hp, hpos, hlt⟩ |
        ⟨Ω, hΩ, hcΩ, d, t, ht, Z, l, U, hU, k, hQ, hQh, hproj, hg', hbir', hp, hpos, hlt⟩
      · exact Or.inl ⟨d, Z, l, U, hU, k, hQ, hQh, hg', hbir', hp, hpos, hlt _ _⟩
      · subst Ω
        exact Or.inr ⟨0, d, t, ht, Z, l, U, hU, k, eq_of_heq hQh, hproj, hg', hbir', hp, hpos,
          hlt _ _⟩
  · have hlow (j : Fin n) : 2 * (-x.2 j) ≤ β :=
      le_of_not_gt fun hj ↦ hhigh ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    obtain ⟨A, Q, p, hA, hAh, ht⟩ :=
      exists_quadric_decrease_of_no_high_order k₀ b hΦ hc r hr hT g hg hbir hpole hlow
    exact ⟨A, Q, p, hA, hAh, Or.inr ht⟩

end QPainleve.BlowupTower.IsClosedPointTower
