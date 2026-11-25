/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.Step

import QPainleve.SignedClusterModularGroup.SarkisovDegree.MixedQuadric.PreparedExit
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Quadric.Corner
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Quadric.MarkedExit

/-!
# The marked exit from a prepared quadric

After elementary transformations along a positive section, the quadric carries one
or two marked first centers on distinct invariant fibers. The numerical preparation
bound gives a primary Sarkisov decrease, by a plane exit for one mark or a quadric
exit for two marks. The exit uses the marked plane target throughout. The links are
those of [Lutz, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra

namespace TauCeti.Toric.Fan.LogarithmicProjection

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "plane[" b "," hi "]" => Fan.projectiveSpace b hi
local notation "planeIso[" b "," hi "]" =>
  (Fan.projectivePlaneIso b hi ≪≫ Basis.polynomialProjIso (Pi.basisFun ℂ (Fin 3)))
local notation "rankTwo[" b "]" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "pt" => IsLocalRing.closedPoint ℂ
local notation "center[" b "," ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ rankTwo[b] (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c pt

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
  [IsIntegral X] [IsNoetherian X] {D : X.IdealSheafData} {A B : LogarithmicProjection i D}
  {Y : Scheme} {b b' : Basis (Fin 2) ℤ N} {hi : IsIntegralLattice i}
  (r : Fin 4 ≃ A.fan.Ray)
  (hr : (fun t ↦ (r t).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
  {n : ℕ} {T : BlowupTower A.fan.algebraicRealization n Y}
  (hT : IsClosedPointTower A.fan.algebraicRealization T) (g : Y ⟶ P)

local notation "fA" => (A.fan.algebraicRealization ↘ S)
local notation "smooth[" b "]" =>
  (Eq.mp (congrArg (fun m ↦ SmoothOfRelativeDimension m fA) rankTwo[b])
    (A.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap A.isRegular))
local notation "x" =>
  (LinearEquiv.symm (BlowupTower.picardMarking T hT fA) (Additive.ofMul (pullback g H)))
local notation "C" => A.fan.hirzebruchPicardBasis b 0 A.isRegular r hr
local notation "α" => Basis.repr (C) (Prod.fst x) 0
local notation "β" => Basis.repr (C) (Prod.fst x) 1
local notation "order[" j "]" => -(Prod.snd x) j
local notation "fiber[" t "]" => r ((![1, 3] : Fin 2 → Fin 4) t)
local notation "onFiber[" t "," j "]" =>
  (∃ c : ℂˣ, hT.baseCenter j = center[b,fiber[t],c])
local notation "atCorner[" t "," j "]" =>
  (∃ σ : A.fan.cones, Nat.card (ToricRay σ.val) = 2 ∧ Fan.Ray.toCone A.fan (fiber[t]) ≤ σ ∧
    Fan.Ray.toCone A.fan (r 0) ≤ σ ∧ hT.baseCenter j = A.fan.distinguishedPointHom σ pt)

variable (hD : D.IsEffectiveCartier)
  (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
  (hB : B.fan = plane[b',hi]) (k : X ≅ Y)
  (hAh : A.hom = k.hom ≫ T.toBase) (hBh : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv)
  (hg : g ≫ (P ↘ S) = T.toBase ≫ (A.fan.algebraicRealization ↘ S))
  (hbir : Scheme.BirationalOver g (𝟙 P))

include hB k hAh hBh hg hbir

private theorem decrease_of_one_prepared_quadric_center
    (t : Fin 2) (j : Fin n) (hjfirst : ∀ q < j, hT.baseCenter q ≠ hT.baseCenter j)
    (hj : onFiber[t,j] ∨ atCorner[t,j]) (d : ℕ ×ₗ ℕ) :
    let : Nonempty A.fan.cones := A.isComplete.nonempty_cones
    let : SmoothOfRelativeDimension 2 fA := smooth[b]
    2 * (α - order[j]) < β → 3 * Int.toNat β ≤ (ofLex d).1 →
    HasPlaneTargetDecrease A B rankTwo[b] hD hNode d := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (Fin.pos_iff_nonempty.mpr ⟨j⟩))
  intro hcones hdim hbound hd
  let := hcones
  let := hdim
  rcases hj with ⟨c, hj⟩ | ⟨σ, hσ, -, -, hj⟩
  · refine exists_sarkisov_step_of_quadric_smooth_center r hr hT g hD hNode
      hB k hAh hBh hg hbir t c j hj hjfirst d ?_ hd
    omega
  · refine exists_sarkisov_step_of_quadric_corner r hr hT g hD hNode
      hB k hAh hBh hg hbir σ hσ j hj hjfirst d ?_ hd
    omega

private theorem decrease_of_two_prepared_quadric_centers
    (j l : Fin n) (hjl : j ≠ l)
    (hjfirst : ∀ q < j, hT.baseCenter q ≠ hT.baseCenter j)
    (hlfirst : ∀ q < l, hT.baseCenter q ≠ hT.baseCenter l)
    (hj : onFiber[0,j] ∨ atCorner[0,j]) (hl : onFiber[1,l] ∨ atCorner[1,l]) (d : ℕ ×ₗ ℕ) :
    let : Nonempty A.fan.cones := A.isComplete.nonempty_cones
    let : SmoothOfRelativeDimension 2 fA := smooth[b]
    α < order[j] + order[l] → 3 * Int.toNat β ≤ (ofLex d).1 →
    HasPlaneTargetDecrease A B rankTwo[b] hD hNode d := by
  have hn : 2 ≤ n := by
    apply Nat.succ_le_of_lt
    simpa only [Fintype.card_fin] using Fintype.one_lt_card_iff.mpr ⟨j, l, hjl⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  intro hcones hdim hbound hd
  let := hcones
  let := hdim
  rcases open_fiber_centers_or_sarkisov_step_of_prepared_quadric r hr hT g hD hNode
      hB k hAh hBh hg hbir hjl hjfirst hlfirst hj hl d hbound hd with ⟨⟨c, hc⟩, c', hc'⟩ | h
  · rw [← Equiv.swap_apply_left (0 : Fin 2) 1] at hc'
    exact exists_sarkisov_step_of_quadric_two_smooth_fiber_centers r hr hT g hD hNode
      hB k hAh hBh hg hbir j l hjl 0 c c' hc hc' hjfirst hlfirst d hbound hd
  · exact h

/-- A nonempty set of retained first centers on distinct invariant fibers of a
quadric gives a decreasing block for the specified plane projection. Each mark
is either on its fiber's open orbit or at its corner on the section `r 0`.
If there are `s` marks with orders summing to `M`, the preparation bound is
`2 * (a - M) < (2 - s) * β`, where `a` is the transverse degree and `β` is the
fiber degree. The block decreases the bidegree against `(3 * β, m)` for arbitrary
secondary degree `m`. Taking `m = 0` gives a strict primary decrease. Additional
centers may have arbitrary orders, including at infinitely near points. -/
theorem exists_sarkisov_step_of_prepared_quadric
    (J : Finset (Fin n)) (hJ : J.Nonempty) (fiber : J ↪ Fin 2)
    (hfirst : ∀ j : J, ∀ q < (j : Fin n), hT.baseCenter q ≠ hT.baseCenter j)
    (hmem : ∀ j : J, onFiber[fiber j,(j : Fin n)] ∨ atCorner[fiber j,(j : Fin n)])
    (m : ℕ) :
    let : Nonempty A.fan.cones := A.isComplete.nonempty_cones
    let : SmoothOfRelativeDimension 2 fA := smooth[b]
    2 * (α - ∑ j ∈ J, order[j]) < (2 - (J.card : ℤ)) * β →
    HasPlaneTargetDecrease A B rankTwo[b] hD hNode
      (hirzebruchSarkisovBidegree (Int.toNat β) m) := by
  classical
  intro hcones hdim hbound
  let := hcones
  let := hdim
  let d := hirzebruchSarkisovBidegree (Int.toNat β) m
  have hd : 3 * Int.toNat β ≤ (ofLex d).1 := by
    simp only [d, ofLex_hirzebruchSarkisovBidegree, le_refl]
  have hcard : J.card ≤ 2 := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      Fintype.card_le_of_injective fiber fiber.injective
  have hpos := Finset.card_pos.mpr hJ
  have hex : J.card = 1 ∨ J.card = 2 := by omega
  rcases hex with h | h
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h
    let j' : ({j} : Finset (Fin n)) := ⟨j, Finset.mem_singleton_self j⟩
    refine decrease_of_one_prepared_quadric_center r hr hT g hD hNode hB k hAh hBh
      hg hbir (fiber j') j (hfirst j') (hmem j') d ?_ hd
    norm_num only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, one_mul] at hbound
    omega
  · obtain ⟨j, l, hjl, rfl⟩ := Finset.card_eq_two.mp h
    let j' : ({j, l} : Finset (Fin n)) := ⟨j, Finset.mem_insert_self j _⟩
    let l' : ({j, l} : Finset (Fin n)) :=
      ⟨l, Finset.mem_insert_of_mem (Finset.mem_singleton_self l)⟩
    have hne : fiber j' ≠ fiber l' := fun he ↦ hjl (congrArg Subtype.val (fiber.injective he))
    have hsum : α < order[j] + order[l] := by
      simp only [Finset.sum_pair hjl, Finset.card_pair hjl, Nat.cast_ofNat, sub_self,
        zero_mul] at hbound
      omega
    have hf : (fiber j' = 0 ∧ fiber l' = 1) ∨ (fiber j' = 1 ∧ fiber l' = 0) := by
      generalize fiber j' = a, fiber l' = b at hne ⊢
      fin_cases a <;> fin_cases b <;> simp_all
    rcases hf with ⟨hj, hl⟩ | ⟨hj, hl⟩
    · exact decrease_of_two_prepared_quadric_centers r hr hT g hD hNode hB k hAh hBh
        hg hbir j l hjl (hfirst j') (hfirst l') (hj ▸ hmem j') (hl ▸ hmem l') d hsum hd
    · exact decrease_of_two_prepared_quadric_centers r hr hT g hD hNode hB k hAh hBh
        hg hbir l j hjl.symm (hfirst l') (hfirst j') (hl ▸ hmem l') (hj ▸ hmem j') d
        (by simpa only [add_comm] using hsum) hd

end TauCeti.Toric.Fan.LogarithmicProjection
