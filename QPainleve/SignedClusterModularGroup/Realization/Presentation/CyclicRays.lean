/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.CyclicOrder.Survivors
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Numbered

import QPainleve.Geometry.Toric.Fan.Boundary.ContractedNumbering
import QPainleve.Geometry.Toric.Fan.Boundary.OrderedContraction
import QPainleve.Geometry.Toric.Fan.CyclicOrder.Construction

/-!
# Signed loop substitutions from cyclic toric ray coordinates

A positive cyclic ray list and a valid sequence of boundary contractions determine a
numbered Picard lattice. The signed cluster modular group in universal coefficient
coordinates is the signed boundary isometry group of this lattice when the numerical
boundary tests give a primitive nef square-zero class.

The realization combines `Fan.exists_fan_of_cyclic_rays`,
`Fan.exists_numbered_contraction_of_square_neg_one` and
`Fan.exists_oriented_numbering_of_contracted_toric_boundary`. It applies
`exists_signedLoopSubstitutions_mulEquiv_of_numbered_contraction` to the resulting model.
The numerical presentation is that of the [signed cluster modular group comparator
challenge][comparator].

[comparator]: https://github.com/q-painleve-lean/QPainleve/pull/841
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric TauCeti.Toric.Fan Module

namespace QPainleve.SignedClusterModularGroup

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "b₂" => Pi.basisFun ℤ (Fin 2)

section Comparison

variable {m : ℕ} [NeZero m] {ι : Type} [Fintype ι] [DecidableEq ι]
  (u : ZMod m → Fin 2 → ℤ) (ρ : ι → ZMod m) (l : List (ZMod m))

local notation "V₀" => (ZMod m ⊕ ι → ℤ)
local notation "F" => (Matrix.toBilin' (Fan.numberedInternalBlowupGram ι u))
local notation "a" => (l.map (Fan.numberedStrictBoundaryCoefficients ρ))
local notation "n" => Finset.card (survivingRayIndices l)
local notation "vₛ" => Finset.orderEmbOfFin (survivingRayIndices l) rfl
local notation "E" => SkewExchangeMatrix.ofChargeCoordinates (u ∘ ρ)

private theorem exists_signed_comparison_with_survivors
    {d q : ℕ} [NeZero q] (hmd : m = q + d) (hd : l.length = d)
    (f : Fin q ↪o Fin m) (hf : ∀ j : Fin m, j ∈ Set.range f ↔ ZMod.finEquiv m j ∉ l)
    (hdet : ∀ j, (b₂).detDualEquiv (u j) (u (j + 1)) = 1)
    (hwind : (Finset.univ.filter fun j ↦ u j 1 < 0 ∧ 0 ≤ u (j + 1) 1).card = 1)
    (hl : l.Nodup) (hlen : l.length < m)
    {R : Submodule ℤ V₀} (B : LinearMap.BilinForm ℤ (V₀ ⧸ R))
    (hR : R = Submodule.span ℤ (Set.range fun k : Fin 2 ↦ Sum.elim (fun j ↦ u j k) 0))
    (hB : B.compl₁₂ R.mkQ R.mkQ = F)
    (hs : ∀ x ∈ (F).orthogonalizeNegOnes a, F x x = -1) :
    let j := ZMod.finEquiv m ∘ f ∘ (ZMod.finEquiv q).symm
    let P := B.orthogonal
      (Submodule.span ℤ {x | x ∈ l.map fun k ↦ R.mkQ (Fan.numberedStrictBoundaryCoefficients ρ k)})
    let x := fun k ↦ (F).projectOffNegOnes a (Fan.numberedStrictBoundaryCoefficients ρ (j k))
    (∃ y, F (∑ k, x k) y = 1) →
    (∀ k, 0 ≤ F (∑ i, x i) (x k)) →
    F (∑ k, x k) (∑ k, x k) = 0 →
    ∃ A : ZMod q → P, (∀ k, (A k).val = R.mkQ (x k)) ∧
      Nonempty (signedLoopSubstitutions E ≃* signedBoundaryIsometryGroup (B.restrict P) A) := by
  subst m
  intro j P x hp hn hz
  obtain ⟨Φ, hΦ, hc, v, hv, hcone⟩ := Fan.exists_fan_of_cyclic_rays u hdet hwind
  let : Nonempty Φ.cones := hc.nonempty_cones
  have hv' (k : ZMod (q + d)) :
      (b₂).detDualEquiv (v k).primitiveGenerator (v (k + 1)).primitiveGenerator = 1 ∧
        ∃ σ : Φ.cones, (v k).toCone ≤ σ ∧ (v (k + 1)).toCone ≤ σ :=
    ⟨by simpa only [hv] using hdet k,
      ⟨⟨_, hcone k⟩, Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩⟩
  let o := Fintype.equivFin ι |>.symm
  -- The ordered internal tower allows repeated centers on the same ray.
  let c : Fin (Fintype.card ι) → ℂˣ := fun _ ↦ 1
  have hcoord (k : ZMod (q + d)) : (b₂).repr (v k).primitiveGenerator = u k := by
    funext t
    simp [hv]
  obtain ⟨X, z, hi, hP, hS, hrat, D, hD, hpreD, _, W, T, e, hT, he, hsupp, hsurv, _⟩ :=
    Fan.exists_numbered_contraction_of_square_neg_one b₂ hΦ hc v o ρ c hv' l hl hlen
      (by simpa only [hcoord] using hs)
  -- Identify the tower length with the difference of the two boundary lengths.
  revert hsurv hsupp he hT e T
  rw [hd]
  intro T e hT he hsupp hsurv _
  let : X.Over S := ⟨z⟩
  let : IsIntegral X := hi
  let : X.IsProjectiveOver ℂ := hP
  let : SmoothOfRelativeDimension 2 (X ↘ S) := hS
  let : Scheme.IsRationalOver (X ↘ S) := hrat
  let : PrestableFamily (D.subscheme ↘ S) := hpreD
  obtain ⟨htor, C, A, g, hC, hker, hg, hgOver, hsub, hj⟩ :=
    Fan.exists_oriented_numbering_of_contracted_toric_boundary hΦ hc b₂ (v ∘ ρ ∘ o) c v
      hT.isClosedPointTower e hv' he hsupp hD f
      (fun k ↦ (hsurv (ZMod.finEquiv _ k)).trans (hf k).symm)
  let : PrestableFamily ((Φ.boundaryIdeal (inferInstance : Nonempty Φ.cones)).subscheme ↘ S) :=
    htor
  let : g.IsOver S := hgOver
  have hrange (k : ZMod (q + d)) : k ∈ Set.range j ↔ k ∉ l := by
    obtain ⟨k, rfl⟩ := (ZMod.finEquiv (q + d)).surjective k
    simpa [j, Set.range_comp, EquivLike.range_eq_univ] using hf k
  have hj' (k : ZMod q) := hj ((ZMod.finEquiv q).symm k)
  simp only [RingEquiv.apply_symm_apply] at hj'
  have hE := Fan.reindex_ofChargeCoordinates_eq_rayExchangeMatrix b₂ (v ∘ ρ ∘ o) o (c := u ∘ ρ)
    (fun k ↦ hcoord (ρ (o k)))
  subst v
  have h := exists_signedLoopSubstitutions_mulEquiv_of_numbered_contraction hΦ hc A C hD
    o ρ c hT e he hker g hg hsub hv' B
    (by simpa only [hcoord] using hR) (by simpa only [hcoord] using hB) l j
    (fun k ↦ by simpa only [not_not] using (not_congr (hrange k)).symm)
    hj' (SkewExchangeMatrix.ofChargeCoordinates (u ∘ ρ)) hE
  simp only [hB] at h
  exact h hs hp hn hz

/-- Compute the signed cluster modular group from cyclic ray coordinates, center labels and
an ordered list of contractions. The quotient form is induced by the numbered intersection
matrix. The right-hand boundary classes are the successive projections of the surviving
strict ray classes in ascending ray order. The three tests on their sum certify primitivity,
nefness and square zero. -/
theorem exists_signedLoopSubstitutions_mulEquiv_of_cyclic_rays
    (hdet : ∀ j, (b₂).detDualEquiv (u j) (u (j + 1)) = 1)
    (hwind : (Finset.univ.filter fun j ↦ u j 1 < 0 ∧ 0 ≤ u (j + 1) 1).card = 1)
    (hl : l.Nodup) (hlen : l.length < m)
    {R : Submodule ℤ V₀} (B : LinearMap.BilinForm ℤ (V₀ ⧸ R))
    (hR : R = Submodule.span ℤ (Set.range fun k : Fin 2 ↦ Sum.elim (fun j ↦ u j k) 0))
    (hB : B.compl₁₂ R.mkQ R.mkQ = F)
    (hs : ∀ x ∈ (F).orthogonalizeNegOnes a, F x x = -1) :
    let : NeZero n := ⟨by
      rw [card_survivingRayIndices, List.toFinset_card_of_nodup hl]
      exact Nat.sub_ne_zero_of_lt hlen⟩
    let j := ZMod.finEquiv m ∘ vₛ ∘ (ZMod.finEquiv n).symm
    let P := B.orthogonal
      (Submodule.span ℤ {x | x ∈ l.map fun k ↦ R.mkQ (Fan.numberedStrictBoundaryCoefficients ρ k)})
    let x := fun k ↦ (F).projectOffNegOnes a (Fan.numberedStrictBoundaryCoefficients ρ (j k))
    (∃ y, F (∑ k, x k) y = 1) →
    (∀ k, 0 ≤ F (∑ i, x i) (x k)) →
    F (∑ k, x k) (∑ k, x k) = 0 →
    ∃ A : ZMod n → P, (∀ k, (A k).val = R.mkQ (x k)) ∧
      Nonempty (signedLoopSubstitutions E ≃* signedBoundaryIsometryGroup (B.restrict P) A) := by
  intro _
  have hm : m = n + l.length := by
    rw [card_survivingRayIndices, List.toFinset_card_of_nodup hl, Nat.sub_add_cancel hlen.le]
  exact exists_signed_comparison_with_survivors u ρ l hm rfl vₛ
    (fun k ↦ by simpa only [Finset.range_orderEmbOfFin, Finset.mem_coe] using
      mem_survivingRayIndices l k) hdet hwind hl hlen B hR hB hs

end Comparison
end QPainleve.SignedClusterModularGroup
