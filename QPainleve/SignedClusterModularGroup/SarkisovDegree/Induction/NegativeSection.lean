/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.Marking

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.SignedClusterModularGroup.SarkisovDegree.NoHighMultiplicity.Path

/-!
# Marking the negative-section contraction

When a positive-index Hirzebruch-to-plane resolution has no base order above
half the ruling degree, contracting the negative section yields a plane source.
The new marking gives a smaller Sarkisov bidegree for the same specified target
projection on the same resolving surface.

See [Lutz, proof of Theorem 8.4][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "s" => (P ↘ S)
local notation "coords" => Pi.basisFun ℂ (Fin 3)
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "plane[" b "," hi "]" => Fan.projectiveSpace b hi
local notation "planeIso[" b "," hi "]" =>
  (Fan.projectivePlaneIso b hi ≪≫ Basis.polynomialProjIso coords)
local notation "mark[" T "," hT "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking T hT f) (Additive.ofMul (pullback g H))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} {Y : Scheme} {b b' : Basis (Fin 2) ℤ N}
  {hi : IsIntegralLattice i}
  (a : ℕ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (a : ℤ) • b 0 - b 1])
  {n : ℕ} {T : BlowupTower Φ.algebraicRealization n Y}
  (hT : IsClosedPointTower Φ.algebraicRealization T) (g : Y ⟶ P)

local notation "f" => (Φ.algebraicRealization ↘ S)
local notation "x" => mark[T,hT,f,g]
local notation "β" => Basis.repr (Fan.hirzebruchPicardBasis b a hΦ r hr) (Prod.fst x) 1
local notation "order[" j "]" => -(Prod.snd x) j
local notation "measure" =>
  hirzebruchSarkisovBidegree (Int.toNat β)
    (Int.toNat (sarkisovSecondaryDegree ℂ (Additive.toMul (Prod.fst x))))

variable [Φ.algebraicRealization.IsProjectiveOver ℂ] [Nonempty Φ.cones]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S)] [IsNoetherian Φ.algebraicRealization]
  {J : Y.IdealSheafData}

include hc in
/-- A positive-index Hirzebruch marking with all orders at most half the
fiber degree admits a resolved Sarkisov path to a plane marking of strictly
smaller bidegree for the same plane target. -/
theorem exists_sarkisov_path_with_smaller_plane_marking_of_no_high_order
    (ha : 0 < a) (hg : g ≫ s = T.toBase ≫ f) (hbir : Scheme.BirationalOver g (𝟙 P))
    (hlow : ∀ j, 2 * order[j] ≤ β) :
    let : Y.Over S := ⟨T.toBase ≫ f⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f
    let : IsIntegral Y := hT.isIntegral f
    ∀ {L R : LogarithmicProjection i J}, L.fan = Φ → L.hom ≍ T.toBase →
      R.fan = plane[b',hi] → R.hom ≍ g ≫ (planeIso[b',hi]).inv →
      ∃ next, next < measure ∧
        ∃ (C : LogarithmicProjection i J) (d : Basis (Fin 2) ℤ N),
          C.fan = plane[d,hi] ∧ Nonempty (SarkisovPath L C) ∧
          HasPlaneTargetMarking C R next := by
  intro hOver hSmooth hInt L R hL hhL hR hhR
  let := hOver
  let := hSmooth
  let := hInt
  rcases hT.exists_sarkisov_path_decrease_of_no_high_multiplicity
    b a hΦ hc r hr g hg hbir L hL hhL hlow with ⟨C, p, hzero | hplane⟩
  · obtain ⟨_, _, _, _, _, he, _⟩ := hzero
    omega
  · obtain ⟨d, _, Z, U, hU, k, _, hC, _, hhC, hg', hb', _, hlt⟩ := hplane
    let : IsNoetherian P := isNoetherian_of_finiteType s
    let y := mark[U,hU,s,k.inv ≫ g]
    let degree := (Basis.picardTwistEquiv coords y.1).toNat
    refine ⟨planeSarkisovBidegree degree (sarkisovSecondaryDegree ℂ y.1.toMul).toNat, ?_,
      C, d, hC, ⟨p⟩, .plane d b' hi hC hR U hU k (k.inv ≫ g) hhC ?_ hg' hb'⟩
    · rw [hT.sarkisovSecondaryDegree_eq_sum g hg hbir]
      exact hlt _
    · simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hhR

end TauCeti.Toric.Fan.LogarithmicProjection
