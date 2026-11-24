/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.Step

import QPainleve.Geometry.Toric.Fan.Hirzebruch.Projective
import QPainleve.Geometry.Toric.Fan.Logarithmic.SarkisovReduction

/-!
# Sarkisov induction with a plane target

The marked plane and quadric cases, together with a decrease for positive-index Hirzebruch
sources, give a resolved factorization for any two specified logarithmic toric projections.
The induction takes place on nodal refinements of the original resolving surface and keeps
the prescribed target projection throughout.

See [Lutz, proof of Theorem 8.4](https://arxiv.org/pdf/2005.05010v3#page=73).
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra

namespace TauCeti.Toric.Fan.LogarithmicProjection

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "s" => (P ↘ S)
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "plane[" b "," hi "]" => Fan.projectiveSpace b hi
local notation "planeIso[" b "," hi "]" =>
  (Fan.projectivePlaneIso b hi ≪≫ Basis.polynomialProjIso (Pi.basisFun ℂ (Fin 3)))
local notation "rankTwo(" b ")" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

variable
  (hstep : ∀ {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
    [IsIntegral X] [IsNoetherian X] {D : X.IdealSheafData}
    (A B : LogarithmicProjection i D)
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (b b' : Basis (Fin 2) ℤ N) (e : ℕ), 0 < e → ∀ (hi : IsIntegralLattice i)
    (r : Fin 4 ≃ A.fan.Ray)
    (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])
    [A.fan.algebraicRealization.IsProjectiveOver ℂ],
    B.fan = plane[b',hi] → ∀
    {Y : Scheme} {n : ℕ} (T : BlowupTower A.fan.algebraicRealization n Y)
    (hT : IsClosedPointTower A.fan.algebraicRealization T)
    (k : X ≅ Y) (g : Y ⟶ P),
    A.hom = k.hom ≫ T.toBase →
    B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv →
    g ≫ s = T.toBase ≫ (A.fan.algebraicRealization ↘ S) →
    Scheme.BirationalOver g (𝟙 P) →
    let f := (A.fan.algebraicRealization ↘ S)
    letI : SmoothOfRelativeDimension 2 f :=
      rankTwo(b) ▸ A.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap A.isRegular
    let x := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    let d := hirzebruchSarkisovBidegree
      ((A.fan.hirzebruchPicardBasis b e A.isRegular r hr).repr x.1 1).toNat
      (∑ j, -x.2 j).toNat
    HasPlaneTargetDecrease A B rankTwo(b) hD hNode d)

include hstep in
private theorem exists_sarkisov_step_of_marking
    {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
    [IsIntegral X] [IsNoetherian X] {D : X.IdealSheafData}
    (hRank : finrank ℤ N = 2)
    (A B : LogarithmicProjection i D) (d : ℕ ×ₗ ℕ)
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hmark : HasPlaneTargetMarking A B d) :
    Nonempty (SarkisovPath A B) ∨ HasPlaneTargetDecrease A B hRank hD hNode d := by
  cases hmark with
  | plane b b' hi hA hB T hT k g hAh hBh hg hbir =>
    exact exists_sarkisov_step_of_plane_marking (hT := hT) hD hNode hA hB k hAh hBh hg hbir
  | hirzebruch b b' e hi r hr hB T hT k g hAh hBh hg hbir =>
    cases e with
    | zero =>
      exact Or.inr (exists_sarkisov_step_of_quadric_marking r hr hT g hD hNode hB k hAh hBh hg hbir)
    | succ e =>
      let : A.fan.algebraicRealization.IsProjectiveOver ℂ :=
        A.fan.isProjectiveOver_hirzebruch b (e + 1 : ℕ) A.isRegular A.isComplete r hr
      exact Or.inr (hstep A B hD hNode b b' (e + 1) (Nat.succ_pos e) hi
        r hr hB T hT k g hAh hBh hg hbir)

include hstep in
/-- A strictly decreasing resolved block for each positive-index Hirzebruch marking
completes the factorization of a specified change between logarithmic toric projections
on a smooth projective surface. The resulting path has the original endpoint projections
pulled back to one nodal refinement, with the reduced total boundary as its pole ideal. -/
theorem exists_resolved_sarkisov_factorization_of_positive_hirzebruch_steps
    (b₀ : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
    [IsIntegral X] [X.IsProjectiveOver ℂ] {D : X.IdealSheafData}
    (A B : LogarithmicProjection i D) [IsModification A.hom] [IsModification B.hom]
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S)) :
    letI : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
    HasResolvedSarkisovFactorization A B := by
  apply exists_resolved_sarkisov_factorization_of_plane b₀ hi _ A B hD hNode
  intro Y hOver hIntegral hProjective hSmooth R hR hNodeR C E hModC hModE hC hE
  let : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ S)
  obtain ⟨d, hmark⟩ := exists_hasPlaneTargetMarking_of_plane C E b₀ b₀ hi hC hE
  exact hasResolvedSarkisovFactorization_iff.mpr
    (exists_sarkisov_path_of_bidegree_decrease rankTwo(b₀) hR hNodeR
      (fun C E d ↦ HasPlaneTargetMarking C E d)
      (exists_sarkisov_step_of_marking hstep rankTwo(b₀)) d hmark)

end TauCeti.Toric.Fan.LogarithmicProjection
