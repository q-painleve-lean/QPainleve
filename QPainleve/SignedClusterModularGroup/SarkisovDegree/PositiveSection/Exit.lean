/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Incidence
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.InvariantFiber
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Quadric.PreparedExit

import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.BaseMultiplicity
import QPainleve.Geometry.Toric.Fan.Smooth

/-!
# Exiting positive-section preparation

After preparation to index zero, the original marks can still be indexed by
their original set. Distinct invariant ruling values separate the projected
centers. Absence from the strict transforms of the prepared section puts each
first center either in the open fiber orbit or at the opposite corner. The
prepared quadric links then give the decrease for the specified plane map.
The preparation step is the one in [Lutz, Proposition 8.11, Case C][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra

namespace TauCeti.Toric.Fan.LogarithmicProjection

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "planeIso[" b "," hi "]" =>
  (Fan.projectivePlaneIso b hi ≪≫ Basis.polynomialProjIso (Pi.basisFun ℂ (Fin 3)))
local notation "pt" => (IsLocalRing.closedPoint ℂ : S)
local notation "p[" j "]" => projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) j 0

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
  [IsIntegral X] [IsNoetherian X] {D : X.IdealSheafData} {A B : LogarithmicProjection i D}
  {Y : Scheme} {b b' : Basis (Fin 2) ℤ N} {hi : IsIntegralLattice i}
  (r : Fin 4 ≃ A.fan.Ray)
  (hr : (fun t ↦ (r t).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
  {n : ℕ} {T : BlowupTower A.fan.algebraicRealization n Y}
  (hT : IsClosedPointTower A.fan.algebraicRealization T) (g : Y ⟶ P)

local notation "fA" => (A.fan.algebraicRealization ↘ S)
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "q" =>
  Fan.characterRuling A.fan (LinearMap.toAddMonoidHom (b.coord 1))
    (Fan.nonneg_or_nonpos_hirzebruch_ruling_character b 0 r hr)
local notation "C" => A.fan.hirzebruchPicardBasis b 0 A.isRegular r hr
local notation "Jsec" => A.fan.rayBoundaryIdeal A.isRegular (r 2)

/-- A prepared quadric has a decreasing block for the original plane map
when the retained first centers have distinct invariant ruling values and
the required total order. The centers are indexed by the original marks.
Their absence from the strict transforms of section `r 2` allows a mark at
the corresponding corner on `r 0`, as well as on the open invariant fiber. -/
theorem exists_sarkisov_step_of_prepared_quadric_ruling_values
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hB : B.fan = Fan.projectiveSpace b' hi) (k : X ≅ Y)
    (hAh : A.hom = k.hom ≫ T.toBase) (hBh : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv)
    (hg : g ≫ (P ↘ S) = T.toBase ≫ fA) (hbir : Scheme.BirationalOver g (𝟙 P))
    {ι : Type*} [Fintype ι] [Nonempty ι] (fiber : ι ↪ Fin 2) (index : ι → Fin n)
    (hfirst : ∀ a, ∀ l < index a, hT.baseCenter l ≠ hT.baseCenter (index a))
    (hvalue : ∀ a, q (hT.baseCenter (index a)) = p[fiber a] pt) (m : ℕ) :
    let : Nonempty A.fan.cones := A.isComplete.nonempty_cones
    let : SmoothOfRelativeDimension 2 fA :=
      rankTwo ▸ A.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap A.isRegular
    let : IsNoetherian A.fan.algebraicRealization := by
      let : Smooth fA := SmoothOfRelativeDimension.smooth 2 fA
      exact isNoetherian_of_finiteType fA
    let x := (T.picardMarking hT fA).symm (Additive.ofMul (pullback g H))
    let α := Basis.repr C x.1 0
    let β := Basis.repr C x.1 1
    let order := fun j : Fin n ↦ -x.2 j
    (∀ a, index a ∉ hT.strictTransformCenterIndices Jsec) →
    2 * (α - ∑ a, order (index a)) < (2 - (Fintype.card ι : ℤ)) * β →
    HasPlaneTargetDecrease A B rankTwo hD hNode (hirzebruchSarkisovBidegree β.toNat m) := by
  intro hcones hdim hnoeth x α β order hoff hbound
  let := hcones
  let := hdim
  let := hnoeth
  have hcoord : Function.Injective (fun j : Fin 2 ↦ p[j] pt) := by
    have hzero : p[0] pt ∈ Set.range (projectiveLine.polynomialChartι ℂ 0) := by
      rw [projectiveLine.polynomialPoint_def]
      exact ⟨_, (rfl)⟩
    have hne : p[0] pt ≠ p[1] pt := fun h ↦
      projectiveLine.infinitySection_notMem_range_polynomialChartι ℂ pt
        (by rwa [← projectiveLine.polynomialPoint_zero, ← h])
    intro a c hac
    fin_cases a <;> fin_cases c <;> first | rfl | exact (hne hac).elim | exact (hne hac.symm).elim
  let emb : ι ↪ Fin n := ⟨index, fun a c he ↦ fiber.injective (hcoord
    ((hvalue a).symm.trans ((congrArg (fun j ↦ q (hT.baseCenter j)) he).trans (hvalue c))))⟩
  let J := Finset.univ.map emb
  let E : ι ≃ J := (Equiv.subtypeUnivEquiv Finset.mem_univ).symm.trans
    (Finset.equivMap emb Finset.univ)
  have hE (a : ι) : (E a : Fin n) = index a :=
    Finset.equivMap_apply_coe emb Finset.univ _
  have hindex (j : J) : index (E.symm j) = (j : Fin n) :=
    (hE (E.symm j)).symm.trans (congrArg Subtype.val (E.apply_symm_apply j))
  have hcard : J.card = Fintype.card ι := by simp [J]
  have hsum : (∑ j ∈ J, order j) = ∑ a, order (index a) := by
    rw [Finset.sum_map]
    rfl
  let targetFiber := E.symm.toEmbedding.trans fiber
  refine exists_sarkisov_step_of_prepared_quadric r hr hT g hD hNode
    hB k hAh hBh hg hbir J Finset.univ_nonempty.map targetFiber ?_ ?_ m ?_
  · intro j
    simpa only [hindex] using hfirst (E.symm j)
  · intro j
    let a := E.symm j
    have hnot : hT.baseCenter (index a) ∉ (Jsec).support := by
      intro hmem
      apply hoff a
      exact (hT.mem_strictTransformCenterIndices _ _).mpr
        ((hT.strictTransformCoefficients_ne_zero_iff_of_first fA
          (A.fan.isEffectiveCartier_rayBoundaryIdeal A.isRegular (r 2)) (hfirst a)).mpr hmem)
    have h := (A.fan.hirzebruch_ruling_eq_coordinatePoint_and_notMem_section_iff
      b 0 A.isRegular A.isComplete r hr (fiber a) 0 (hT.isClosed_baseCenter (index a))).mp
      ⟨hvalue a, hnot⟩
    simpa only [a, hindex, targetFiber, Function.Embedding.trans_apply,
      Equiv.toEmbedding_apply, Matrix.cons_val_zero] using h
  · -- Use the same marked coordinates to compare the sums under the two indexings.
    change 2 * (α - ∑ j ∈ J, order j) < (2 - (J.card : ℤ)) * β
    simpa only [hcard, hsum] using hbound

end TauCeti.Toric.Fan.LogarithmicProjection
