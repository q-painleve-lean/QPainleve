/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Complexity
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Smooth
public import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Boundary

import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Chow.Ample
import QPainleve.AlgebraicGeometry.Chow.ProjectivePlane.Numerical
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.PlanePrimeDivisor
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.Product
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample

/-!
# Toric recognition on the projective plane

An anticanonical nodal cycle of complexity zero in the projective plane consists of three
lines. The node opposite each line separates its defining linear form from the other two,
so the three forms give projective coordinates. This characterizes the toric case among the
projective-plane inputs to the toric model construction of Gross, Hacking and Keel,
[*Mirror symmetry for log Calabi–Yau surfaces I*, Proposition 1.3][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open AlgebraicGeometry AlgebraicGeometry.Proj CategoryTheory Limits Module TopologicalSpace
open QPainleve
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "V₃" => (Fin 3 → ℂ)
local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule ℂ V₃
local notation "P" => Proj 𝒜
local notation "std" => Pi.basisFun ℂ (Fin 3)
local notation "degree" => Module.Basis.picardTwistEquiv std
local notation "L" => Proj.symmetricAlgebraTwistingBundle ℂ V₃ 1
local notation "linearForm" => SymmetricAlgebra.ι ℂ V₃

attribute [local instance] MvPolynomial.gradedAlgebra

private instance : ∀ x : P, UniqueFactorizationMonoid ((P).presheaf.stalk x) :=
  (P ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two

variable {D : (P).IdealSheafData} [D.subscheme.Over S] [PrestableFamily (D.subscheme ↘ S)]
  {α : Type*} {a : α → (D.subscheme ↘ S).smoothLocus}

private theorem planeCycle_length {n : ℕ} [NeZero n] (A : Scheme.NodalCycleNumbering a n)
    (hD : D.IsEffectiveCartier) (hzero : D.boundaryComplexity = 0) : n = 3 := by
  have hn := (Nat.card_congr (A.boundaryPrimeEquiv hD)).symm
  rw [Nat.card_zmod] at hn
  have hn' : D.boundaryPrimes.ncard = n := hn
  rw [boundaryComplexity_def, finrank_projectivePlane, hn'] at hzero
  omega

private theorem planeCycle_primeDegree (A : Scheme.NodalCycleNumbering a 3)
    (hD : D.IsEffectiveCartier)
    (hcan : LineBundleClass.mk hD.toInvertibleSheaf = LineBundleClass.mk (canonicalBundle ℂ P 2)) :
    ∀ j : ZMod 3, degree (Additive.ofMul
      (primeDivisorClass (D.boundaryPrimeEmbedding (A.boundaryPrimeEquiv hD j)))) = 1 := by
  classical
  let p := (A.boundaryPrimeEquiv hD).toEmbedding.trans D.boundaryPrimeEmbedding
  have hp : ∀ q : CodimensionOnePoint P, (q : P) ∈ D.support ↔ q ∈ Set.range p := by
    have h : Set.range p = Set.range D.boundaryPrimeEmbedding :=
      (A.boundaryPrimeEquiv hD).surjective.range_comp D.boundaryPrimeEmbedding
    rw [h, D.range_boundaryPrimeEmbedding]
    exact fun _ ↦ Iff.rfl
  let : IsReduced D.subscheme := (PrestableFamily.atWorstNodalOfRelativeDimensionOne
    (f := D.subscheme ↘ S)).isReduced
  have hs := congrArg degree (hD.ofMul_inv_toInvertibleSheaf_eq_sum_primeDivisorClass p hp)
  rw [hcan, mk_canonicalBundle_projectivePlane, ofMul_inv, map_neg,
    (std).picardTwistEquiv_apply_twist, map_sum,
    ← (ZMod.finEquiv 3).toEquiv.sum_comp, Fin.sum_univ_three] at hs
  have hsum : degree (Additive.ofMul (primeDivisorClass (p 0))) +
      degree (Additive.ofMul (primeDivisorClass (p 1))) +
      degree (Additive.ofMul (primeDivisorClass (p 2))) = 3 := hs.symm
  have hpos (j : ZMod 3) : 0 < degree (Additive.ofMul (primeDivisorClass (p j))) := by
    have h : 0 < Chow.classIntersectionNumber ℂ P (LineBundleClass.mk L)
        (primeDivisorClass (p j)) :=
      Chow.classIntersectionNumber_primeDivisorClass_pos_of_isAmple ℂ
        (topologicalKrullDim_eq_of_smoothOfRelativeDimension (P ↘ S))
        (TauCeti.SymmetricAlgebra.isAmple_twistingSheaf ℂ V₃ Nat.one_pos) (p j)
    rwa [Chow.classIntersectionNumber_projectivePlane, (std).picardTwistEquiv_apply_twist,
      one_mul] at h
  intro j
  have hp₀ := hpos 0
  have hp₁ := hpos 1
  have hp₂ := hpos 2
  have h0 : degree (Additive.ofMul (primeDivisorClass (p 0))) = 1 := by omega
  have h1 : degree (Additive.ofMul (primeDivisorClass (p 1))) = 1 := by omega
  have h2 : degree (Additive.ofMul (primeDivisorClass (p 2))) = 1 := by omega
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

private theorem planeCycle_linearIndependent (A : Scheme.NodalCycleNumbering a 3)
    (hD : D.IsEffectiveCartier) (v : ZMod 3 → V₃)
    (hv : ∀ (j : ZMod 3) (x : P), x ∈ Proj.basicOpen 𝒜 (linearForm (v j)) ↔
      x ∉ closure {(A.boundaryPrimeEquiv hD j).val}) : LinearIndependent ℂ v := by
  rw [linearIndependent_iff_notMem_span]
  intro j
  let x := A.ambientNode (j + 1)
  have hx (l : ZMod 3) : x ∈ closure {(A.boundaryPrimeEquiv hD l).val} ↔ l ≠ j := by
    rw [A.ambientNode_mem_closure_boundaryPrime_iff hD]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [Fin.exists_fin_two, TauCeti.DualGraph.cycle, Fin.isValue, ite_true, h10, ite_false,
      ne_eq, ← (ZMod.val_injective 3).eq_iff, ZMod.val_add, ZMod.val_one]
    have hj := ZMod.val_lt j
    have hl := ZMod.val_lt l
    omega
  let J := (x.asHomogeneousIdeal.toIdeal.restrictScalars ℂ).comap linearForm
  have hJ (l : ZMod 3) : v l ∈ J ↔ l ≠ j := by
    have h := hv l x
    rw [Proj.mem_basicOpen] at h
    have hl : v l ∈ J ↔ linearForm (v l) ∈ x.asHomogeneousIdeal := Iff.rfl
    exact hl.trans ((not_iff_not.mp h).trans (hx l))
  have hspan : Submodule.span ℂ (v '' (Set.univ \ {j})) ≤ J := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    exact (hJ l).mpr hl.2
  exact fun h ↦ (hJ j).mp (hspan h) rfl

private theorem planeCycle_support (A : Scheme.NodalCycleNumbering a 3)
    (hD : D.IsEffectiveCartier) :
    (D.support : Set P) = ⋃ j : ZMod 3, closure {(A.boundaryPrimeEquiv hD j).val} := by
  classical
  let p := (A.boundaryPrimeEquiv hD).toEmbedding.trans D.boundaryPrimeEmbedding
  let : IsReduced D.subscheme := (PrestableFamily.atWorstNodalOfRelativeDimensionOne
    (f := D.subscheme ↘ S)).isReduced
  have hp : ∀ q : CodimensionOnePoint P, q ∈ Finset.univ.map p ↔ (q : P) ∈ D.support := by
    intro q
    simp only [Finset.mem_map, Finset.mem_univ, true_and, ← Set.mem_range]
    have h : Set.range p = Set.range D.boundaryPrimeEmbedding :=
      (A.boundaryPrimeEquiv hD).surjective.range_comp D.boundaryPrimeEmbedding
    rw [h, D.range_boundaryPrimeEmbedding]
    rfl
  have h := congrArg (fun K : (P).IdealSheafData ↦ (K.support : Set P))
    (hD.eq_prod_vanishingIdeal_of_isReduced _ hp)
  refine h.trans ?_
  simp only [Finset.prod_map, coe_support_prod, coe_support_vanishingIdeal, Closeds.coe_mk,
    p, Function.Embedding.trans_apply, Equiv.toEmbedding_apply, coe_boundaryPrimeEmbedding]

private theorem exists_toric_of_standardPlane_boundaryComplexity_zero
    {N W : Type} [AddCommGroup N] [AddCommGroup W] [Module ℝ W]
    {i : N →+ W} (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    {n : ℕ} [NeZero n] (A : Scheme.NodalCycleNumbering a n)
    (hD : D.IsEffectiveCartier)
    (hcan : LineBundleClass.mk hD.toInvertibleSheaf = LineBundleClass.mk (canonicalBundle ℂ P 2))
    (hzero : D.boundaryComplexity = 0) :
    ∃ e : (projectiveSpace b hi).algebraicRealization ≅ P,
      e.hom ≫ P ↘ S = (projectiveSpace b hi).algebraicRealizationStructureMap ∧
      D.comap e.hom = (projectiveSpace b hi).boundaryIdeal
        (isComplete_projectiveSpace b hi).nonempty_cones := by
  have hn := planeCycle_length A hD hzero
  subst n
  choose v hv using fun j ↦ (D.boundaryPrimeEmbedding (A.boundaryPrimeEquiv hD j))
    |>.exists_linearForm_of_projectivePlane_degree_eq_one (planeCycle_primeDegree A hD hcan j)
  simp only [coe_boundaryPrimeEmbedding] at hv
  let a := (ZMod.finEquiv 3).toEquiv
  let c := basisOfLinearIndependentOfCardEqFinrank ((planeCycle_linearIndependent A hD v hv).comp
    a a.injective) (Module.finrank_fintype_fun_eq_card ℂ).symm
  let e := projectivePlaneIso b hi ≪≫ c.polynomialProjIso
  refine ⟨e, ?_, ?_⟩
  · let := projectivePlaneIso_trans_polynomialProjIso_hom_isOver b hi c
    rw [← algebraicRealization_over]
    exact CategoryTheory.comp_over e.hom S
  let : IsReduced D.subscheme := (PrestableFamily.atWorstNodalOfRelativeDimensionOne
    (f := D.subscheme ↘ S)).isReduced
  let h₀ := (isComplete_projectiveSpace b hi).nonempty_cones
  let H (j : Fin 3) := Proj.coordinateHyperplaneIdeal (k := ℂ) (n := 2) j
  have hrad := (D.isReduced_subscheme_iff_radical_eq).mp ‹IsReduced D.subscheme›
  have htriangle : D.comap c.polynomialProjIso.hom = (∏ j, H j).radical := by
    rw [← hrad, ← radical_comap_of_isOpenImmersion,
      ← vanishingIdeal_support, ← vanishingIdeal_support]
    congr 1
    apply SetLike.coe_injective
    rw [support_comap, Closeds.coe_preimage, planeCycle_support A hD, coe_support_prod]
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion]
    have hc (j : Fin 3) : c j = v (a j) :=
      congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) j
    have hmem (j : Fin 3) :
        c.polynomialProjIso.hom x ∈ closure {(A.boundaryPrimeEquiv hD (a j)).val} ↔
          x ∈ ((H j).support : Set _) := by
      have hopen :
          c.polynomialProjIso.hom x ∈ Proj.basicOpen 𝒜 (linearForm (c j)) ↔
            x ∈ (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)
              (MvPolynomial.X j) : Set _) := by
        have hr := c.polynomialProjIso_hom_preimage_basicOpen_ι j
        exact (Scheme.Hom.mem_preimage (f := c.polynomialProjIso.hom)).symm.trans
          (by rw [hr]
              rfl)
      dsimp only [H]
      rw [coe_support_coordinateHyperplaneIdeal, Set.mem_compl_iff, ← hopen, hc, hv, not_not]
    exact ⟨fun ⟨j, hj⟩ ↦ ⟨a.symm j, (hmem _).mp (by simpa only [a.apply_symm_apply] using hj)⟩,
      fun ⟨j, hj⟩ ↦ ⟨a j, (hmem j).mpr hj⟩⟩
  dsimp only [e]
  rw [Iso.trans_hom, comap_comp, htriangle]
  exact projectivePlaneIso_comap_coordinateTriangle b hi h₀

/-- A complexity-zero anticanonical cycle on a surface isomorphic to the complex
projective plane is the boundary of the projective-space fan. The returned
isomorphism is over the ground field and identifies the boundary ideals. -/
theorem exists_toric_of_projectivePlane_boundaryComplexity_zero
    {N W : Type} [AddCommGroup N] [AddCommGroup W] [Module ℝ W]
    {i : N →+ W} (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
    (e : P ≅ X) [e.hom.IsOver S] {E : X.IdealSheafData}
    [E.subscheme.Over S] [PrestableFamily (E.subscheme ↘ S)]
    (hOver : E.subscheme ↘ S = E.subschemeι ≫ X ↘ S)
    {β : Type*} {p : β → (E.subscheme ↘ S).smoothLocus}
    {n : ℕ} [NeZero n] (A : Scheme.NodalCycleNumbering p n)
    (hE : E.IsEffectiveCartier)
    (hcan : LineBundleClass.mk hE.toInvertibleSheaf = LineBundleClass.mk (canonicalBundle ℂ X 2))
    (hzero : E.boundaryComplexity = 0) :
    ∃ f : (projectiveSpace b hi).algebraicRealization ≅ X,
      f.hom ≫ X ↘ S = (projectiveSpace b hi).algebraicRealizationStructureMap ∧
      E.comap f.hom = (projectiveSpace b hi).boundaryIdeal
        (isComplete_projectiveSpace b hi).nonempty_cones := by
  let F := E.comap e.hom
  let d : F.subscheme ≅ E.subscheme := E.comapIso e.hom ≪≫ asIso (pullback.snd e.hom E.subschemeι)
  let : F.subscheme.Over S := ⟨F.subschemeι ≫ P ↘ S⟩
  have hd : d.hom ≫ E.subschemeι = F.subschemeι ≫ e.hom := by
    rw [Iso.trans_hom, asIso_hom, Category.assoc, ← pullback.condition,
      ← Category.assoc, E.comapIso_hom_fst]
  have hstructure : d.hom ≫ E.subscheme ↘ S = F.subscheme ↘ S := by
    rw [hOver, ← Category.assoc, hd, Category.assoc, CategoryTheory.comp_over e.hom S]
    rfl
  let : d.symm.hom.IsOver S := ⟨by rw [← hstructure, Iso.symm_hom, Iso.inv_hom_id_assoc]⟩
  let : PrestableFamily (F.subscheme ↘ S) := hstructure ▸
    (MorphismProperty.cancel_left_of_respectsIso («P» := @PrestableFamily) d.hom _).mpr
      inferInstance
  let q : Empty → (F.subscheme ↘ S).smoothLocus := Empty.elim
  let B := d.symm.mapNodalCycleNumbering A (q := q)
  have hF : F.IsEffectiveCartier := hE.comap e.hom
  have hcanF :
      LineBundleClass.mk hF.toInvertibleSheaf = LineBundleClass.mk (canonicalBundle ℂ P 2) := by
    rw [← hE.pullback_mk_toInvertibleSheaf hF, hcan, pullback_mk, mk_pullback_canonicalBundle]
  have hzeroF : F.boundaryComplexity = 0 := (boundaryComplexity_comap_iso e E).trans hzero
  obtain ⟨f, hf, hFf⟩ :=
    exists_toric_of_standardPlane_boundaryComplexity_zero b hi B hF hcanF hzeroF
  refine ⟨f ≪≫ e, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, CategoryTheory.comp_over e.hom S, hf]
  · rw [Iso.trans_hom, comap_comp]
    exact hFf

end TauCeti.Toric.Fan
