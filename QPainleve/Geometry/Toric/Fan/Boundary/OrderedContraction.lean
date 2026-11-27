/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.OrderedBlowdown
public import QPainleve.Geometry.Toric.Fan.Picard.NumberedMarking

import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.Geometry.Toric.Fan.Boundary.BlowupNumbering
import QPainleve.Geometry.Toric.Fan.Boundary.Canonical
import QPainleve.Geometry.Toric.Fan.Boundary.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Logarithmic.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Rationality

/-!
# Ordered contractions from numbered toric intersection data

The numerical elimination of strict boundary classes gives the successive
self-intersection tests for nodal blowdowns of the internal blowup. The
numbered Picard map and the strict boundary numbering identify the two tests.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower
open TauCeti TauCeti.AlgebraicGeometry Module
open Scheme.IdealSheafData LineBundleClass

namespace TauCeti.Toric.Fan

universe u

variable (K : Type u) [Field K] [IsAlgClosed K] [NeZero (2 : K)] {N V : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {m r : ℕ} [NeZero m]
  (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (v : ZMod m ≃ Φ.Ray) (o : Fin r ≃ ι) (ρ : ι → ZMod m) (c : Fin r → Kˣ)

local notation "S" => Spec (CommRingCat.of K)
local notation "s" => (v ∘ ρ ∘ o)
local notation "U" => Fan.internalBlowupTower K b s c
local notation "Y" => Sigma.fst U
local notation "Z" => Φ.finiteFanScheme K
local notation "T₀" => WithBoundary.toTower (Sigma.snd U)
local notation "D₀" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd U))
local notation "F₀" => (Matrix.toBilin' (Fan.numberedInternalBlowupGram ι
  (fun j ↦ b.repr (Fan.Ray.primitiveGenerator (v j)))))
local notation "a₀" => (Fan.numberedStrictBoundaryCoefficients ρ)

include hc in
/-- Realize ordered contractions of strict ray components from the square-minus-one
tests in their numbered divisor coordinates. The projection pulls back the
anticanonical boundary support to the strict toric boundary and takes exactly the
uncontracted primes to boundary primes. The total exceptional classes record the
successive updates in reverse order, since the tower builds the inverse blowups. -/
theorem exists_numbered_contraction_of_square_neg_one
    (hv : ∀ j, b.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ)
    (l : List (ZMod m)) (hl : l.Nodup) (hlen : l.length < m)
    (hsq : ∀ x ∈ (F₀).orthogonalizeNegOnes (l.map a₀), F₀ x x = -1) :
    ∃ (X : Scheme) (z : X ⟶ S),
      let : X.Over S := ⟨z⟩
      ∃ (_ : IsIntegral X) (_ : X.IsProjectiveOver K) (_ : SmoothOfRelativeDimension 2 (X ↘ S)),
        Scheme.IsRationalOver (X ↘ S) ∧
        ∃ (D : X.IdealSheafData) (hD : D.IsEffectiveCartier)
          (_ : PrestableFamily (D.subscheme ↘ S)),
          LineBundleClass.mk hD.toInvertibleSheaf = LineBundleClass.mk (canonicalBundle K X 2) ∧
          ∃ (W : Scheme) (T : BlowupTower X l.length W) (e : Y ≅ W),
            IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T ∧
            e.hom ≫ T.toBase ≫ (X ↘ S) = (T₀).toBase ≫ Φ.finiteFanSchemeToSpec K ∧
            (D.comap (e.hom ≫ T.toBase)).support = (D₀).support ∧
            (∀ j : ZMod m,
              (e.hom ≫ T.toBase) (internalBlowupBoundaryPrimeEquiv K hΦ b s c (v j)).val ∈
                D.boundaryPrimes ↔ j ∉ l) ∧
            (List.ofFn fun k ↦ Additive.ofMul (pullback e.hom (T.exceptionalClass k))) =
              (((F₀).orthogonalizeNegOnes (l.map a₀)).map
                (numberedInternalBlowupPicardMap K b hΦ v o ρ c)).reverse := by
  let : (Z).IsProjectiveOver K := Φ.isProjectiveOver_finiteFanScheme_of_isComplete K hΦ hc b
  have hdim : finrank ℤ N = 2 := (finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let : SmoothOfRelativeDimension 2 (Z ↘ S) := by
    rw [Φ.finiteFanScheme_over K]
    exact hdim ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ
  let : Scheme.IsRationalOver (Z ↘ S) := by
    rw [Φ.finiteFanScheme_over K]
    exact Φ.isRationalOver_of_isComplete K hΦ hc b
  let hU := Fan.isClosedPointTower_internalBlowupTower K b s c
  let : (Y).Over S := ⟨(T₀).toBase ≫ (Z ↘ S)⟩
  let : IsIntegral Y := Fan.isIntegral_internalBlowupTower K b s c hΦ
  let : (Y).IsProjectiveOver K := (T₀).isProjectiveOver K
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hU.smoothOfRelativeDimension (Z ↘ S)
  let : Scheme.IsRationalOver (Y ↘ S) := hU.isRationalOver (Z ↘ S)
  let : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ S)
  let := (Y ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hZ := Φ.isEffectiveCartier_boundaryIdeal K hΦ hc hdim
  have hY := Fan.isEffectiveCartier_internalBlowupBoundary K b s hΦ c hZ
  have hcan := Fan.canonicalClass_internalBlowupTower K b s c hΦ hZ hY
    (Φ.canonicalClass_boundaryIdeal K hΦ hc b hZ)
  obtain ⟨_, hpre, _, A, _, _, _, hprime⟩ :=
    Fan.exists_numbering_internalBlowup_of_cyclicRays K hΦ hc b s c v hv hY
  let : PrestableFamily ((D₀).subscheme ↘ S) := hpre
  let B := Chow.intersectionBilinForm K Y
  let f := Fan.numberedInternalBlowupPicardMap K b hΦ v o ρ c
  have hf (x y : ZMod m ⊕ ι → ℤ) : B (f x) (f y) = F₀ x y := by
    have h : B.compl₁₂ f f = F₀ :=
      Fan.numberedInternalBlowupPicardMap_intersection K b hΦ v o ρ c hc hv
    exact (LinearMap.compl₁₂_apply ..).symm.trans congr($h x y)
  have ha (j : ZMod m) : f (a₀ j) = Additive.ofMul
      (primeDivisorClass ((D₀).boundaryPrimeEmbedding (A.boundaryPrimeEquiv hY j))) := by
    let p := Fan.internalBlowupBoundaryPrimeEquiv K hΦ b s c (v j)
    have hp : (D₀).boundaryPrimeEmbedding p = ⟨p.val, (mem_boundaryPrimes.mp p.property).2⟩ :=
      Subtype.ext ((D₀).coe_boundaryPrimeEmbedding p)
    rw [hprime, hp]
    exact Fan.numberedInternalBlowupPicardMap_strictBoundary K b hΦ v o ρ c j
  let classes := fun j ↦
    Additive.ofMul (primeDivisorClass ((D₀).boundaryPrimeEmbedding (A.boundaryPrimeEquiv hY j)))
  have hclasses : (l.map a₀).map f = l.map classes :=
    (List.map_map ..).trans (congrArg (fun g ↦ l.map g) (funext ha))
  have horth := ((F₀).map_orthogonalizeNegOnes f hf (l.map a₀)).trans
    (congrArg B.orthogonalizeNegOnes hclasses)
  have hsq' : ∀ x ∈ B.orthogonalizeNegOnes (l.map classes), B x x = -1 := by
    rw [← horth]
    simpa only [List.forall_mem_map, hf] using hsq
  obtain ⟨X, z, p, hI, hP, hS, hR, hp, D, hD, hpreD, hK, hsupp, hsurv, W, T, e, hT, he, hE⟩ :=
    A.exists_nodal_boundary_tower_of_ordered_contractions hY hcan l hl hlen hsq'
  let : X.Over S := ⟨z⟩
  let : p.IsOver S := hp
  refine ⟨X, z, hI, hP, hS, hR, D, hD, hpreD, hK, W, T, e, hT, ?_, ?_, ?_, ?_⟩
  · rw [reassoc_of% he, comp_over p S]
    exact congrArg ((T₀).toBase ≫ ·) (Φ.finiteFanScheme_over K)
  · simpa only [he] using hsupp
  · simpa only [he, hprime] using hsurv
  · exact hE.trans (congrArg List.reverse horth.symm)

end TauCeti.Toric.Fan
