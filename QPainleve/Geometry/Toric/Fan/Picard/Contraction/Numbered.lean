/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Sequence
public import QPainleve.Geometry.Toric.Fan.Picard.NumberedMarking

import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
import QPainleve.LinearAlgebra.BilinearForm.Isometry
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic

/-!
# Numbered divisor coordinates after toric boundary contractions

The numbered divisor quotient for an ordered internal blowup restricts to the Picard
lattice of a nodal contraction. The restriction uses the orthogonal complement of the
contracted boundary classes and identifies the surviving prime classes by the successive
square-minus-one updates.

The comparison uses `Fan.numberedInternalBlowupPicardIsometry` upstairs and
`Fan.contractedPicardMarking_symm_boundaryPrime_eq_projectOffNegOnes` downstairs.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory LinearMap Module
open QPainleve QPainleve.BlowupTower TauCeti TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

namespace TauCeti.Toric.Fan

variable {N V : Type} {ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {m n : ℕ} [NeZero m] [Fintype ι]
  (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (v : ZMod m ≃ Φ.Ray) (o : Fin n ≃ ι) (ρ : ι → ZMod m) (c : Fin n → ℂˣ)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Z" => Φ.algebraicRealization
local notation "s" => (v ∘ ρ ∘ o)
local notation "U" => internalBlowupTower b s c
local notation "Y" => (Sigma.fst U)
local notation "T₀" => WithBoundary.toTower (Sigma.snd U)
local notation "A" => (ZMod m ⊕ ι → ℤ)
local notation "F" => numberedInternalBlowupPicardMap b hΦ v o ρ c
local notation "Aux" => (LinearMap.BilinForm.prod (Chow.intersectionBilinForm ℂ Z)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin n → ℤ))))
local notation "strict" j:arg => numberedStrictBoundaryCoefficients ρ j
local notation "rayClass" j:arg => markedBoundaryMap hΦ s (Pi.single (v j) 1)
local notation "Gram" =>
  numberedInternalBlowupGram ι (fun j ↦ Basis.repr b (Ray.primitiveGenerator (v j)))

include c in
open Classical in
private theorem exists_numberedAuxIsometry (hv : (∀ j,
  b.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
    ∃ σ : Φ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ)) {R : Submodule ℤ A}
    (B : LinearMap.BilinForm ℤ (A ⧸ R))
    (hR : R = Submodule.span ℤ (Set.range fun a : Fin 2 ↦
      Sum.elim (fun j ↦ b.repr (v j).primitiveGenerator a) 0))
    (hB : B.compl₁₂ R.mkQ R.mkQ = Matrix.toBilin' Gram) :
    let : (Z).IsProjectiveOver ℂ := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
    let : SmoothOfRelativeDimension 2 (Z ↘ S) :=
      (algebraicRealization_over Φ).symm ▸
        (((finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
          Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ)
    ∃ g : B.IsometryEquiv Aux, ∀ j, g (R.mkQ (strict j)) = rayClass j := by
  intro _ _
  let : (Y).Over S := ⟨(T₀).toBase ≫ Z ↘ S⟩
  let : (Y).IsProjectiveOver ℂ := (T₀).isProjectiveOver ℂ
  let : IsIntegral Y := isIntegral_internalBlowupTower b s c hΦ
  let hU := isClosedPointTower_internalBlowupTower b s c
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hU.smoothOfRelativeDimension (Z ↘ S)
  let : IsNoetherian Y := (T₀).isNoetherian
  let := (Y ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  obtain ⟨q, hq⟩ := numberedInternalBlowupPicardIsometry b hΦ v o ρ c hc hv B hR hB
  let f : (Aux).IsometryEquiv (Chow.intersectionBilinForm ℂ Y) :=
    { internalBlowupPicardMarking b s c hΦ with
      map_app' := fun x y ↦ by
        simpa only [picardMarking_apply, internalBlowupPicardMarking_apply,
          Chow.intersectionBilinForm_apply, LinearMap.BilinForm.prod_apply, LinearMap.neg_apply,
          LinearMap.toFun_eq_coe, LinearEquiv.coe_coe, dotProductBilin_apply_apply, dotProduct,
          sub_eq_add_neg] using classIntersectionNumber_picardMarking ℂ hU x y }
  refine ⟨q.trans f.symm, fun j ↦ f.injective ?_⟩
  simp only [BilinForm.IsometryEquiv.trans_apply, BilinForm.IsometryEquiv.coe_toLinearEquiv,
    f.apply_symm_apply, hq, numberedInternalBlowupPicardMap_strictBoundary]
  -- The underlying linear map of the isometry is the ordered tower marking.
  change _ = internalBlowupPicardMarking b s c hΦ (rayClass j)
  rw [internalBlowupPicardMarking_apply, picardHom_markedBoundaryMap_single_eq_primeDivisorClass]

variable {X W : Scheme} [X.Over S] [X.IsProjectiveOver ℂ] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ S)] {D : X.IdealSheafData} {d : ℕ}
  {T : BlowupTower X d W}
  (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T) (e : (internalBlowupTower b (v ∘ ρ ∘ o) c).1 ≅ W)
  (he : e.hom ≫ T.toBase ≫ (X ↘ S) =
    (internalBlowupTower b (v ∘ ρ ∘ o) c).2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap)
  (hD : (D.comap (e.hom ≫ T.toBase)).support =
    (internalBlowupTower b (v ∘ ρ ∘ o) c).2.boundaryι.ker.support)

local notation "p" => (e.hom ≫ T.toBase)
local notation "Span" a:arg => Submodule.span ℤ (Set.ofPred fun x ↦ x ∈ a)

local instance numberedContraction_noetherian : IsNoetherian X :=
  isNoetherian_of_finiteType (X ↘ S)

local instance numberedContraction_factorial (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) :=
  (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two x

local instance numberedContraction_normal : IsNormalScheme X :=
  IsNormalScheme.of_uniqueFactorizationMonoid_stalk

include he in
open Classical in
/-- The contracted Picard lattice is the orthogonal complement of the span of the
specified strict boundary classes in the numbered divisor quotient. If the ordered
contractions have square minus one at each step, the inverse isometry sends each
surviving prime class to the successive update of its numbered strict class. -/
theorem exists_numberedContractedPicardIsometry (hv : (∀ j,
  b.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
    ∃ σ : Φ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ)) {R : Submodule ℤ A}
    (B : LinearMap.BilinForm ℤ (A ⧸ R))
    (hR : R = Submodule.span ℤ (Set.range fun a : Fin 2 ↦
      Sum.elim (fun j ↦ b.repr (v j).primitiveGenerator a) 0))
    (hB : B.compl₁₂ R.mkQ R.mkQ = Matrix.toBilin' Gram)
    (l : List (ZMod m)) :
    let : (Z).IsProjectiveOver ℂ := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
    let : IsModification p := isModification_orderedContraction hΦ b s c hT e
    let a := contractedBoundaryRayEmbedding hΦ b s c p hD
    let C := l.map fun j ↦ R.mkQ (strict j)
    let P := B.orthogonal (Span C)
    (∀ j, j ∈ l ↔ v j ∉ Set.range a) →
    (∀ x ∈ B.orthogonalizeNegOnes C, B x x = -1) →
    ∃ g : (B.restrict P).IsometryEquiv (Chow.intersectionBilinForm ℂ X),
      ∀ x : D.boundaryPrimes,
        (g.symm (Additive.ofMul (primeDivisorClass (D.boundaryPrimeEmbedding x)))).val =
          B.projectOffNegOnes C (R.mkQ (strict (v.symm (a x)))) := by
  intro _ _ a C P hl hsq
  let : SmoothOfRelativeDimension 2 (Z ↘ S) :=
    ((finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
      Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ S)
  let hU := isClosedPointTower_internalBlowupTower b s c
  let E := markedExceptionalSpan ℂ hU T e
  let g₀ := contractedPicardMarking ℂ hT.isClosedPointTower hU e he
  obtain ⟨q, hq⟩ := exists_numberedAuxIsometry b hΦ hc v o ρ c hv B hR hB
  let l' := l.map v
  let C' := l'.map fun r ↦ markedBoundaryMap hΦ s (Pi.single r 1)
  have hlist : C.map q.toLinearMap = C' := by
    simp only [C, C', l', List.map_map]
    exact congrArg (fun f ↦ l.map f) (funext hq)
  have hl' (r : Φ.Ray) : r ∈ l' ↔ r ∉ Set.range a := by
    obtain ⟨j, rfl⟩ := v.surjective r
    simp only [l', List.mem_map]
    exact ⟨fun ⟨k, hk, hkj⟩ ↦ (hl j).mp (v.injective hkj ▸ hk),
      fun hj ↦ ⟨j, (hl j).mpr hj, rfl⟩⟩
  have hspan : (Span C).map q.toLinearMap = E := by
    dsimp only [E]
    rw [markedExceptionalSpan_eq_span_compl_survivingRays hΦ b s c hT e hD, Submodule.map_span]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, ← List.mem_map, hlist]
    simp only [C', List.mem_map, hl', Set.mem_compl_iff]
    rfl
  have hpair (x y) : (Aux) (q.toLinearMap x) (q.toLinearMap y) = B x y := q.map_app y x
  have hmap : P.map q.toLinearMap = (Aux).orthogonal E := (q.map_orthogonal _).trans
    (congrArg (Aux).orthogonal hspan)
  let g := q.ofSubmodules P _ hmap
  have hsq' : ∀ x ∈ (Aux).orthogonalizeNegOnes C', (Aux) x x = -1 := by
    rw [← hlist, ← B.map_orthogonalizeNegOnes q.toLinearMap hpair C]
    simpa only [List.forall_mem_map, hpair] using hsq
  refine ⟨g.trans g₀, fun x ↦ q.injective ?_⟩
  have hx := contractedPicardMarking_symm_boundaryPrime_eq_projectOffNegOnes
    hΦ b s c hT e he hD l' x hl' hsq'
  rw [BilinForm.IsometryEquiv.symm_trans_apply]
  have hleft := BilinForm.IsometryEquiv.coe_ofSubmodules_symm_apply q hmap
    (g₀.symm (Additive.ofMul (primeDivisorClass (D.boundaryPrimeEmbedding x))))
  have hproj := B.map_projectOffNegOnes q.toLinearMap hpair C (R.mkQ (strict (v.symm (a x))))
  rw [hlist] at hproj
  have hinput : q.toLinearMap (R.mkQ (strict (v.symm (a x)))) =
      markedBoundaryMap hΦ s (Pi.single (a x) 1) := by
    simpa only [LinearEquiv.coe_coe, BilinForm.IsometryEquiv.coe_toLinearEquiv,
      Equiv.apply_symm_apply] using hq (v.symm (a x))
  rw [hinput] at hproj
  have hprime : D.boundaryPrimeEmbedding x = ⟨x.val, (mem_boundaryPrimes.mp x.property).2⟩ :=
    Subtype.ext (D.coe_boundaryPrimeEmbedding x)
  rw [← hprime] at hx
  have hright := hx.trans hproj.symm
  exact ((congrArg q hleft).trans (q.apply_symm_apply _)).trans
    (by simpa only [LinearEquiv.coe_coe] using hright)

end TauCeti.Toric.Fan
