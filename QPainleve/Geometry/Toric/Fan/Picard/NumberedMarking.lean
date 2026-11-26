/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
public import QPainleve.Geometry.Toric.Fan.Boundary.SelfIntersection
public import QPainleve.Geometry.Toric.Fan.Picard.StrictTransform
public import QPainleve.Geometry.Toric.Fan.Subdivision.Projective

import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection

/-!
# The numbered Picard marking of an internal toric blowup

Divisor coefficients on the cyclically numbered rays and on the labeled total
exceptional divisors give a presentation of the Picard lattice. The two
coordinate characters generate its relations, and its intersection matrix is
the toric wall matrix with an orthogonal negative identity block.

The map uses `Fan.exact_characterToRayDivisor_rayDivisorToPicard` and the
closed-point tower marking. The strict boundary comparison uses
`Fan.picardHom_markedBoundaryMap_single_eq_primeDivisorClass`. In particular,
the exceptional coordinates refer to total transforms even for repeated centers.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory LinearMap Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

section Coordinates

variable {m : ℕ} {ι : Type*}

/-- The divisor coefficients of a strict toric boundary component after internal
blowups, given the ray of each center. -/
def numberedStrictBoundaryCoefficients (ρ : ι → ZMod m) (j : ZMod m) :
    ZMod m ⊕ ι → ℤ :=
  Sum.elim (Pi.single j 1) (fun a ↦ if ρ a = j then -1 else 0)

variable (ι) in
open Classical in
/-- The intersection matrix in ray and total exceptional divisor coordinates for
a numbered fan. The ray block uses the cyclic wall intersections. -/
def numberedInternalBlowupGram (u : ZMod m → Fin 2 → ℤ) :
    Matrix (ZMod m ⊕ ι) (ZMod m ⊕ ι) ℤ :=
  Matrix.fromBlocks
    (Matrix.of fun j k ↦
      (if k = j + 1 then 1 else 0) + (if k = j - 1 then 1 else 0) +
        if k = j then toricBoundarySelfIntersection u j else 0)
    0 0 (Matrix.diagonal fun _ ↦ -1)

@[simp]
theorem numberedStrictBoundaryCoefficients_inl (ρ : ι → ZMod m) (j k : ZMod m) :
    numberedStrictBoundaryCoefficients ρ j (.inl k) = (Pi.single j 1 : ZMod m → ℤ) k :=
  (rfl)

@[simp]
theorem numberedStrictBoundaryCoefficients_inr (ρ : ι → ZMod m) (j : ZMod m) (a : ι) :
    numberedStrictBoundaryCoefficients ρ j (.inr a) = if ρ a = j then -1 else 0 :=
  (rfl)

open Classical in
theorem numberedInternalBlowupGram_def (u : ZMod m → Fin 2 → ℤ) :
    numberedInternalBlowupGram ι u =
      Matrix.fromBlocks (Matrix.of fun j k ↦
        (if k = j + 1 then 1 else 0) + (if k = j - 1 then 1 else 0) +
          if k = j then toricBoundarySelfIntersection u j else 0)
        0 0 (Matrix.diagonal fun _ ↦ -1) :=
  (rfl)

end Coordinates

variable {N V : Type} {ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {m n : ℕ}
  (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular)
  (e : ZMod m ≃ Φ.Ray) (o : Fin n ≃ ι) (ρ : ι → ZMod m) (c : Fin n → ℂˣ)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Z" => Φ.algebraicRealization
local notation "model" => internalBlowupTower b (e ∘ ρ ∘ o) c
local notation "Y" => Sigma.fst model
local notation "T" => WithBoundary.toTower (Sigma.snd model)
local notation "A" => (ZMod m ⊕ ι → ℤ)
local notation "Pic" X:arg => Additive (LineBundleClass X)

private def numberedPicardCoordinates : A →ₗ[ℤ] (Pic Z × (Fin n → ℤ)) :=
  ((Φ.rayDivisorToPicard hΦ).toIntLinearMap.prodMap (LinearMap.id : (Fin n → ℤ) →ₗ[ℤ] _)) ∘ₗ
    ((LinearEquiv.funCongrLeft ℤ ℤ e.symm).prodCongr
      (LinearEquiv.funCongrLeft ℤ ℤ o)).toLinearMap ∘ₗ
    (LinearEquiv.sumArrowLequivProdArrow (ZMod m) ι ℤ ℤ).toLinearMap

private theorem numberedPicardCoordinates_apply (x : A) :
    numberedPicardCoordinates hΦ e o x =
      (Φ.rayDivisorToPicard hΦ (fun j ↦ x (.inl (e.symm j))), fun j ↦ x (.inr (o j))) :=
  (rfl)

/-- Interpret the numbered ray coefficients as pulled-back toric divisors and the
center coefficients as the full transforms of the exceptional divisors. -/
def numberedInternalBlowupPicardMap : A →ₗ[ℤ] Pic Y :=
  (T).picardHom ∘ₗ numberedPicardCoordinates hΦ e o

/-- The numbered map in the ordered tower marking. -/
theorem numberedInternalBlowupPicardMap_apply (x : A) :
    numberedInternalBlowupPicardMap b hΦ e o ρ c x =
      internalBlowupPicardMarking b (e ∘ ρ ∘ o) c hΦ
        (Φ.rayDivisorToPicard hΦ (fun j ↦ x (.inl (e.symm j))), fun j ↦ x (.inr (o j))) := by
  rw [internalBlowupPicardMarking_apply]
  exact congrArg (T).picardHom (numberedPicardCoordinates_apply hΦ e o x)

/-- The numbered divisor and exceptional coefficients generate the Picard group. -/
theorem numberedInternalBlowupPicardMap_surjective :
    Function.Surjective (numberedInternalBlowupPicardMap b hΦ e o ρ c) := by
  intro y
  obtain ⟨⟨a, f⟩, rfl⟩ := (internalBlowupPicardMarking b (e ∘ ρ ∘ o) c hΦ).surjective y
  obtain ⟨g, rfl⟩ := Φ.rayDivisorToPicard_surjective hΦ a
  refine ⟨Sum.elim (g ∘ e) (f ∘ o.symm), ?_⟩
  rw [numberedInternalBlowupPicardMap_apply]
  simp [Function.comp_apply]

private def numberedCharacterDivisor : Dual ℤ N →ₗ[ℤ] A :=
  (LinearEquiv.sumArrowLequivProdArrow (ZMod m) ι ℤ ℤ).symm.toLinearMap ∘ₗ
    ((LinearMap.funLeft ℤ ℤ e).comp
      (Φ.characterToRayDivisor.comp LinearMap.toAddMonoidHom').toIntLinearMap).prod (0 : _ →ₗ[ℤ] _)

omit [Nonempty Φ.cones] in
private theorem numberedCharacterDivisor_apply (χ : Dual ℤ N) :
    numberedCharacterDivisor (Φ := Φ) (ι := ι) e χ =
      Sum.elim (fun j ↦ χ (e j).primitiveGenerator) 0 := by
  funext j
  cases j <;>
    simp [numberedCharacterDivisor, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl,
      LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr]

private theorem ker_numberedPicardCoordinates :
    ker (numberedPicardCoordinates hΦ e o) =
      (numberedCharacterDivisor (Φ := Φ) (ι := ι) e).range := by
  ext x
  rw [mem_ker, mem_range, numberedPicardCoordinates_apply, Prod.mk_eq_zero]
  rw [Φ.exact_characterToRayDivisor_rayDivisorToPicard hΦ (fun j ↦ x (.inl (e.symm j)))]
  simp only [Set.mem_range, numberedCharacterDivisor_apply]
  constructor
  · rintro ⟨⟨χ, hχ⟩, ho⟩
    refine ⟨χ.toIntLinearMap, funext fun j ↦ ?_⟩
    cases j with
    | inl j => simpa using congrFun hχ (e j)
    | inr j => simpa using (congrFun ho (o.symm j)).symm
  · rintro ⟨χ, rfl⟩
    exact ⟨⟨χ.toAddMonoidHom, funext fun j ↦ by simp⟩, rfl⟩

/-- The two coordinate character divisors, with zero exceptional coefficients,
generate all the relations in the numbered Picard presentation. -/
theorem ker_numberedInternalBlowupPicardMap :
    ker (numberedInternalBlowupPicardMap b hΦ e o ρ c) =
      Submodule.span ℤ (Set.range fun a : Fin 2 ↦
        Sum.elim (fun j ↦ b.repr (e j).primitiveGenerator a) 0) := by
  have hinj : Function.Injective (T).picardHom := by
    intro x y h
    apply (internalBlowupPicardMarking b (e ∘ ρ ∘ o) c hΦ).injective
    simpa only [internalBlowupPicardMarking_apply] using h
  rw [numberedInternalBlowupPicardMap, ker_comp_of_ker_eq_bot _ (ker_eq_bot_of_injective hinj),
    ker_numberedPicardCoordinates, ← Submodule.map_top, ← b.dualBasis.span_eq,
    Submodule.map_span, ← Set.range_comp]
  simp only [Function.comp_def, numberedCharacterDivisor_apply, Basis.dualBasis_apply]

open LineBundleClass Scheme.IdealSheafData in
/-- The strict boundary class is the ray divisor minus the total exceptional
classes at the centers assigned to that ray. -/
theorem numberedInternalBlowupPicardMap_strictBoundary (j : ZMod m) :
    let : IsIntegral Y := isIntegral_internalBlowupTower b (e ∘ ρ ∘ o) c hΦ
    let : IsNoetherian Y := (T).isNoetherian
    let f := (T).toBase ≫ Φ.algebraicRealizationStructureMap
    let : SmoothOfRelativeDimension 2 f :=
      smoothOfRelativeDimension_internalBlowupTower b (e ∘ ρ ∘ o) c hΦ
    let := f.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    numberedInternalBlowupPicardMap b hΦ e o ρ c
        (numberedStrictBoundaryCoefficients ρ j) =
      Additive.ofMul (primeDivisorClass
        ⟨_, (mem_boundaryPrimes.mp
          (internalBlowupBoundaryPrimeEquiv hΦ b (e ∘ ρ ∘ o) c (e j)).property).2⟩) := by
  intro _ _ f _ _
  classical
  rw [numberedInternalBlowupPicardMap_apply, internalBlowupPicardMarking_apply,
    ← picardHom_markedBoundaryMap_single_eq_primeDivisorClass]
  congr 1
  have hj : (Pi.single j (1 : ℤ) ∘ e.symm) = Pi.single (e j) 1 := by
    rw [Pi.single_comp_equiv, Equiv.symm_symm]
  simp only [numberedStrictBoundaryCoefficients, Sum.elim_inl, Sum.elim_inr,
    markedBoundaryMap_apply, Prod.mk.injEq]
  refine ⟨congrArg (Φ.rayDivisorToPicard hΦ) hj, ?_⟩
  simp only [Pi.single_apply, Function.comp_apply, Equiv.apply_eq_iff_eq]
  funext k
  split_ifs <;> simp

section Intersection

variable [NeZero m] [Fintype ι]
  (hc : Φ.IsComplete)
  (he : ∀ j, b.detDualEquiv (e j).primitiveGenerator (e (j + 1)).primitiveGenerator = 1 ∧
    ∃ σ : Φ.cones, (e j).toCone ≤ σ ∧ (e (j + 1)).toCone ≤ σ)

local notation "B" => Chow.intersectionBilinForm ℂ Y
local notation "F" => numberedInternalBlowupPicardMap b hΦ e o ρ c
local notation "G" =>
  numberedInternalBlowupGram ι (fun j ↦ Basis.repr b (Ray.primitiveGenerator (e j)))

include he in
open Classical in
/-- In the numbered coordinates the intersection pairing has the cyclic toric
wall matrix on the rays and an orthogonal negative identity on the centers. -/
theorem numberedInternalBlowupPicardMap_intersection :
    let : (Z).IsProjectiveOver ℂ := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
    let : (Y).Over S := ⟨(T).toBase ≫ Z ↘ S⟩
    let : (Y).IsProjectiveOver ℂ := (T).isProjectiveOver ℂ
    let : IsIntegral Y := isIntegral_internalBlowupTower b (e ∘ ρ ∘ o) c hΦ
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := Eq.mp
      (congrArg (fun f ↦ SmoothOfRelativeDimension 2 ((T).toBase ≫ f))
        (algebraicRealization_over Φ).symm)
      (smoothOfRelativeDimension_internalBlowupTower b (e ∘ ρ ∘ o) c hΦ)
    (B).compl₁₂ F F = Matrix.toBilin' G := by
  intro _ _ _ _ _
  have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  let : SmoothOfRelativeDimension 2 (Z ↘ S) := by
    rw [algebraicRealization_over, ← hdim]
    exact Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  have hmark (x y : Pic Z × (Fin n → ℤ)) := classIntersectionNumber_picardMarking ℂ
    (isClosedPointTower_internalBlowupTower b (e ∘ ρ ∘ o) c) x y
  simp only [picardMarking_apply] at hmark
  apply LinearMap.BilinForm.ext_basis (Pi.basisFun ℤ (ZMod m ⊕ ι))
  intro a d
  simp only [Pi.basisFun_apply, compl₁₂_apply, Matrix.toBilin'_single,
    numberedInternalBlowupGram_def,
    numberedInternalBlowupPicardMap_apply, internalBlowupPicardMarking_apply,
    Chow.intersectionBilinForm_apply, hmark]
  rcases a with j | a <;> rcases d with k | d <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Matrix.zero_apply, Matrix.diagonal_apply]
  · have hp := he (j - 1)
    rw [sub_add_cancel] at hp
    rw [← Chow.intersectionBilinForm_apply]
    simp only [Pi.single_apply, Sum.inl.injEq, reduceCtorEq, ite_false,
      mul_zero, Finset.sum_const_zero, sub_zero]
    have hpair := Φ.intersectionBilinForm_rayDivisorToPicard_single hΦ b hc
      (Pi.single k 1 ∘ e.symm) hp (he j)
    have hs := Pi.single_comp_equiv e.symm j (1 : ℤ)
    rw [Equiv.symm_symm] at hs
    rw [← hs] at hpair
    simp only [Function.comp_def, Pi.single_apply, Equiv.symm_apply_apply] at hpair
    rw [hpair, congrFun (rayBoundarySelfIntersection_eq_of_positiveRayCoordinates hΦ hc b e he) j]
    simp only [eq_comm (a := j), eq_comm (a := j - 1), eq_comm (a := j + 1)]
    split_ifs <;> ring
  · simp only [Pi.single_apply, reduceCtorEq, ite_false, zero_mul, Finset.sum_const_zero, sub_zero]
    rw [← Pi.zero_def, map_zero, toMul_zero, Chow.classIntersectionNumber_one_right]
  · simp only [Pi.single_apply, reduceCtorEq, ite_false, mul_zero, Finset.sum_const_zero, sub_zero]
    rw [← Pi.zero_def, map_zero, toMul_zero, Chow.classIntersectionNumber_one_left]
  · simp only [Pi.single_apply, reduceCtorEq, ite_false, Sum.inr.injEq]
    rw [← Pi.zero_def, map_zero, toMul_zero, Chow.classIntersectionNumber_one_left, zero_sub]
    have ho (x : Fin n) (y : ι) : o x = y ↔ x = o.symm y := o.eq_symm_apply.symm
    simp only [ho, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, Equiv.apply_eq_iff_eq]
    by_cases h : a = d <;> simp [h]

include he in
open Classical in
/-- A quotient whose relations are the coordinate characters and whose form is
induced by the numbered intersection matrix is isometric to the Picard lattice.
The isometry evaluates each representative by the geometric divisor map. -/
theorem numberedInternalBlowupPicardIsometry
    {R : Submodule ℤ A} (Q : LinearMap.BilinForm ℤ (A ⧸ R))
    (hR : R = Submodule.span ℤ (Set.range fun a : Fin 2 ↦
      Sum.elim (fun j ↦ b.repr (e j).primitiveGenerator a) 0))
    (hQ : Q.compl₁₂ R.mkQ R.mkQ = Matrix.toBilin' G) :
    let : (Z).IsProjectiveOver ℂ := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
    let : (Y).Over S := ⟨(T).toBase ≫ Z ↘ S⟩
    let : (Y).IsProjectiveOver ℂ := (T).isProjectiveOver ℂ
    let : IsIntegral Y := isIntegral_internalBlowupTower b (e ∘ ρ ∘ o) c hΦ
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := Eq.mp
      (congrArg (fun f ↦ SmoothOfRelativeDimension 2 ((T).toBase ≫ f))
        (algebraicRealization_over Φ).symm)
      (smoothOfRelativeDimension_internalBlowupTower b (e ∘ ρ ∘ o) c hΦ)
    ∃ g : Q.IsometryEquiv B, ∀ x : A, g (R.mkQ x) = F x := by
  intro _ _ _ _ _
  let g := (Submodule.quotEquivOfEq R (F).ker
    (hR.trans (ker_numberedInternalBlowupPicardMap b hΦ e o ρ c).symm)).trans
      ((F).quotKerEquivOfSurjective (numberedInternalBlowupPicardMap_surjective b hΦ e o ρ c))
  have hg (x : A) : g (R.mkQ x) = F x := by
    simp [g, Submodule.mkQ_apply]
  have hiso (x y : A ⧸ R) : B (g x) (g y) = Q x y := by
    obtain ⟨x, rfl⟩ := R.mkQ_surjective x
    obtain ⟨y, rfl⟩ := R.mkQ_surjective y
    rw [hg, hg]
    have h := (numberedInternalBlowupPicardMap_intersection b hΦ e o ρ c hc he).trans hQ.symm
    simpa only [compl₁₂_apply] using congr($h x y)
  exact ⟨⟨g, hiso⟩, hg⟩

end Intersection

end TauCeti.Toric.Fan
