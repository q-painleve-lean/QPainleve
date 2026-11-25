/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.StrictTransform
public import TauCeti.AlgebraicGeometry.Chow.SurfaceIntersection.Basic

import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
import QPainleve.Geometry.Toric.Fan.Boundary.SelfIntersection
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective

/-!
# Boundary intersection matrices of internal toric blowups

The strict boundary of an ordered internal blowup tower has one prime for each ray of
the original complete fan. In positive cyclic order the two adjacent entries in each
row are one. The diagonal entry is the negative determinant of the neighboring ray
generators, decreased by the number of centers on that ray. An infinitely near center
contributes to the same count as any other center on the given ray.

The calculation uses the toric wall relation of Fulton, *Introduction to Toric
Varieties*, §5.1, and the orthogonal Picard marking of the blowup tower in total
transform exceptional classes. Its integer matrix can be used to recover the
multiplicities in the pullback of a nef square-zero boundary.
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Chow

namespace QPainleve

/-- The strict boundary intersection matrix from positively ordered primitive ray
coordinates and the ray index of every internal center. The `Fin` indices use the
same order as the cyclic ray labels. -/
def internalBlowupBoundaryIntersectionMatrix {m r : ℕ} [NeZero m]
    (ray : ZMod m → Fin 2 → ℤ) (centerRay : Fin r → ZMod m) :
    Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun a d ↦
    let j := ZMod.finEquiv m a
    let l := ZMod.finEquiv m d
    let u := ray (j - 1)
    let v := ray (j + 1)
    (if j = l then
      -Matrix.det !![u 0, u 1; v 0, v 1] -
        (Finset.univ.filter (fun k ↦ centerRay k = j)).card
    else 0) + (if j - 1 = l then 1 else 0) + (if j + 1 = l then 1 else 0)

/-- The diagonal correction counts each label assigned to the given ray. The two
neighbor terms use the cyclic predecessor and successor. -/
@[simp]
theorem internalBlowupBoundaryIntersectionMatrix_apply {m r : ℕ} [NeZero m]
    (ray : ZMod m → Fin 2 → ℤ) (centerRay : Fin r → ZMod m) (a d : Fin m) :
    internalBlowupBoundaryIntersectionMatrix ray centerRay a d =
      let j := ZMod.finEquiv m a
      let l := ZMod.finEquiv m d
      let u := ray (j - 1)
      let v := ray (j + 1)
      (if j = l then
        -Matrix.det !![u 0, u 1; v 0, v 1] -
          (Finset.univ.filter (fun k ↦ centerRay k = j)).card
      else 0) + (if j - 1 = l then 1 else 0) + (if j + 1 = l then 1 else 0) :=
  (rfl)

end QPainleve

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} {m r : ℕ}

local notation "S" => Spec (CommRingCat.of ℂ)

open Classical in
private theorem sum_markedBoundaryMap_single_mul [Nonempty Φ.cones]
    (hΦ : Φ.IsRegular) (e : ZMod m ≃ Φ.Ray) (s : Fin r → Φ.Ray) (j l : ZMod m) :
    (∑ k : Fin r, (markedBoundaryMap hΦ s (Pi.single (e j) 1)).2 k *
      (markedBoundaryMap hΦ s (Pi.single (e l) 1)).2 k) =
      if j = l then ((Finset.univ.filter (fun k ↦ e.symm (s k) = j)).card : ℤ) else 0 := by
  simp only [markedBoundaryMap_apply, Pi.single_apply, neg_mul_neg]
  by_cases h : j = l
  · subst l
    rw [ite_eq_left rfl, ← Finset.sum_boole]
    exact Finset.sum_congr rfl fun k _ ↦ by
      by_cases hk : e.symm (s k) = j
      · simp [e.symm_apply_eq.mp hk]
      · simp [hk, mt e.symm_apply_eq.mpr hk]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : s k = e j
    · simp [hk, h]
    · simp [hk]

section Geometry

variable [NeZero m] (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (e : ZMod m ≃ Φ.Ray) (s : Fin r → Φ.Ray) (c : Fin r → ℂˣ)

local notation "Base" => Φ.algebraicRealization
local notation "P" => internalBlowupTower (h₀ := Fan.IsComplete.nonempty_cones hc) b s c
local notation "Y" => Sigma.fst P
local notation "T" => WithBoundary.toTower (Sigma.snd P)
local notation "hT" => isClosedPointTower_internalBlowupTower
  (h₀ := Fan.IsComplete.nonempty_cones hc) b s c
local notation "f" => (Base ↘ S)
local notation "J" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd P))
local notation "prime[" ρ "]" => boundaryPrimeEmbedding J
  (internalBlowupBoundaryPrimeEquiv hΦ b s c ρ)
local notation "A" => internalBlowupBoundaryIntersectionMatrix
  (fun j ↦ b.repr (Ray.primitiveGenerator (e j))) (e.symm ∘ s)
local notation "C[" j "]" => markedBoundaryMap hΦ s (Pi.single (e j) 1)

open Classical in
private theorem classIntersectionNumber_markedBoundaryMap_single_single
    (he : ∀ j : ZMod m,
      b.detDualEquiv (e j).primitiveGenerator (e (j + 1)).primitiveGenerator = 1 ∧
        ∃ σ : Φ.cones, (e j).toCone ≤ σ ∧ (e (j + 1)).toCone ≤ σ) (a d : Fin m) :
    letI : Nonempty Φ.cones := hc.nonempty_cones
    letI : Scheme.Over Y S := ⟨BlowupTower.toBase T ≫ f⟩
    classIntersectionNumber ℂ Y (BlowupTower.picardHom T C[ZMod.finEquiv m a]).toMul
      (BlowupTower.picardHom T C[ZMod.finEquiv m d]).toMul = A a d := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Scheme.Over Y S := ⟨BlowupTower.toBase T ≫ f⟩
  let : Scheme.IsProjectiveOver (X := Base) ℂ :=
    Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
  let : IsIntegral Base := inferInstance
  let : IsNoetherian Base := isNoetherian_of_finiteType f
  let : SmoothOfRelativeDimension 2 f := by
    have hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
    rw [algebraicRealization_over, ← hdim]
    exact Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let j := ZMod.finEquiv m a
  let l := ZMod.finEquiv m d
  have hp := he (j - 1)
  rw [sub_add_cancel] at hp
  have hn := he j
  have hbase := Φ.intersectionBilinForm_rayDivisorToPicard_single hΦ b hc
    (Pi.single (e l) 1) hp hn
  simp only [intersectionBilinForm_apply, Pi.single_apply, e.injective.eq_iff]
    at hbase
  have hdet := rayBoundarySelfIntersection_eq_neg_det_of_neighbors b hΦ hc hp hn
  rw [Basis.detDualEquiv_apply, Basis.det_apply] at hdet
  simp only [Basis.toMatrix_apply, Matrix.det_fin_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at hdet
  rw [← picardMarking_apply T (hT) f, ← picardMarking_apply T (hT) f,
    classIntersectionNumber_picardMarking ℂ (hT),
    sum_markedBoundaryMap_single_mul hΦ e s,
    internalBlowupBoundaryIntersectionMatrix_apply]
  dsimp only [j, l] at hbase hdet
  simp only [markedBoundaryMap_apply, hbase, hdet, Function.comp_apply, Matrix.det_fin_two_of]
  by_cases h : ZMod.finEquiv m a = ZMod.finEquiv m d <;>
    simp only [h, ite_true, ite_false, mul_one, mul_zero, sub_zero] <;> ring

/-- The executable integer matrix is the intersection matrix of the actual numbered
strict boundary primes of the ordered toric blowup. The chosen center parameters
may coincide, including on the same ray. -/
theorem classIntersectionNumber_internalBlowupBoundaryPrime_eq_matrix
    (he : ∀ j : ZMod m,
      b.detDualEquiv (e j).primitiveGenerator (e (j + 1)).primitiveGenerator = 1 ∧
        ∃ σ : Φ.cones, (e j).toCone ≤ σ ∧ (e (j + 1)).toCone ≤ σ) (a d : Fin m) :
    letI : Nonempty Φ.cones := hc.nonempty_cones
    letI : Scheme.Over Y S := ⟨BlowupTower.toBase T ≫ f⟩
    letI : IsIntegral Y := isIntegral_internalBlowupTower (h₀ := hc.nonempty_cones) b s c hΦ
    letI : IsNoetherian Y := BlowupTower.isNoetherian T
    letI : SmoothOfRelativeDimension 2 (BlowupTower.toBase T ≫ f) :=
      smoothOfRelativeDimension_internalBlowupTower (h₀ := hc.nonempty_cones) b s c hΦ
    letI := (BlowupTower.toBase T ≫ f)
      |>.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    classIntersectionNumber ℂ Y
      (LineBundleClass.primeDivisorClass prime[e (ZMod.finEquiv m a)])
      (LineBundleClass.primeDivisorClass prime[e (ZMod.finEquiv m d)]) = A a d := by
  classical
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : IsIntegral Y := isIntegral_internalBlowupTower b s c hΦ
  let : IsNoetherian Y := BlowupTower.isNoetherian T
  let : SmoothOfRelativeDimension 2 (BlowupTower.toBase T ≫ f) :=
    smoothOfRelativeDimension_internalBlowupTower b s c hΦ
  let := (BlowupTower.toBase T ≫ f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have h (j : ZMod m) : (BlowupTower.picardHom T C[j]).toMul =
      LineBundleClass.primeDivisorClass prime[e j] := by
    have hmark := congrArg Additive.toMul
      (picardHom_markedBoundaryMap_single_eq_primeDivisorClass hΦ b s c (e j))
    rw [hmark, toMul_ofMul]
    congr 1
    exact Subtype.ext (coe_boundaryPrimeEmbedding _ _).symm
  rw [← h, ← h]
  exact classIntersectionNumber_markedBoundaryMap_single_single b hΦ hc e s c he a d

end Geometry

end TauCeti.Toric.Fan
