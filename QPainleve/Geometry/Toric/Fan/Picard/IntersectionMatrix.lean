/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Boundary.Degree
public import QPainleve.Geometry.Toric.Fan.Picard.StrictTransform
public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection

import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
import QPainleve.Geometry.Toric.BaseChange.FiniteType
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
    (if j = l then
      toricBoundarySelfIntersection ray j -
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
      else 0) + (if j - 1 = l then 1 else 0) + (if j + 1 = l then 1 else 0) := by
  simp only [internalBlowupBoundaryIntersectionMatrix, Matrix.of_apply,
    toricBoundarySelfIntersection_apply]

/-- A matrix entry is the degree on the row ray of the strict boundary class of the
column ray. Its exceptional coefficients are minus one at centers on the column ray. -/
private theorem internalBlowupBoundaryIntersectionMatrix_apply_eq_degree {m r : ℕ} [NeZero m]
    (ray : ZMod m → Fin 2 → ℤ) (centerRay : Fin r → ZMod m) (a d : Fin m) :
    internalBlowupBoundaryIntersectionMatrix ray centerRay a d =
      let e := ZMod.finEquiv m
      let l := e d
      strictBoundaryRayDegree (toricBoundarySelfIntersection ray) (Pi.single l 1)
        (e.symm ∘ centerRay) (fun k ↦ -((Pi.single l 1 : ZMod m → ℤ) (centerRay k))) a := by
  let e := ZMod.finEquiv m
  let j := e a
  let l := e d
  have hsum : (∑ k ∈ Finset.univ.filter (fun k ↦ centerRay k = j),
      -((Pi.single l 1 : ZMod m → ℤ) (centerRay k))) =
      (Finset.univ.filter (fun k ↦ centerRay k = j)).card •
        (-((Pi.single l 1 : ZMod m → ℤ) j)) := by
    rw [← Finset.sum_const]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [(Finset.mem_filter.mp hk).2]
  simp only [internalBlowupBoundaryIntersectionMatrix_apply,
    strictBoundaryRayDegree_apply, Function.comp_apply, RingEquiv.symm_apply_eq]
  rw [hsum]
  simp only [toricBoundarySelfIntersection_apply, Pi.single_apply, nsmul_eq_mul, j, l, e]
  by_cases h : ZMod.finEquiv m a = ZMod.finEquiv m d <;>
    simp only [h, ite_true, ite_false, mul_one, mul_zero, neg_zero] <;> ring

end QPainleve

namespace TauCeti.Toric.Fan

universe u

variable (K : Type u) [Field K] [IsAlgClosed K]

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} {m r : ℕ}

local notation "S" => Spec (CommRingCat.of K)

section Geometry

variable [NeZero m] (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (e : ZMod m ≃ Φ.Ray) (s : Fin r → Φ.Ray) (c : Fin r → Kˣ)

local notation "Base" => (Φ.finiteFanScheme K)
local notation "P" => internalBlowupTower K (h₀ := Fan.IsComplete.nonempty_cones hc) b s c
local notation "Y" => Sigma.fst P
local notation "T" => WithBoundary.toTower (Sigma.snd P)
local notation "hT" => isClosedPointTower_internalBlowupTower K
  (h₀ := Fan.IsComplete.nonempty_cones hc) b s c
local notation "f" => (Base ↘ S)
local notation "J" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd P))
local notation "prime[" ρ "]" => boundaryPrimeEmbedding J
  (internalBlowupBoundaryPrimeEquiv K hΦ b s c ρ)
local notation "A" => internalBlowupBoundaryIntersectionMatrix
  (fun j ↦ b.repr (Ray.primitiveGenerator (e j))) (e.symm ∘ s)
local notation "C[" j "]" => markedBoundaryMap K hΦ s (Pi.single (e j) 1)

open Classical in
private theorem classIntersectionNumber_markedBoundaryMap_single_single
    (he : ∀ j : ZMod m,
      b.detDualEquiv (e j).primitiveGenerator (e (j + 1)).primitiveGenerator = 1 ∧
        ∃ σ : Φ.cones, (e j).toCone ≤ σ ∧ (e (j + 1)).toCone ≤ σ) (a d : Fin m) :
    letI : Nonempty Φ.cones := hc.nonempty_cones
    letI : Scheme.Over Y S := ⟨BlowupTower.toBase T ≫ f⟩
    classIntersectionNumber K Y (BlowupTower.picardHom T C[ZMod.finEquiv m a]).toMul
      (BlowupTower.picardHom T C[ZMod.finEquiv m d]).toMul = A a d := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Scheme.Over Y S := ⟨BlowupTower.toBase T ≫ f⟩
  let : Scheme.IsProjectiveOver (X := Base) K :=
    Φ.isProjectiveOver_finiteFanScheme_of_isComplete K hΦ hc b
  let : IsIntegral Base := inferInstance
  let : IsNoetherian Base := isNoetherian_of_finiteType f
  let : SmoothOfRelativeDimension 2 f := by
    have hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
    rw [finiteFanScheme_over K, ← hdim]
    exact Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ
  let l := ZMod.finEquiv m d
  have hself := Φ.rayBoundarySelfIntersection_eq_of_positiveRayCoordinates K hΦ hc b e he
  have hpair := Φ.markedBoundaryMap_single_pairing_eq_strictBoundaryRayDegree K
    hΦ hc b e s ((ZMod.finEquiv m).symm ∘ e.symm ∘ s) (by simp) he
    (Pi.single l 1) (fun k ↦ -((Pi.single l 1 : ZMod m → ℤ) (e.symm (s k)))) a
  rw [← picardMarking_apply T (hT) f, ← picardMarking_apply T (hT) f,
    classIntersectionNumber_picardMarking K (hT)]
  have hsingle : Pi.single (e l) (1 : ℤ) = Pi.single l 1 ∘ e.symm := by
    rw [Pi.single_comp_equiv, Equiv.symm_symm]
  rw [internalBlowupBoundaryIntersectionMatrix_apply_eq_degree]
  simp only [markedBoundaryMap_apply]
  rw [hsingle]
  simpa only [LinearMap.BilinForm.prod_apply, markedBoundaryMap_apply,
    LinearMap.neg_apply, dotProductBilin_apply_apply, dotProduct, ← sub_eq_add_neg,
    intersectionBilinForm_apply, Function.comp_apply, hself] using hpair

/-- The executable integer matrix is the intersection matrix of the actual numbered
strict boundary primes of the ordered toric blowup. The chosen center parameters
may coincide, including on the same ray. -/
theorem primeIntersectionMatrix_internalBlowupBoundaryPrime_eq
    (he : ∀ j : ZMod m,
      b.detDualEquiv (e j).primitiveGenerator (e (j + 1)).primitiveGenerator = 1 ∧
        ∃ σ : Φ.cones, (e j).toCone ≤ σ ∧ (e (j + 1)).toCone ≤ σ) :
    letI : Nonempty Φ.cones := hc.nonempty_cones
    letI : Scheme.Over Y S := ⟨BlowupTower.toBase T ≫ f⟩
    letI : IsIntegral Y := isIntegral_internalBlowupTower K (h₀ := hc.nonempty_cones) b s c hΦ
    letI : IsNoetherian Y := BlowupTower.isNoetherian T
    letI : SmoothOfRelativeDimension 2 (BlowupTower.toBase T ≫ f) :=
      smoothOfRelativeDimension_internalBlowupTower K (h₀ := hc.nonempty_cones) b s c hΦ
    letI := (BlowupTower.toBase T ≫ f)
      |>.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    primeIntersectionMatrix K (fun a : Fin m ↦ prime[e (ZMod.finEquiv m a)]) = A := by
  classical
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : IsIntegral Y := isIntegral_internalBlowupTower K b s c hΦ
  let : IsNoetherian Y := BlowupTower.isNoetherian T
  let : SmoothOfRelativeDimension 2 (BlowupTower.toBase T ≫ f) :=
    smoothOfRelativeDimension_internalBlowupTower K b s c hΦ
  let := (BlowupTower.toBase T ≫ f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have h (j : ZMod m) : (BlowupTower.picardHom T C[j]).toMul =
      LineBundleClass.primeDivisorClass prime[e j] := by
    have hmark := congrArg Additive.toMul
      (picardHom_markedBoundaryMap_single_eq_primeDivisorClass K hΦ b s c (e j))
    rw [hmark, toMul_ofMul]
    congr 1
    exact Subtype.ext (coe_boundaryPrimeEmbedding _ _).symm
  ext a d
  rw [primeIntersectionMatrix_apply, ← h, ← h]
  exact classIntersectionNumber_markedBoundaryMap_single_single K b hΦ hc e s c he a d

end Geometry

end TauCeti.Toric.Fan
