/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Boundary

import QPainleve.AlgebraicGeometry.Chow.Ample
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.Matrix.Dual

/-!
# Surviving rays from Picard pullback

A ray of an ordered toric presentation is contracted exactly when its strict
boundary class lies in the marked exceptional summand. The pullback lattice in the
same coordinates thus determines which rays survive a nodal contraction.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Additive TauCeti LineBundleClass Scheme.IdealSheafData LinearMap.BilinForm

namespace TauCeti.Toric.Fan

universe u

variable (k : Type u) [Field k] [IsAlgClosed k]
  {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "S" => Spec (CommRingCat.of k)
local notation "Z" => (Φ.finiteFanScheme k)
local notation "mark" c:arg => internalBlowupPicardMarking k b s c hΦ
local notation "hπ" c:arg => isClosedPointTower_internalBlowupTower k b s c

variable [(Φ.finiteFanScheme k).IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (Φ.finiteFanScheme k ↘ Spec (.of k))]
  {X Y : Scheme} [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] {D : X.IdealSheafData}
  {l : ℕ} {T : BlowupTower X l Y}
  (c : Fin n → kˣ)
  (hT : IsNodalBoundaryTower D (X ↘ Spec (.of k)) (𝟙 X) T)
  (e : (internalBlowupTower k b s c).1 ≅ Y)
  (he : e.hom ≫ T.toBase ≫ (X ↘ Spec (.of k)) =
    (internalBlowupTower k b s c).2.toTower.toBase ≫ (Φ.finiteFanScheme k ↘ Spec (.of k)))
  (hD : (D.comap (e.hom ≫ T.toBase)).support =
    (internalBlowupTower k b s c).2.boundaryι.ker.support)

local notation "p" => (Iso.hom e ≫ toBase T)
local notation "P" => markedExceptionalSpan k (hπ c) T e
local notation "F" => LinearMap.BilinForm.prod (Chow.intersectionBilinForm k Z)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin n → ℤ)))

include b hT he hD in
/-- A strict ray class is in the exceptional summand exactly when the ray's prime
divisor is contracted. A surviving prime has nonzero class by ample positivity. -/
theorem markedBoundaryMap_single_mem_markedExceptionalSpan_iff (ρ : Φ.Ray) :
    let : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ S)
    markedBoundaryMap k hΦ s (Pi.single ρ 1) ∈ P ↔
      p (internalBlowupBoundaryPrimeEquiv k hΦ b s c ρ).val ∉ D.boundaryPrimes := by
  classical
  intro _
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let : IsModification p := isModification_orderedContraction k hΦ b s c hT e
  rw [← mem_range_contractedBoundaryRayEmbedding_iff k hΦ b s c p hD]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro h ⟨x, rfl⟩
    let μ := contractedPicardMarking k hT.isClosedPointTower (hπ c) e he
    let z := D.boundaryPrimeEmbedding x
    have hproj := contractedPicardMarking_symm_boundaryPrime k hΦ b s c hT e he hD x
    dsimp only at hproj
    have hz' : z = ⟨x.val, (mem_boundaryPrimes.mp x.property).2⟩ :=
      Subtype.ext (coe_boundaryPrimeEmbedding D x)
    have hzero : μ.symm (Additive.ofMul (primeDivisorClass z)) = 0 := by
      rw [hz']
      exact hproj.trans (Submodule.projectionOnto_apply_of_mem_right
        (isCompl_orthogonal_markedExceptionalSpan k hT.isClosedPointTower (hπ c) e he) h)
    have hz : Additive.ofMul (primeDivisorClass z) = 0 :=
      μ.symm.injective (hzero.trans μ.symm.map_zero.symm)
    obtain ⟨H, hH⟩ := X.exists_isAmple_of_isProjectiveOver k
    have hpos : 0 < Chow.intersectionBilinForm k X (Additive.ofMul H)
        (Additive.ofMul (primeDivisorClass z)) := by
      simpa only [Chow.intersectionBilinForm_apply, toMul_ofMul] using
        (Chow.classIntersectionNumber_primeDivisorClass_pos_of_isAmple k
          (topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)) hH z)
    rw [hz, LinearMap.map_zero] at hpos
    exact (lt_irrefl 0) hpos
  · rw [markedExceptionalSpan_eq_span_compl_survivingRays k hΦ b s c hT e hD]
    exact Submodule.subset_span ⟨ρ, h, rfl⟩

include hT he in
/-- The range of the pullback from a contracted surface in the ordered toric marking
is the orthogonal complement of the exceptional summand. -/
theorem range_marked_pullback_eq_orthogonal :
    let : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ S)
    Set.range (fun L : LineBundleClass X ↦ (mark c).symm (Additive.ofMul (pullback p L))) =
      ((F).orthogonal P : Set _) := by
  intro _
  let μ := contractedPicardMarking k hT.isClosedPointTower (hπ c) e he
  have hcoords (L : LineBundleClass X) :
      (mark c).symm (Additive.ofMul (pullback p L)) = (μ.symm (Additive.ofMul L)).val := by
    apply (mark c).injective
    rw [LinearEquiv.apply_symm_apply, internalBlowupPicardMarking_apply]
    exact (picardHom_contractedPicardMarking_symm k hT.isClosedPointTower (hπ c) e he _).symm
  ext a
  constructor
  · rintro ⟨L, rfl⟩
    simpa only [hcoords, SetLike.mem_coe] using (μ.symm (Additive.ofMul L)).property
  · intro ha
    refine ⟨(μ ⟨a, ha⟩).toMul, ?_⟩
    simpa only [hcoords, ofMul_toMul] using
      congrArg Subtype.val (LinearMap.BilinForm.IsometryEquiv.symm_apply_apply μ ⟨a, ha⟩)

variable {X' Y' : Scheme} [X'.Over (Spec (.of k))] [X'.IsProjectiveOver k] [IsIntegral X']
  [SmoothOfRelativeDimension 2 (X' ↘ Spec (.of k))] {D' : X'.IdealSheafData}
  {l' : ℕ} {T' : BlowupTower X' l' Y'}
  (d : Fin n → kˣ)
  (hT' : IsNodalBoundaryTower D' (X' ↘ Spec (.of k)) (𝟙 X') T')
  (e' : (internalBlowupTower k b s d).1 ≅ Y')
  (he' : e'.hom ≫ T'.toBase ≫ (X' ↘ Spec (.of k)) =
    (internalBlowupTower k b s d).2.toTower.toBase ≫ (Φ.finiteFanScheme k ↘ Spec (.of k)))
  (hD' : (D'.comap (e'.hom ≫ T'.toBase)).support =
    (internalBlowupTower k b s d).2.boundaryι.ker.support)

local notation "p'" => (Iso.hom e' ≫ toBase T')
local notation "P'" => markedExceptionalSpan k (hπ d) T' e'

include hT he hT' he' in
/-- The marked exceptional span is determined by the image of Picard pullback
in the common toric coordinates. -/
theorem markedExceptionalSpan_eq_of_matching_picard_markings
    (hsep : (F).SeparatingRight)
    (G : LineBundleClass X' → LineBundleClass X) (hG : Function.Surjective G)
    (hPic : ∀ L : LineBundleClass X', (mark c).symm (Additive.ofMul (pullback p (G L))) =
      (mark d).symm (Additive.ofMul (pullback p' L))) :
    P = P' := by
  let : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ S)
  have hsymm : (F).IsSymm := by
    refine isSymm_prod_iff.mpr
      ⟨⟨fun a b ↦ ?_⟩, (TauCeti.isSymm_dotProductBilin (R := ℤ) (ι := Fin n)).neg⟩
    simp only [Chow.intersectionBilinForm_apply, Chow.classIntersectionNumber_comm]
  have hc : IsCompl P ((F).orthogonal P) :=
    (isCompl_orthogonal_markedExceptionalSpan k hT.isClosedPointTower (hπ c) e he).symm
  have hd : IsCompl P' ((F).orthogonal P') :=
    (isCompl_orthogonal_markedExceptionalSpan k hT'.isClosedPointTower (hπ d) e' he').symm
  have horth : (F).orthogonal P = (F).orthogonal P' := by
    apply SetLike.coe_injective
    rw [← range_marked_pullback_eq_orthogonal k hΦ b s c hT e he,
      ← range_marked_pullback_eq_orthogonal k hΦ b s d hT' e' he']
    exact (hG.range_comp _).symm.trans (congrArg Set.range (funext hPic))
  rw [← (F).orthogonal_orthogonal_of_isCompl hsymm.isRefl hsep P hc,
    horth, (F).orthogonal_orthogonal_of_isCompl hsymm.isRefl hsep P' hd]

include hT he hD hT' he' hD' in
/-- Surjective identification of the marked pullbacks of two nodal contractions
of the same ordered toric presentation identifies exactly the rays that survive. -/
theorem mem_boundaryPrimes_iff_of_matching_picard_markings
    (hsep : (F).SeparatingRight)
    (G : LineBundleClass X' → LineBundleClass X) (hG : Function.Surjective G)
    (hPic : ∀ L : LineBundleClass X', (mark c).symm (Additive.ofMul (pullback p (G L))) =
      (mark d).symm (Additive.ofMul (pullback p' L)))
    (ρ : Φ.Ray) :
    p (internalBlowupBoundaryPrimeEquiv k hΦ b s c ρ).val ∈ D.boundaryPrimes ↔
      p' (internalBlowupBoundaryPrimeEquiv k hΦ b s d ρ).val ∈ D'.boundaryPrimes := by
  let : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ S)
  have hspan := markedExceptionalSpan_eq_of_matching_picard_markings k hΦ b s
    c hT e he d hT' e' he' hsep G hG hPic
  have hρ := markedBoundaryMap_single_mem_markedExceptionalSpan_iff k hΦ b s c hT e he hD ρ
  have hρ' := markedBoundaryMap_single_mem_markedExceptionalSpan_iff k hΦ b s d hT' e' he' hD' ρ
  dsimp only at hρ hρ'
  exact not_iff_not.mp (hρ.symm.trans (hspan ▸ hρ'))

include hT hT' he he' hD hD' in
/-- The marked pullback coordinates of a surviving prime depend only on its ray and
the exceptional span. -/
theorem marked_pullback_prime_eq_of_contractedBoundaryRayEmbedding_eq
    (hspan : P = P') (x : D.boundaryPrimes) (y : D'.boundaryPrimes)
    (hxy :
      let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
      let : IsNoetherian X' := isNoetherian_of_finiteType (X' ↘ S)
      let : IsNormalScheme X := (X ↘ S).isNormalScheme_of_smoothOfRelativeDimension_two
      let : IsNormalScheme X' := (X' ↘ S).isNormalScheme_of_smoothOfRelativeDimension_two
      letI := isModification_orderedContraction k hΦ b s c hT e
      letI := isModification_orderedContraction k hΦ b s d hT' e'
      contractedBoundaryRayEmbedding k hΦ b s c p hD x =
        contractedBoundaryRayEmbedding k hΦ b s d p' hD' y) :
    let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
    let : IsNoetherian X' := isNoetherian_of_finiteType (X' ↘ S)
    let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let := (X' ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (mark c).symm (Additive.ofMul (pullback p (primeDivisorClass
      ⟨x.val, (mem_boundaryPrimes.mp x.property).2⟩))) =
    (mark d).symm (Additive.ofMul (pullback p' (primeDivisorClass
      ⟨y.val, (mem_boundaryPrimes.mp y.property).2⟩))) := by
  classical
  intro _ _ _ _
  let : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ S)
  let μ := contractedPicardMarking k hT.isClosedPointTower (hπ c) e he
  let ν := contractedPicardMarking k hT'.isClosedPointTower (hπ d) e' he'
  have hc (a : Additive (LineBundleClass X)) :
      (mark c).symm (Additive.ofMul (pullback p a.toMul)) = (μ.symm a).val := by
    apply (mark c).injective
    rw [LinearEquiv.apply_symm_apply, internalBlowupPicardMarking_apply]
    exact (picardHom_contractedPicardMarking_symm k hT.isClosedPointTower (hπ c) e he a).symm
  have hd (a : Additive (LineBundleClass X')) :
      (mark d).symm (Additive.ofMul (pullback p' a.toMul)) = (ν.symm a).val := by
    apply (mark d).injective
    rw [LinearEquiv.apply_symm_apply, internalBlowupPicardMarking_apply]
    exact (picardHom_contractedPicardMarking_symm k hT'.isClosedPointTower (hπ d) e' he' a).symm
  have hproj (U W : Submodule ℤ _) (h : U = W)
      (hU : IsCompl ((F).orthogonal U) U) (hW : IsCompl ((F).orthogonal W) W) (a) :
      ((F).orthogonal U).projection U hU a = ((F).orthogonal W).projection W hW a := by
    subst W
    rfl
  rw [← toMul_ofMul (primeDivisorClass ⟨x.val, (mem_boundaryPrimes.mp x.property).2⟩),
    ← toMul_ofMul (primeDivisorClass ⟨y.val, (mem_boundaryPrimes.mp y.property).2⟩), hc, hd]
  rw [contractedPicardMarking_symm_boundaryPrime k hΦ b s c hT e he hD x,
    contractedPicardMarking_symm_boundaryPrime k hΦ b s d hT' e' he' hD' y, hxy]
  exact hproj _ _ hspan _ _ _

end TauCeti.Toric.Fan
