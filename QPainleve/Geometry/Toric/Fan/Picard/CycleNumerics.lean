/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface
public import QPainleve.Geometry.Toric.Fan.Picard.Orthogonal
public import TauCeti.Algebra.Module.Primitive

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.LinearAlgebra.BilinearForm.QuotientDual
import QPainleve.SignedClusterModularGroup.BoundaryCycle

/-!
# Charge rank and index of a square-zero anticanonical cycle

The norm congruence at modulus zero shows that a nonzero isotropic boundary-orthogonal
class forces the toric charges to span the ray lattice rationally. When the boundary
classes form a primitive anticanonical cycle, the Picard boundary quotient then
bounds the charge index. The charge relation of the total boundary is primitive, and
its sum of coordinate squares is divisible by the charge index.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass
open Scheme.IdealSheafData
open LinearMap (BilinForm)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (hΦ : Φ.IsRegular) (hdim : Module.finrank ℤ N = 2)
  (s : Fin n → Φ.Ray) (m : Fin n → N →+ ℤ)
  (hm : ∀ j, m j (s j).primitiveGenerator = 0) (hprim : ∀ j, Function.Surjective (m j))
  (c : Fin n → ℂˣ)
  (J : Fin n →
    {I : (Φ.boundaryIdeal inferInstance).subscheme.IdealSheafData // I.IsEffectiveCartier})
  (hJ : ∀ j, (J j).val = ((s j).binomialCenterOnBoundary hdim (hm j) (hprim j) (c j)).ker)
  {X Y : Scheme} [X.Over (Spec (.of ℂ))] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))]
  {D : X.IdealSheafData} {d : ℕ} {T : QPainleve.BlowupTower X d Y}
  (hT : IsNodalBoundaryTower D (X ↘ Spec (.of ℂ)) (𝟙 X) T)
  (e : Y ≅ (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι J).1)
  (he : e.inv ≫ T.toBase ≫ (X ↘ Spec (.of ℂ)) =
    (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι J).2.toTower.toBase ≫
      (Φ.algebraicRealization ↘ Spec (.of ℂ)))
  (hD : ((D.comap T.toBase).comap e.inv).support =
    (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι J).2.boundaryι.ker.support)

local notation "Pic(" S ")" => Additive (LineBundleClass S)
local notation "A" => Chow.intersectionBilinForm ℂ X
local notation "fX" => (X ↘ Spec (CommRingCat.of ℂ))

variable (hc : Φ.IsComplete) [rational : Scheme.IsRationalOver (X ↘ Spec (.of ℂ))]

local instance : IsIntegral X :=
  let : Smooth fX := SmoothOfRelativeDimension.smooth 2 fX
  rational.isIntegral_of_smooth
local instance : IsNoetherian X := isNoetherian_of_finiteType fX
local instance : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
  (fX).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two

local notation "M" =>
  Scheme.Opens.primeDivisorSpanCompl (Closeds.compl (Scheme.IdealSheafData.support D))
local notation "v" => rayChargeMap s
local notation "q" =>
  picardBoundaryOrthogonalEquivChargeKernel hΦ hdim s m hm hprim c J hJ hT e he hD
local notation "Q" => chargeKernelIntersectionForm hΦ hdim s m hm hprim c J hJ hT e he hD

variable {k : ℕ} [NeZero k] (C : ZMod k → Pic(X))
  (hGram : ∀ j l : ZMod k, Chow.intersectionBilinForm ℂ X (C j) (C l) =
    (-2 : ℤ) * (if j = l then 1 else 0) +
      (if l = j + 1 then 1 else 0) + (if l = j - 1 then 1 else 0))

local notation "δ" => ∑ j, C j
local notation "KX" => LineBundleClass.mk (QPainleve.canonicalBundle ℂ X 2)

include hGram in
private theorem finrank_picard_eq_ten_of_anticanonical_cycle (hcan : δ = -Additive.ofMul KX) :
    Module.finrank ℤ (Pic(X)) = 10 := by
  have hzero := QPainleve.BoundaryCycle.pairing_sum_sum hGram
  rw [hcan, BilinForm.neg_left, BilinForm.neg_right, neg_neg,
    Chow.intersectionBilinForm_apply, toMul_ofMul] at hzero
  have hrank := Chow.finrank_picard_add_canonical_square_of_isRationalOver ℂ X
  omega

include hΦ hc hJ hT he hD hGram in
/-- An ordered toric presentation of a primitive square-zero anticanonical cycle on a
smooth complex projective rational surface has `12 - k` internal centers and charge
kernel rank `10 - k`, where `k` is the cycle length. The charge image has rank two
and index one, two, or three. The square of the index divides the cycle length,
which is at most nine. The total cycle gives a primitive charge relation whose sum
of squared coordinates is divisible by the index. -/
theorem chargeIndex_bounds_of_anticanonical_cycle
    (hspan : M = Submodule.span ℤ (Set.range C))
    (hcan : δ = -Additive.ofMul KX) (hδ : TauCeti.IsPrimitive δ) :
    n + k = 12 ∧ Module.finrank ℤ (v).ker = 10 - k ∧ Module.finrank ℤ (v).range = 2 ∧
      k ≤ 9 ∧ (v).range.toAddSubgroup.index ^ 2 ∣ k ∧
      (v).range.toAddSubgroup.index ∈ ({1, 2, 3} : Finset ℕ) ∧
      ∃ x : (v).ker, TauCeti.IsPrimitive x ∧
        ((v).range.toAddSubgroup.index : ℤ) ∣ ∑ j, x.val j ^ 2 := by
  let : Module.Free ℤ (Pic(X)) := X.free_picard_of_isRationalOver ℂ
  let : Module.Finite ℤ (Pic(X)) := X.finite_picard_of_isRationalOver ℂ
  let : HasUniqueDiv (Pic(X)) := HasUniqueDiv.of_isTorsionFree ℤ _
  have hA : A = Chow.classIntersectionBilinForm ℂ
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension fX (n := 2)) := by
    ext a b
    simp only [Chow.intersectionBilinForm_apply, Chow.classIntersectionBilinForm_apply]
  let : LinearMap.IsPerfPair A :=
    hA ▸ Chow.isPerfPair_classIntersectionBilinForm_of_isRationalOver ℂ X
  let z : (A).orthogonal M := ⟨δ, by
    rw [hspan, BilinForm.mem_orthogonal_iff]
    intro y hy
    have hp := QPainleve.BoundaryCycle.span_le_orthogonal_total hGram hy
    simpa only [Chow.intersectionBilinForm_apply, Chow.classIntersectionNumber_comm (δ).toMul]
      using BilinForm.mem_orthogonal_iff.mp hp δ (Submodule.mem_span_singleton_self δ)⟩
  let x := q z
  have hx : x ≠ 0 := (q).map_ne_zero_iff.mpr
    (fun hz ↦ hδ.ne_zero (congrArg Subtype.val hz))
  have hxx : Q x x = 0 := by
    simpa only [chargeKernelIntersectionForm_apply, x, LinearEquiv.symm_apply_apply] using
      QPainleve.BoundaryCycle.pairing_sum_sum hGram
  have hrange := finrank_rayChargeMap_range_of_isotropic hΦ hdim s m hm hprim c J hJ hT e he hD
    hc hx hxx
  have hrank := finrank_picard_eq_ten_of_anticanonical_cycle C hGram hcan
  have hM : Module.finrank ℤ M = k := by
    rw [hspan, finrank_span_eq_card (QPainleve.BoundaryCycle.linearIndependent hGram hδ.ne_zero),
      ZMod.card]
  have horth := (A).finrank_add_finrank_orthogonal_int M
  rw [hM, (q).finrank_eq, hrank] at horth
  have hnull := (v).finrank_range_add_finrank_ker
  simp [hrange] at hnull
  have hpos : 0 < Module.finrank ℤ (v).ker := by
    let : Nontrivial ((v).ker) := ⟨⟨x, 0, hx⟩⟩
    exact Module.finrank_pos
  have hdiv : (v).range.toAddSubgroup.index ^ 2 ∣ k := by
    rw [← natCard_torsion_picardBoundaryQuotient_eq_chargeIndex hΦ hdim s m hm hprim c J hJ
      hT e hD (hrange.trans hdim.symm), hspan]
    exact QPainleve.BoundaryCycle.natCard_torsion_quotient_sq_dvd hGram hδ
  have hk : k ≤ 9 := by omega
  have hkpos := Nat.pos_of_ne_zero (NeZero.ne k)
  have hsmall : (v).range.toAddSubgroup.index ≤ 3 :=
    (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp ((Nat.le_of_dvd hkpos hdiv).trans hk)
  have hne := Nat.pos_of_dvd_of_pos ((dvd_pow_self _ (by decide : 2 ≠ 0)).trans hdiv) hkpos
  refine ⟨by omega, by omega, hrange, hk, hdiv, ?_, x, ?_, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp hδ
    apply (q).isPrimitive_iff.mpr
    exact TauCeti.isPrimitive_def.mpr ⟨f.comp ((A).orthogonal M).subtype, hf⟩
  · exact chargeIndex_dvd_sum_sq_of_isotropic hΦ hdim s m hm hprim c J hJ hT e he hD hc x hxx

end TauCeti.Toric.Fan
