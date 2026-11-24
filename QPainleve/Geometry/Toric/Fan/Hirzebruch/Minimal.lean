/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Numerical
import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter
import QPainleve.Geometry.Toric.Fan.Boundary.ProjectiveLine
import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective

/-!
# Exceptional curves on Hirzebruch surfaces

For a complete regular Hirzebruch fan of nonnegative index, the only possible
negative prime curve is the distinguished section. It is exceptional of the
first kind exactly at index one. This gives the index restriction in the
classification of minimal rational surfaces in
[Vakil, *Complex Algebraic Surfaces*, Class 17, §2][Vakil].

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass17A.pdf
-/

public section

open AlgebraicGeometry CategoryTheory Module TopologicalSpace
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (n : ℕ) (hΦ : Φ.IsRegular)
  (hc : Φ.IsComplete) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (n : ℤ) • b 0 - b 1])

local notation "X" => Φ.algebraicRealization
local notation "C" => Φ.hirzebruchPicardBasis b (n : ℤ) hΦ r hr
local notation "B" => Chow.intersectionBilinForm ℂ X
local notation "P" p:arg =>
  Additive.ofMul
    (@primeDivisorClass X _ _ (Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ) p)
local notation "p₀" => Φ.rayBoundaryPoint hΦ (r 0)
local notation "J" => Φ.rayBoundaryIdeal hΦ (r 0)
local notation "S" => Spec (CommRingCat.of ℂ)

include hc hr in
private theorem eq_section_of_selfIntersection_neg [Nonempty Φ.cones]
    [Φ.algebraicRealization.IsProjectiveOver ℂ] [SmoothOfRelativeDimension 2 (X ↘ S)]
    (p : CodimensionOnePoint X) (h : B (P p) (P p) < 0) : p = p₀ := by
  by_contra hne
  let x := P p
  let a := (C).repr x 0
  let d := (C).repr x 1
  have hd : 0 ≤ d := Φ.hirzebruch_fiber_degree_nonneg b n hΦ r hr hc p
  have hle : (n : ℤ) * d ≤ a :=
    le_of_not_gt fun hlt ↦ hne (Φ.eq_section_of_hirzebruch_fiber_coeff_lt b n hΦ r hr hc p hlt)
  have ha : 0 ≤ a := (mul_nonneg (Int.natCast_nonneg n) hd).trans hle
  have hx : x = a • C 0 + d • C 1 := by
    simpa only [a, d, Fin.sum_univ_two] using ((C).sum_repr x).symm
  obtain ⟨h₀, h₁⟩ := Φ.hirzebruchPicardBasis_intersection_repr b n hΦ r hr hc x
  have hnonneg : 0 ≤ B x x := by
    calc
      0 ≤ a * d + d * (a - (n : ℤ) * d) :=
        add_nonneg (mul_nonneg ha hd) (mul_nonneg hd (sub_nonneg.mpr hle))
      _ = B x x := by
        rw [congrArg (B x) hx]
        rw [map_add, map_smul, map_smul, h₀, h₁, Int.zsmul_eq_mul, Int.zsmul_eq_mul]
  exact not_lt_of_ge hnonneg h

include hc hr in
private theorem section_selfIntersection [Nonempty Φ.cones]
    [Φ.algebraicRealization.IsProjectiveOver ℂ] :
    Chow.classIntersectionNumber ℂ X
      (LineBundleClass.mk (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ (r 0)).toInvertibleSheaf)⁻¹
      (LineBundleClass.mk (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ (r 0)).toInvertibleSheaf)⁻¹ =
        -(n : ℤ) := by
  classical
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have hclass : C 1 = P p₀ := by
    rw [hirzebruchPicardBasis_apply_one, rayDivisorToPicard_single, one_zsmul]
  have hsq := Φ.hirzebruchPicardBasis_intersection b n hΦ r hr hc 1 1
  have hJ := Φ.isEffectiveCartier_rayBoundaryIdeal hΦ (r 0)
  have hprime : primeDivisorClass p₀ = (LineBundleClass.mk hJ.toInvertibleSheaf)⁻¹ := by
    rw [primeDivisorClass_def, mk_toInvertibleSheaf_congr _ hJ
      (Φ.rayBoundaryIdeal_def hΦ (r 0)).symm]
  rw [hclass, Chow.intersectionBilinForm_apply, toMul_ofMul, hprime] at hsq
  simpa using hsq

include hc hr in
/-- The exceptional curves of the first kind on a Hirzebruch surface are exactly
the distinguished invariant section in index one. The equality identifies the
actual ideal sheaf of the curve. -/
theorem isExceptionalCurveOfFirstKind_iff_of_hirzebruch (I : (X).IdealSheafData) :
    I.IsExceptionalCurveOfFirstKind ↔ n = 1 ∧ I = J := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : (X).IsProjectiveOver ℂ := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  let : SmoothOfRelativeDimension 2 (X ↘ S) :=
    hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have hJ := Φ.isEffectiveCartier_rayBoundaryIdeal hΦ (r 0)
  have hself := section_selfIntersection b n hΦ hc r hr
  constructor
  · intro hI
    let : IsIntegral I.subscheme := hI.isIntegral_subscheme
    let : IsProper (I.subscheme ↘ S) := by
      rw [over_eq_subschemeι_comp]
      infer_instance
    have : I.subscheme.IsCurveOver ℂ := Scheme.isCurveOver_iff.mpr
      ⟨inferInstance, inferInstance, hI.topologicalKrullDim_subscheme⟩
    have hC := hI.isEffectiveCartier
    have hsquare := ((hC.isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_classIntersectionNumber
      (k := ℂ) hdim.le).mp hI).2
    let p : CodimensionOnePoint X :=
      ⟨I.subschemeι (genericPoint I.subscheme), hC.coheight_subschemeι_genericPoint⟩
    have hp : vanishingIdeal ⟨closure {(p : X)}, isClosed_closure⟩ = I :=
      I.vanishingIdeal_closure_subschemeι_genericPoint
    have hclass : primeDivisorClass p = (LineBundleClass.mk hC.toInvertibleSheaf)⁻¹ := by
      rw [primeDivisorClass_def, mk_toInvertibleSheaf_congr _ hC hp]
    have hpneg : B (P p) (P p) < 0 := by
      rw [Chow.intersectionBilinForm_apply, toMul_ofMul, hclass, hsquare]
      decide
    have heq : I = J := by
      rw [← hp, rayBoundaryIdeal_def, eq_section_of_selfIntersection_neg b n hΦ hc r hr p hpneg]
    rw [mk_toInvertibleSheaf_congr hC hJ heq, hself] at hsquare
    exact ⟨by omega, heq⟩
  · rintro ⟨hn, rfl⟩
    let m := (b.detDualEquiv (r 0).primitiveGenerator).toAddMonoidHom
    have hm : m (r 0).primitiveGenerator = 0 := b.detDualEquiv_self _
    have hsurj := (r 0).surjective_detCharacter b
    have : (J).subscheme.IsCurveOver ℂ := (r 0).isCurveOver_boundaryComponent hΦ hN hm hsurj
    let e := (r 0).boundaryIsoProjectiveLine hΦ hN hm hsurj
    have hgenus : (J).subscheme.genus ℂ = 0 :=
      Scheme.genus_eq_zero_iff_exists_iso_projectiveLine.mpr ⟨e, inferInstance⟩
    exact (hJ.isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_classIntersectionNumber
      (k := ℂ) hdim.le).mpr ⟨hgenus, by simpa only [hn, Nat.cast_one] using hself⟩

end TauCeti.Toric.Fan
