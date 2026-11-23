/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
public import QPainleve.AlgebraicGeometry.Blowup.Projective.Line

import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.AffineLine
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Divisors of a projective-line elementary transformation

In the common blowup of the two rulings, the total transform of the base divisor is
the sum of the two exceptional divisors. The total transforms of each coordinate
section differ by the exceptional divisor on the side where the section contains the center.
These ideal-sheaf identities give the pullback formulas for the three Picard classes.

This is the divisor calculation for the elementary transformation of Gross, Hacking
and Keel, [*Birational geometry of cluster algebras*][GHK], §3.1.

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory Polynomial
open Scheme.IdealSheafData (blowupExceptionalClass_def comap_comp comap_mul mul_top top_mul)
open TauCeti.NodeAlgebra

namespace TauCeti.AlgebraicGeometry.projectiveLine

universe u

variable {R : Type u} [CommRing R] (f : R) (i : Fin 2)

local notation "P" => R[X]
local notation "N" => NodeAlgebra R f
local notation "𝓘(" a ")" =>
  IdealSheafData.ofIdealTop
    (Ideal.map (CommRingCat.Hom.hom (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of _))))
      (Ideal.span (singleton a)))
local notation "Z(" i ")" => coordinateSectionCenter f i
local notation "D(" i ")" => coordinateSectionCenter (0 : R) i
local notation "π(" i ")" => IdealSheafData.blowupToBase (Z(i))
local notation "E(" i ")" => IdealSheafData.comap (Z(i)) π(i)
local notation "p" => (projectiveLine R ↘ Spec (CommRingCat.of R))

local notation "F" =>
  Scheme.Hom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (singleton f)))))

private theorem comap_baseDivisor_SpecMap {A : Type u} [CommRing A] (g : R →+* A) :
    (F).comap (Spec.map (CommRingCat.ofHom g)) = 𝓘(g f) := by
  rw [Scheme.Hom.ker_Spec_map, CommRingCat.hom_ofHom, Ideal.mk_ker,
    IdealSheafData.comap_ofIdealTop_map_ΓSpecIso_inv, Ideal.map_span, Set.image_singleton,
    CommRingCat.hom_ofHom]

/-- The total transform of the opposite coordinate section is effective Cartier. -/
theorem isEffectiveCartier_comap_coordinateSectionCenter_zero_rev (hf : IsSMulRegular R f) :
    ((D(i.rev)).comap π(i)).IsEffectiveCartier := by
  apply isEffectiveCartier_of_sectionBlowupCharts f i hf
  · rw [← comap_comp, sectionBlowupNodeChartι_blowupToBase,
      comap_coordinateSectionCenter_zero_rev_polynomialPoint]
    exact IdealSheafData.isEffectiveCartier_top _
  · rw [← comap_comp, sectionBlowupDivisorChartι_blowupToBase,
      comap_coordinateSectionCenter_zero_rev_polynomialPoint]
    exact IdealSheafData.isEffectiveCartier_top _
  · rw [← comap_comp, sectionBlowupOppositeChartι_blowupToBase]
    exact (isEffectiveCartier_coordinateSectionCenter_zero i.rev).comap (polynomialChartι R i.rev)

section Domain

variable [IsDomain R] (hf : f ≠ 0)

local notation "h" => IsLeftRegular.isSMulRegular (IsRegular.left (IsRegular.of_ne_zero hf))
local notation "e" => elementaryTransform f i hf

/-- In the common blowup, the total transform of the base divisor is the sum of the
source exceptional divisor and the pullback of the target exceptional divisor. -/
theorem comap_baseDivisor_elementaryTransform :
    (F).comap (π(i) ≫ p) = E(i) * (E(i.rev)).comap (e).hom := by
  apply sectionBlowup_idealSheaf_ext f i h
  -- At the intersection of the exceptional divisors, the two coordinates multiply to f.
  · rw [← comap_comp, sectionBlowupNodeChartι_blowupToBase_assoc,
      polynomialPoint_over, comap_baseDivisor_SpecMap, comap_mul,
      exceptional_comap_sectionBlowupNodeChartι, ← comap_comp (E(i.rev)),
      sectionBlowupNodeChartι_elementaryTransform_hom,
      exceptional_comap_sectionBlowupNodeChartι]
    have hi : i.rev = 1 - i := by fin_cases i <;> decide
    rw [← IdealSheafData.ofIdealTop_mul, ← Ideal.map_mul, Ideal.span_singleton_mul_span_singleton,
      hi, coord_mul_coord_one_sub]
  · rw [← comap_comp, sectionBlowupDivisorChartι_blowupToBase_assoc,
      polynomialPoint_over, comap_baseDivisor_SpecMap, comap_mul,
      exceptional_comap_sectionBlowupDivisorChartι, ← comap_comp (E(i.rev)),
      sectionBlowupDivisorChartι_elementaryTransform_hom,
      exceptional_comap_sectionBlowupOppositeChartι, mul_top]
  · rw [← comap_comp, sectionBlowupOppositeChartι_blowupToBase_assoc,
      polynomialChartι_over, comap_baseDivisor_SpecMap, comap_mul,
      exceptional_comap_sectionBlowupOppositeChartι, ← comap_comp (E(i.rev)),
      sectionBlowupOppositeChartι_elementaryTransform_hom,
      exceptional_comap_sectionBlowupDivisorChartι, top_mul, Polynomial.algebraMap_eq]

/-- The total transform of the source center's section contains the source exceptional
divisor in addition to the pullback of that section from the target ruling. -/
theorem comap_coordinateSectionCenter_elementaryTransform :
    (D(i)).comap (π(i)) =
      ((D(i)).comap ((e).hom ≫ π(i.rev))) * E(i) := by
  apply sectionBlowup_idealSheaf_ext f i h
  · rw [← comap_comp, sectionBlowupNodeChartι_blowupToBase,
      comap_coordinateSectionCenter_zero_polynomialPoint, comap_mul,
      ← comap_comp (D(i)), sectionBlowupNodeChartι_elementaryTransform_hom_assoc,
      sectionBlowupNodeChartι_blowupToBase,
      comap_coordinateSectionCenter_zero_polynomialPoint_rev, top_mul,
      exceptional_comap_sectionBlowupNodeChartι]
  · rw [← comap_comp, sectionBlowupDivisorChartι_blowupToBase,
      comap_coordinateSectionCenter_zero_polynomialPoint, comap_mul,
      ← comap_comp (D(i)), sectionBlowupDivisorChartι_elementaryTransform_hom_assoc,
      sectionBlowupOppositeChartι_blowupToBase, Fin.rev_rev,
      coordinateSectionCenter_zero_comap_polynomialChartι,
      exceptional_comap_sectionBlowupDivisorChartι]
    simpa only [Polynomial.zeroIdealSheaf_eq_ofIdealTop, mul_comm (X : P) (C f)] using
      Polynomial.zeroIdealSheaf_mul (X : P) (C f)
  · rw [← comap_comp, sectionBlowupOppositeChartι_blowupToBase,
      coordinateSectionCenter_comap_polynomialChartι_rev, comap_mul,
      ← comap_comp (D(i)),
      sectionBlowupOppositeChartι_elementaryTransform_hom_assoc,
      sectionBlowupDivisorChartι_blowupToBase,
      comap_coordinateSectionCenter_zero_polynomialPoint_rev,
      exceptional_comap_sectionBlowupOppositeChartι, top_mul]

/-- The total transform of the target center's section contains the target exceptional
divisor in addition to the total transform of that section from the source ruling. -/
theorem comap_coordinateSectionCenter_rev_elementaryTransform :
    (D(i.rev)).comap ((e).hom ≫ π(i.rev)) =
      ((D(i.rev)).comap (π(i))) * (E(i.rev)).comap (e).hom := by
  apply sectionBlowup_idealSheaf_ext f i h
  · rw [← comap_comp, sectionBlowupNodeChartι_elementaryTransform_hom_assoc,
      sectionBlowupNodeChartι_blowupToBase, comap_coordinateSectionCenter_zero_polynomialPoint,
      comap_mul, ← comap_comp (D(i.rev)),
      sectionBlowupNodeChartι_blowupToBase, comap_coordinateSectionCenter_zero_rev_polynomialPoint]
    rw [← comap_comp (E(i.rev)), sectionBlowupNodeChartι_elementaryTransform_hom,
      exceptional_comap_sectionBlowupNodeChartι, top_mul]
  · rw [← comap_comp, sectionBlowupDivisorChartι_elementaryTransform_hom_assoc,
      sectionBlowupOppositeChartι_blowupToBase, coordinateSectionCenter_comap_polynomialChartι_rev,
      comap_mul, ← comap_comp (D(i.rev)),
      sectionBlowupDivisorChartι_blowupToBase,
      comap_coordinateSectionCenter_zero_rev_polynomialPoint]
    rw [← comap_comp (E(i.rev)), sectionBlowupDivisorChartι_elementaryTransform_hom,
      exceptional_comap_sectionBlowupOppositeChartι, top_mul]
  · rw [← comap_comp,
      sectionBlowupOppositeChartι_elementaryTransform_hom_assoc,
      sectionBlowupDivisorChartι_blowupToBase, comap_coordinateSectionCenter_zero_polynomialPoint,
      comap_mul, ← comap_comp (D(i.rev)),
      sectionBlowupOppositeChartι_blowupToBase, coordinateSectionCenter_zero_comap_polynomialChartι,
      ← comap_comp (E(i.rev)),
      sectionBlowupOppositeChartι_elementaryTransform_hom,
      exceptional_comap_sectionBlowupDivisorChartι]
    simpa only [Polynomial.zeroIdealSheaf_eq_ofIdealTop, mul_comm (X : P) (C f)] using
      Polynomial.zeroIdealSheaf_mul (X : P) (C f)

include hf in
/-- The total transform of the section containing the center is effective Cartier. -/
theorem isEffectiveCartier_comap_coordinateSectionCenter_zero :
    ((D(i)).comap π(i)).IsEffectiveCartier := by
  have hs := isEffectiveCartier_comap_coordinateSectionCenter_zero_rev f i.rev h
  rw [Fin.rev_rev] at hs
  rw [comap_coordinateSectionCenter_elementaryTransform f i hf, comap_comp]
  exact isEffectiveCartier_mul (hs.comap (e).hom) (Z(i)).isEffectiveCartier_comap_blowupToBase

include hf in
/-- The total transform of the base divisor is effective Cartier. -/
theorem isEffectiveCartier_comap_baseDivisor :
    ((F).comap (π(i) ≫ p)).IsEffectiveCartier := by
  rw [comap_baseDivisor_elementaryTransform f i hf]
  exact isEffectiveCartier_mul (Z(i)).isEffectiveCartier_comap_blowupToBase
    ((Z(i.rev)).isEffectiveCartier_comap_blowupToBase.comap (e).hom)

open LineBundleClass

local notation "cl(" hc ")" =>
  Inv.inv (LineBundleClass.mk (Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf hc))
local notation "S(" j ")" => cl(isEffectiveCartier_coordinateSectionCenter_zero (R := R) j)
local notation "Ex(" j ")" => IdealSheafData.blowupExceptionalClass (Z(j))

/-- The target exceptional class pulls back to the total base-divisor class
minus the source exceptional class. -/
theorem pullback_blowupExceptionalClass_elementaryTransform :
    pullback (e).hom Ex(i.rev) =
      cl(isEffectiveCartier_comap_baseDivisor f i hf) / Ex(i) := by
  let hE := (Z(i)).isEffectiveCartier_comap_blowupToBase
  let hE' := (Z(i.rev)).isEffectiveCartier_comap_blowupToBase
  have hc := mk_toInvertibleSheaf_congr (isEffectiveCartier_comap_baseDivisor f i hf)
    (isEffectiveCartier_mul hE (hE'.comap (e).hom))
    (comap_baseDivisor_elementaryTransform f i hf)
  rw [mk_toInvertibleSheaf_mul hE (hE'.comap (e).hom)] at hc
  apply eq_div_iff_mul_eq'.mpr
  rw [blowupExceptionalClass_def, pullback_inv, hE'.pullback_mk_toInvertibleSheaf
    (hE'.comap (e).hom), blowupExceptionalClass_def, hc, mul_inv_rev]

/-- The target class of the source center's section pulls back to its source total
transform minus the source exceptional class. -/
theorem pullback_coordinateSection_elementaryTransform :
    pullback ((e).hom ≫ π(i.rev)) S(i) = pullback π(i) S(i) / Ex(i) := by
  let hD := isEffectiveCartier_coordinateSectionCenter_zero (R := R) i
  let hS := isEffectiveCartier_comap_coordinateSectionCenter_zero f i hf
  let hE := (Z(i)).isEffectiveCartier_comap_blowupToBase
  have hT : ((D(i)).comap ((e).hom ≫ π(i.rev))).IsEffectiveCartier := by
    rw [comap_comp]
    have ht := isEffectiveCartier_comap_coordinateSectionCenter_zero_rev f i.rev h
    rw [Fin.rev_rev] at ht
    exact ht.comap (e).hom
  have hc := mk_toInvertibleSheaf_congr hS (isEffectiveCartier_mul hT hE)
    (comap_coordinateSectionCenter_elementaryTransform f i hf)
  rw [mk_toInvertibleSheaf_mul hT hE] at hc
  apply eq_div_iff_mul_eq''.mpr
  rw [blowupExceptionalClass_def, pullback_inv, pullback_inv,
    hD.pullback_mk_toInvertibleSheaf hS, hD.pullback_mk_toInvertibleSheaf hT,
    hc, mul_inv_rev]

/-- The target class of its center's section pulls back to the source total transform
of that section plus the total base-divisor class minus the source exceptional class. -/
theorem pullback_coordinateSection_rev_elementaryTransform :
    pullback ((e).hom ≫ π(i.rev)) S(i.rev) =
      pullback π(i) S(i.rev) * (cl(isEffectiveCartier_comap_baseDivisor f i hf) / Ex(i)) := by
  rw [← pullback_blowupExceptionalClass_elementaryTransform f i hf]
  let hD := isEffectiveCartier_coordinateSectionCenter_zero (R := R) i.rev
  let hS := isEffectiveCartier_comap_coordinateSectionCenter_zero_rev f i h
  let hE' := (Z(i.rev)).isEffectiveCartier_comap_blowupToBase
  have hT : ((D(i.rev)).comap ((e).hom ≫ π(i.rev))).IsEffectiveCartier := by
    rw [comap_comp]
    exact (isEffectiveCartier_comap_coordinateSectionCenter_zero f i.rev hf).comap (e).hom
  have hc := mk_toInvertibleSheaf_congr hT (isEffectiveCartier_mul hS (hE'.comap (e).hom))
    (comap_coordinateSectionCenter_rev_elementaryTransform f i hf)
  rw [mk_toInvertibleSheaf_mul hS (hE'.comap (e).hom)] at hc
  simp only [pullback_inv, hD.pullback_mk_toInvertibleSheaf hT,
    hD.pullback_mk_toInvertibleSheaf hS, blowupExceptionalClass_def,
    hE'.pullback_mk_toInvertibleSheaf (hE'.comap (e).hom), hc, mul_inv_rev]
  exact mul_comm _ _

end Domain

end TauCeti.AlgebraicGeometry.projectiveLine
