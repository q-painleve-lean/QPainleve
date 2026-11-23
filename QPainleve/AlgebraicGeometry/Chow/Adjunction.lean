/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import QPainleve.AlgebraicGeometry.IdealSheaf.EulerCharacteristic

import QPainleve.AlgebraicGeometry.IdealSheaf.Image.Over
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Geometrically.GlobalSections

/-!
# Arithmetic adjunction from surface Riemann–Roch

For an integral effective Cartier curve on a smooth projective surface, the arithmetic
adjunction equation is equivalent to the surface Riemann–Roch equation for its ideal
line bundle. The ideal exact sequence compares the Euler characteristics and the
restriction degree identifies the signs of the two intersection terms.

[Hacking, *Compact Complex Surfaces*, §5.2](https://paulhacking.github.io/surfaces.pdf#page=30)
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules LineBundleClass

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  {I : X.IdealSheafData} [I.subscheme.IsCurveOver k]

/-- Arithmetic adjunction for the effective curve is equivalent to the doubled Riemann–Roch
equation for its ideal line bundle. The arithmetic genus is computed on the given curve,
including when it is singular. -/
theorem two_mul_genus_sub_two_eq_intersection_iff_riemannRoch (hI : I.IsEffectiveCartier)
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    (hconst : Function.Surjective (Scheme.Modules.baseRingToGlobalSections k I.subscheme)) :
    let J := LineBundleClass.mk hI.toInvertibleSheaf
    let K := LineBundleClass.mk (QPainleve.canonicalBundle k X 2)
    let B := Chow.classIntersectionNumber k X
    2 * (I.subscheme.genus k : ℤ) - 2 = B J⁻¹ J⁻¹ + B J⁻¹ K ↔
      2 * (eulerCharBelow k J 3 - eulerCharBelow k (1 : LineBundleClass X) 3) = B J J - B J K := by
  intro J K B
  have : Nonempty X := Nonempty.map I.subschemeι inferInstance
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)
  have hcomm (a b : LineBundleClass X) : B a b = B b a :=
    Chow.classIntersectionNumber_comm a b
  have hC := Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := I.subscheme) k
  have hneg (a : LineBundleClass X) : B a J = -B a J⁻¹ := by
    have h := Chow.classIntersectionNumber_mul_zpow_inv_mk_toInvertibleSheaf
      k hX.le hI hC a 1 (-1)
    simpa only [J, B, one_mul, zpow_neg_one, inv_inv, Chow.classIntersectionNumber_one_right,
      zero_add, neg_one_mul, ← Chow.classIntersectionNumber_eq_intersectionNumber_subschemeι
        k hX.le hI hC] using h
  have hself : B J J = B J⁻¹ J⁻¹ := by
    rw [hneg J, hcomm J J⁻¹, hneg J⁻¹, neg_neg]
  have hcan : B J K = -B J⁻¹ K := by
    rw [hcomm J K, hneg K, hcomm K J⁻¹]
  rw [hI.eulerCharBelow_sub_eulerCharBelow_one_eq_genus_sub_one
    (hX.trans_lt (by decide)) hconst, hself, hcan]
  omega

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] [IsAlgClosed k] {C X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [C.Over (Spec (.of k))] [C.IsCurveOver k]

/-- For a closed integral curve over an algebraically closed field, arithmetic adjunction
is equivalent to Riemann–Roch for the line bundle of its Cartier ideal in the ambient surface.
The genus is that of the source of the specified closed immersion. -/
theorem two_mul_genus_sub_two_eq_intersection_iff_riemannRoch (i : C ⟶ X)
    [IsClosedImmersion i] [i.IsOver (Spec (.of k))] (hI : i.ker.IsEffectiveCartier) :
    let J := LineBundleClass.mk hI.toInvertibleSheaf
    let K := LineBundleClass.mk (QPainleve.canonicalBundle k X 2)
    let B := Chow.classIntersectionNumber k X
    2 * (C.genus k : ℤ) - 2 = B J⁻¹ J⁻¹ + B J⁻¹ K ↔
      2 * (eulerCharBelow k J 3 - eulerCharBelow k (1 : LineBundleClass X) 3) = B J J - B J K := by
  have : IsIntegral i.ker.subscheme := IsIntegral.of_isIso i.toImage
  have : i.ker.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k i.ker.subschemeι
  have hdim : topologicalKrullDim i.ker.subscheme = 1 :=
    (i.toImage.homeomorph.isHomeomorph.topologicalKrullDim_eq).symm.trans
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one k)
  have : i.ker.subscheme.IsCurveOver k :=
    Scheme.isCurveOver_iff.mpr ⟨inferInstance, inferInstance, hdim⟩
  have hconst := (i.ker.subscheme.baseRingToGlobalSections_bijective_of_isIntegrallyClosedIn k
    isIntegrallyClosedIn_of_isAlgClosed).surjective
  have hgen : i.ker.subscheme.genus k = C.genus k := by
    simpa only [Scheme.genus_def] using (i.toImage.finrank_cohomology_trivial_of_isIso k 1).symm
  simpa only [hgen] using hI.two_mul_genus_sub_two_eq_intersection_iff_riemannRoch hconst

end AlgebraicGeometry.Scheme.Hom
