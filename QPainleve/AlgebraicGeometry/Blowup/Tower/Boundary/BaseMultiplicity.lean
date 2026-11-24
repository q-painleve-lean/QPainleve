/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Picard
public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Basic
public import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef
import QPainleve.AlgebraicGeometry.IntersectionNumber.ClosedPoint
import TauCeti.AlgebraicGeometry.Curves.Normalization
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Multiplicity bounds along a boundary component

For a point-blowup tower along a fixed boundary, the degree of a marked line bundle on
a strict-transform component equals its base degree plus its exceptional coefficients
at the centers on that component. The formula counts repeated centers separately.
In particular, when the transformed class is nef, the sum of the multiplicities on
the component is bounded by the original degree.

This is the intersection calculation for the interior blowups in
[Lutz's appendix to Hacking and Keating, Proposition 8.7][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass

universe u

namespace QPainleve.BlowupTower

variable {k : Type u} [Field k] [IsAlgClosed k] {X D C : Scheme.{u}} {n : ℕ}
  (i : D ⟶ X) [IsClosedImmersion i] (e : C ⟶ D) [IsClosedImmersion e]
  [C.Over (Spec (.of k))] [C.IsCurveOver k]
  (J : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier})
  (p : Fin n → D) (hp : ∀ j, IsClosed ({p j} : Set D))
  (hJ : ∀ j, (J j).val = (D.fromSpecResidueField (p j)).ker)
  [∀ j, Decidable (p j ∈ Set.range e)]

local notation "S" => Spec (CommRingCat.of k)
local notation "B" => (Sigma.snd (alongBoundary i J))
local notation "T" => (WithBoundary.toTower B)
local notation "s" => (Finset.univ.filter fun j ↦ p j ∈ Set.range e)

include hp hJ in
/-- In the ordered Picard marking, restriction to the strict component adds the exceptional
coefficients exactly at the centers lying on that component. The degree is computed on the
same integral curve via its strict-transform embedding. -/
theorem intersectionNumber_picardHom_alongBoundary
    (a : LineBundleClass X) (b : Fin n → ℤ) :
    intersectionNumber k (e ≫ WithBoundary.boundaryι B) (picardHom T (Additive.ofMul a, b)).toMul =
      intersectionNumber k (e ≫ i) a + ∑ j ∈ s, b j := by
  have : RelativeDimensionLE 1 (C ↘ S) :=
    (relativeDimensionLE_iff_of_field _).mpr (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  have hdegree (j : Fin n) :
      intersectionNumber k e (mk (J j).property.toInvertibleSheaf) =
        if p j ∈ Set.range e then -1 else 0 := by
    have hI : (D.fromSpecResidueField (p j)).ker.IsEffectiveCartier := hJ j ▸ (J j).property
    rw [mk_toInvertibleSheaf_congr _ hI (hJ j)]
    exact intersectionNumber_mk_ker_fromSpecResidueField e (hp j) hI
  rw [← intersectionNumber_pullback, pullback_picardHom_alongBoundary,
    intersectionNumber_mul_of_isIntegral, intersectionNumber_pullback, toMul_ofMul,
    intersectionNumber_prod_of_isIntegral, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [intersectionNumber_zpow_of_isIntegral, hdegree]
  split <;> simp

include hp hJ in
/-- If the class with exceptional coefficients `-m` is nef, the sum of its base
multiplicities on the boundary curve is bounded by the original intersection number. -/
theorem sum_baseMultiplicity_le_boundaryIntersection (f : X ⟶ S)
    (hbase : C ↘ S = (e ≫ i) ≫ f) (a : LineBundleClass X) (m : Fin n → ℤ)
    (hnef : ((T).picardHom (Additive.ofMul a, -m)).toMul.IsNef k ((T).toBase ≫ f)) :
    ∑ j ∈ s, m j ≤ intersectionNumber k (e ≫ i) a := by
  have hfinal : C ↘ S = (e ≫ WithBoundary.boundaryι B) ≫ (T).toBase ≫ f := by
    simpa only [Category.assoc, WithBoundary.boundaryι_toBase_assoc] using hbase
  have hdeg := hnef.intersectionNumber_nonneg (e ≫ WithBoundary.boundaryι B) hfinal
  rw [intersectionNumber_picardHom_alongBoundary i e J p hp hJ a (-m)] at hdeg
  simp only [Pi.neg_apply, Finset.sum_neg_distrib] at hdeg
  omega

section

omit [∀ j, Decidable (p j ∈ Set.range e)]

include hp hJ in
/-- Two labels above the same boundary curve cannot both have multiplicity strictly greater
than half its original intersection number. This also applies to distinct labels with the
same original center. -/
theorem eq_of_boundaryIntersection_lt_two_mul_baseMultiplicity
    (f : X ⟶ S) (hbase : C ↘ S = (e ≫ i) ≫ f)
    (a : LineBundleClass X) (m : Fin n → ℤ)
    (hnef : ((T).picardHom (Additive.ofMul a, -m)).toMul.IsNef k ((T).toBase ≫ f))
    (hm : ∀ j, p j ∈ Set.range e → 0 ≤ m j)
    {r l : Fin n} (hr : p r ∈ Set.range e) (hl : p l ∈ Set.range e)
    (hrm : intersectionNumber k (e ≫ i) a < 2 * m r)
    (hlm : intersectionNumber k (e ≫ i) a < 2 * m l) :
    r = l := by
  classical
  by_contra hne
  have hr' : r ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
  have hl' : l ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩
  have hsum := Finset.add_le_sum (fun j hj ↦ hm j (Finset.mem_filter.mp hj).2) hr' hl' hne
  have hbound := sum_baseMultiplicity_le_boundaryIntersection i e J p hp hJ f hbase a m hnef
  omega

end

variable (f : X ⟶ Spec (.of k)) [hIntegral : IsIntegral X] [hNoeth : IsNoetherian X]
  [hSmooth : SmoothOfRelativeDimension 2 f]

include hIntegral hNoeth hSmooth in
/-- The successive orders of an effective Cartier divisor at the chosen centers on a
boundary curve sum to at most its original intersection with the curve if the final
strict transform has nef positive class. The orders are taken before the corresponding
blowups, including at infinitely near points. -/
theorem sum_neg_strictTransformCoefficients_le_boundaryIntersection
    (hbase : C ↘ S = (e ≫ i) ≫ f)
    {A : X.IdealSheafData} (hA : A.IsEffectiveCartier) :
    let hT := isClosedPointTower_alongBoundary i J (fun j ↦ ⟨p j, hp j, hJ j⟩)
    let hStrict := hT.isEffectiveCartier_strictTransform f hA
    ((mk hStrict.toInvertibleSheaf)⁻¹).IsNef k ((T).toBase ≫ f) →
      (∑ j ∈ s, -hT.strictTransformCoefficients A j) ≤
        intersectionNumber k (e ≫ i) (mk hA.toInvertibleSheaf)⁻¹ := by
  intro hT hStrict hnef
  have hclass := congrArg Additive.toMul (hT.picardMarking_strictTransform f hA)
  simp only [picardMarking_apply, toMul_ofMul] at hclass
  exact sum_baseMultiplicity_le_boundaryIntersection i e J p hp hJ f hbase
    (mk hA.toInvertibleSheaf)⁻¹ (-hT.strictTransformCoefficients A)
    (by simpa only [neg_neg, hclass] using hnef)

end QPainleve.BlowupTower
