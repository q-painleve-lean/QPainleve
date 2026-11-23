/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Picard
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

variable [X.Over (Spec (.of k))] [(e ≫ i).IsOver (Spec (.of k))]

local notation "g" => (BlowupTower.toBase T ≫ X ↘ S)

include hp hJ in
/-- If the transform of a class is nef, the sum of its multiplicities over a boundary
component is at most its initial degree on that component. Each infinitely near center
in the ordered boundary tower contributes its own multiplicity. -/
theorem sum_multiplicities_le_intersectionNumber_alongBoundary
    (a : LineBundleClass X) (m : Fin n → ℤ)
    (hnef : LineBundleClass.IsNef k g (picardHom T (Additive.ofMul a, -m)).toMul) :
    ∑ j ∈ s, m j ≤ intersectionNumber k (e ≫ i) a := by
  have hcomp : (e ≫ WithBoundary.boundaryι B) ≫ g = C ↘ S := by
    simp only [Category.assoc, WithBoundary.boundaryι_toBase_assoc, ← Category.assoc e i,
      comp_over (e ≫ i) S]
  have hdeg := hnef.intersectionNumber_nonneg (e ≫ WithBoundary.boundaryι B) hcomp.symm
  rw [intersectionNumber_picardHom_alongBoundary i e J p hp hJ a (-m)] at hdeg
  simp only [Pi.neg_apply, Finset.sum_neg_distrib] at hdeg
  omega

include hp hJ in
/-- Among the centers on a fixed component, at most one has multiplicity greater than
half the initial degree there, provided the transformed class is nef and all center
multiplicities on that component are nonnegative. -/
theorem card_filter_two_mul_lt_multiplicities_alongBoundary
    (a : LineBundleClass X) (m : Fin n → ℤ)
    (hnef : LineBundleClass.IsNef k g (picardHom T (Additive.ofMul a, -m)).toMul)
    (hm : ∀ j ∈ s, 0 ≤ m j) :
    (Finset.filter (fun j ↦ intersectionNumber k (e ≫ i) a < 2 * m j) s).card ≤ 1 := by
  refine Finset.card_le_one_iff.mpr fun {j l} hj hl ↦ ?_
  obtain ⟨hj, hj'⟩ := Finset.mem_filter.mp hj
  obtain ⟨hl, hl'⟩ := Finset.mem_filter.mp hl
  by_contra hne
  have hsum := Finset.add_le_sum hm hj hl hne
  have hbound := sum_multiplicities_le_intersectionNumber_alongBoundary i e J p hp hJ a m hnef
  omega

end QPainleve.BlowupTower
