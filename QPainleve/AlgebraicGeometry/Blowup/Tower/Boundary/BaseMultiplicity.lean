/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Picard
public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform
public import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.EulerCharacteristic
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Base multiplicities along a boundary curve

For an ordered blowup tower with reduced point centers on a fixed boundary, restriction
to an integral boundary curve counts each exceptional coefficient whose center lies on
that curve. Repeated centers contribute at each stage of the tower.

If the transformed class is nef, the sum of the base multiplicities on the curve is
bounded by the original intersection number. This is the intersection estimate used in
[Lutz, Appendix to *Homological mirror symmetry for log Calabi–Yau surfaces*,
Proposition 8.7][Lutz].

[Lutz]: https://arxiv.org/pdf/2005.05010v3#page=70
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open LineBundleClass Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower

variable (k : Type u) [Field k] [hk : IsAlgClosed k]
  {C D : Scheme.{u}} [C.Over (Spec (.of k))] [hProj : C.IsProjectiveOver k]
  (e : C ⟶ D) [heClosed : IsClosedImmersion e]

include hk hProj heClosed in
private theorem eulerDegree_mk_comap_point (p : D) (hp : IsClosed ({p} : Set D))
    (h : ((D.fromSpecResidueField p).ker.comap e).IsEffectiveCartier)
    [Decidable (p ∈ Set.range e)] :
    eulerDegree k (mk h.toInvertibleSheaf) = if p ∈ Set.range e then -1 else 0 := by
  by_cases hmem : p ∈ Set.range e
  · obtain ⟨q, rfl⟩ := hmem
    have hq : IsClosed ({q} : Set C) := by
      apply e.isClosedEmbedding.isClosed_iff_image_isClosed.mpr
      simpa only [Set.image_singleton] using hp
    let s := C.fromSpecResidueField q
    have hs : IsClosedImmersion s := isClosed_singleton_iff_isClosedImmersion.mp hq
    have hker : (D.fromSpecResidueField (e q)).ker.comap e = s.ker := by
      rw [Scheme.ker_fromSpecResidueField_eq_vanishingIdeal,
        comap_vanishingIdeal_closure_singleton_of_isClosedImmersion,
        ← Scheme.ker_fromSpecResidueField_eq_vanishingIdeal]
    have hC : s.ker.IsEffectiveCartier := hker ▸ h
    let f := C ↘ Spec (CommRingCat.of k)
    have : IsIso (s ≫ f) := by
      rw [← SpecMap_residueFieldIsoBase_inv f q hq]
      infer_instance
    have : IsIso (s.ker.subschemeι ≫ f) := by
      rw [← isIso_comp_left_iff s.toImage, ← Category.assoc, Scheme.Hom.toImage_imageι]
      infer_instance
    have := Scheme.Modules.moduleFinite_cohomology_of_isProjectiveOver k
      (InvertibleSheaf.trivial C).obj 0
    have := Scheme.Modules.moduleFinite_cohomology_of_isProjectiveOver k
      (InvertibleSheaf.trivial C).obj 1
    rw [mk_toInvertibleSheaf_congr h hC hker, eulerDegree_mk,
      hC.eulerDegree_toInvertibleSheaf k _ default, Scheme.Hom.finrank_eq_one_of_isIso]
    simp
  · have htop : (D.fromSpecResidueField p).ker.comap e = ⊤ := by
      rw [comap_eq_top_iff, ← Opens.coe_eq_univ, Scheme.Hom.coe_preimage,
        Closeds.coe_compl, Scheme.support_ker_fromSpecResidueField_of_isClosed hp,
        Set.eq_univ_iff_forall]
      exact fun q hq ↦ hmem ⟨q, hq⟩
    rw [mk_toInvertibleSheaf_congr h (isEffectiveCartier_top C) htop,
      mk_toInvertibleSheaf_top, eulerDegree_one, ite_eq_right hmem]

variable {X : Scheme.{u}} [hCurve : C.IsCurveOver k] {n : ℕ} (i : D ⟶ X) [IsClosedImmersion i]
  (J : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier})
  (p : Fin n → D) (hp : ∀ j, IsClosed ({p j} : Set D))
  (hJ : ∀ j, (J j).val = (D.fromSpecResidueField (p j)).ker)
  (he : ∀ j, ((J j).val.comap e).IsEffectiveCartier)
  [hDec : ∀ j, Decidable (p j ∈ Set.range e)]

local notation "T" => WithBoundary.toTower (Sigma.snd (alongBoundary i J))
local notation "jCurve" => e ≫ WithBoundary.boundaryι (Sigma.snd (alongBoundary i J))

include hk hCurve hProj heClosed hp hJ he in
/-- The degree on the lifted boundary curve differs from the degree on the original
curve by the sum of the exceptional coefficients at centers on the curve. -/
theorem intersectionNumber_picardHom_alongBoundary (a : LineBundleClass X) (b : Fin n → ℤ) :
    intersectionNumber k (jCurve) ((T).picardHom (Additive.ofMul a, b)).toMul =
      intersectionNumber k (e ≫ i) a +
        ∑ j ∈ Finset.univ.filter (fun j ↦ p j ∈ Set.range e), b j := by
  have : RelativeDimensionLE 1 (C ↘ Spec (CommRingCat.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  have := Scheme.Modules.moduleFinite_cohomology_of_isProjectiveOver k
    (InvertibleSheaf.trivial C).obj 0
  have := Scheme.Modules.moduleFinite_cohomology_of_isProjectiveOver k
    (InvertibleSheaf.trivial C).obj 1
  let degree : LineBundleClass C →* Multiplicative ℤ :=
    MonoidHom.mk' (fun L ↦ Multiplicative.ofAdd (eulerDegree k L))
      (fun L M ↦ congrArg Multiplicative.ofAdd (eulerDegree_mul_of_isIntegral k L M))
  have hdegree (j : Fin n) :
      eulerDegree k (pullback e (mk (J j).property.toInvertibleSheaf)) =
        if p j ∈ Set.range e then -1 else 0 := by
    rw [(J j).property.pullback_mk_toInvertibleSheaf (he j)]
    let hj : ((D.fromSpecResidueField (p j)).ker.comap e).IsEffectiveCartier := hJ j ▸ he j
    rw [mk_toInvertibleSheaf_congr (he j) hj (congrArg (fun I ↦ I.comap e) (hJ j))]
    exact eulerDegree_mk_comap_point k e (p j) (hp j) hj
  simp only [intersectionNumber_def, ← pullback_comp, pullback_picardHom_alongBoundary,
    toMul_ofMul, pullback_mul]
  rw [← pullbackHom_apply (f := e) (a := ∏ j : Fin n, _), map_prod,
    eulerDegree_mul_of_isIntegral, add_right_inj, Finset.sum_filter]
  simp only [pullbackHom_apply, pullback_zpow]
  -- Use the multiplicative degree homomorphism to evaluate the product and powers.
  change (degree (∏ j, pullback e (mk (J j).property.toInvertibleSheaf) ^ (-b j))).toAdd = _
  rw [map_prod, toAdd_prod]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_zpow, toAdd_zpow, zsmul_eq_mul, degree, MonoidHom.mk'_apply,
    toAdd_ofAdd, hdegree]
  split <;> simp_all

include hk hCurve hProj heClosed hp hJ he in
/-- If the class with exceptional coefficients `-m` is nef, the sum of its base
multiplicities on the boundary curve is bounded by the original intersection number. -/
theorem sum_baseMultiplicity_le_boundaryIntersection (f : X ⟶ Spec (.of k))
    (hbase : C ↘ Spec (.of k) = (e ≫ i) ≫ f) (a : LineBundleClass X) (m : Fin n → ℤ)
    (hnef : ((T).picardHom (Additive.ofMul a, fun j ↦ -m j)).toMul.IsNef k ((T).toBase ≫ f)) :
    (∑ j ∈ Finset.univ.filter (fun j ↦ p j ∈ Set.range e), m j) ≤
      intersectionNumber k (e ≫ i) a := by
  have hfinal : C ↘ Spec (.of k) = (jCurve) ≫ (T).toBase ≫ f := by
    simpa only [Category.assoc, WithBoundary.boundaryι_toBase_assoc] using hbase
  have h := hnef.intersectionNumber_nonneg (jCurve) hfinal
  rw [intersectionNumber_picardHom_alongBoundary k e i J p hp hJ he, Finset.sum_neg_distrib] at h
  omega

include hk hCurve hProj heClosed hp hJ he in
omit hDec in
/-- Two labels above the same boundary curve cannot both have multiplicity strictly greater
than half its original intersection number. This also applies to distinct labels with the
same original center. -/
theorem eq_of_boundaryIntersection_lt_two_mul_baseMultiplicity
    (f : X ⟶ Spec (.of k)) (hbase : C ↘ Spec (.of k) = (e ≫ i) ≫ f)
    (a : LineBundleClass X) (m : Fin n → ℤ)
    (hnef : ((T).picardHom (Additive.ofMul a, fun j ↦ -m j)).toMul.IsNef k ((T).toBase ≫ f))
    (hm : ∀ j, p j ∈ Set.range e → 0 ≤ m j)
    {r s : Fin n} (hr : p r ∈ Set.range e) (hs : p s ∈ Set.range e)
    (hrm : intersectionNumber k (e ≫ i) a < 2 * m r)
    (hsm : intersectionNumber k (e ≫ i) a < 2 * m s) :
    r = s := by
  classical
  by_contra hrs
  have hpair : ({r, s} : Finset (Fin n)) ⊆
      Finset.univ.filter (fun j ↦ p j ∈ Set.range e) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    obtain rfl | rfl := hj <;> simpa
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := m) hpair
    (fun j hj _ ↦ hm j (Finset.mem_filter.mp hj).2)
  rw [Finset.sum_pair hrs] at hle
  have hbound := sum_baseMultiplicity_le_boundaryIntersection k e i J p hp hJ he f hbase a m hnef
  omega

variable (f : X ⟶ Spec (.of k)) [hIntegral : IsIntegral X] [hNoeth : IsNoetherian X]
  [hSmooth : SmoothOfRelativeDimension 2 f]

include hk hCurve hProj heClosed he hIntegral hNoeth hSmooth in
/-- The successive orders of an effective Cartier divisor at the chosen centers on a
boundary curve sum to at most its original intersection with the curve if the final
strict transform has nef positive class. The orders are taken before the corresponding
blowups, including at infinitely near points. -/
theorem sum_neg_strictTransformCoefficients_le_boundaryIntersection
    (hbase : C ↘ Spec (.of k) = (e ≫ i) ≫ f)
    {A : X.IdealSheafData} (hA : A.IsEffectiveCartier) :
    let hT := isClosedPointTower_alongBoundary i J (fun j ↦ ⟨p j, hp j, hJ j⟩)
    let hStrict := hT.isEffectiveCartier_strictTransform f hA
    ((mk hStrict.toInvertibleSheaf)⁻¹).IsNef k ((T).toBase ≫ f) →
      (∑ j ∈ Finset.univ.filter (fun j ↦ p j ∈ Set.range e),
        -hT.strictTransformCoefficients A j) ≤
        intersectionNumber k (e ≫ i) (mk hA.toInvertibleSheaf)⁻¹ := by
  intro hT hStrict hnef
  have hclass := congrArg Additive.toMul (hT.picardMarking_strictTransform f hA)
  simp only [picardMarking_apply, toMul_ofMul] at hclass
  exact sum_baseMultiplicity_le_boundaryIntersection k e i J p hp hJ he f hbase
    (mk hA.toInvertibleSheaf)⁻¹ (fun j ↦ -hT.strictTransformCoefficients A j)
    (by simpa only [neg_neg, hclass] using hnef)

end QPainleve.BlowupTower
