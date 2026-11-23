/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.ProperIntersection
public import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
public import QPainleve.Geometry.Toric.Fan.Picard.Basic
public import TauCeti.Geometry.Toric.Analytic.Cone.Orbit.Basic

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Set.Card
import QPainleve.Geometry.Toric.Fan.Adjacency
import QPainleve.Geometry.Toric.Fan.Picard.Presentation
import QPainleve.Geometry.Toric.Fan.Point
import QPainleve.Geometry.Toric.Fan.Smooth
import TauCeti.AlgebraicGeometry.IdealSheaf.Extension
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-!
# Intersections of toric boundary divisors

On a rank-two regular toric fan, distinct ray divisors are disjoint unless their rays
share a cone. If they do, the intersection is the single reduced distinguished point
of that cone, as a closed subscheme over `ℂ`. On a projective fan scheme this gives
the off-diagonal entries of the Picard intersection pairing. The principal character
relations then give the lattice relation involving each ray's self-intersection.

The calculation uses the monomial values of Tau Ceti's `Toric.distinguishedPoint`.
See Fulton, *Introduction to Toric Varieties*, §§3.1 and 5.1.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry (LineBundleClass)
open TauCeti.AlgebraicGeometry.Chow

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

private theorem exists_pos_primitiveGenerator_of_ne_zero
    (hi : IsIntegralLattice i) (hσ : IsToricCone i σ) (hreg : IsRegularCone i σ)
    (hfull : Nat.card (ToricRay σ) = Module.finrank ℤ N)
    {m : dualSemigroup hi σ} (hm : m ≠ 0) :
    ∃ r : ToricRay σ, 0 < (m : N →+ ℤ) (primitiveGenerator hi hσ r) := by
  classical
  obtain ⟨l, b, hb⟩ := hreg.exists_basis_sum
  have := ToricRay.finite_of_fg hσ.fg
  have hl : l = 0 := by
    rw [Module.finrank_eq_nat_card_basis b, Nat.card_sum, Nat.card_fin] at hfull
    omega
  by_contra! h
  have hzero : ∀ r : ToricRay σ, (m : N →+ ℤ) (primitiveGenerator hi hσ r) = 0 := by
    intro r
    refine le_antisymm (h r) ?_
    have hnonneg := (mem_dualSemigroup hi _).mp m.property
      (r.val.isFaceOf.le (primitiveGenerator_mem hi hσ r))
    exact_mod_cast (hi.realCharacter_apply _ _ ▸ hnonneg)
  apply hm
  apply Subtype.ext
  apply AddMonoidHom.toIntLinearMap_injective
  apply b.ext
  rintro (r | j)
  · simpa only [AddMonoidHom.coe_toIntLinearMap, AddSubmonoid.coe_zero,
      AddMonoidHom.zero_apply, (hb r).eq_primitiveGenerator hi hσ] using hzero r
  · exact (Nat.not_lt_zero j.val (hl ▸ j.isLt)).elim

/-- In a full-rank regular cone the sum of the ray ideals is the kernel of evaluation
at the distinguished point of the cone. -/
theorem iSup_rayIdeal_eq_ker_distinguishedPoint (hi : IsIntegralLattice i)
    (hσ : IsToricCone i σ) (hreg : IsRegularCone i σ)
    (hfull : Nat.card (ToricRay σ) = Module.finrank ℤ N) :
    (⨆ r : ToricRay σ, rayIdeal hi hσ r) =
      RingHom.ker (distinguishedPoint hi (⊤ : σ.Face)).toRingHom := by
  classical
  let J := ⨆ r : ToricRay σ, rayIdeal hi hσ r
  let d := distinguishedPoint hi (⊤ : σ.Face)
  let q := Ideal.Quotient.mkₐ ℂ J
  have hcomp : q = (Algebra.ofId ℂ _).comp d := by
    apply MonoidAlgebra.algHom_ext
    · intro m
      let a := m.toAdd
      by_cases ha : a = 0
      · have hm : m = 1 := toAdd.injective ha
        rw [hm, ← MonoidAlgebra.one_def]
        simp
      · obtain ⟨r, hr⟩ := exists_pos_primitiveGenerator_of_ne_zero hi hσ hreg hfull ha
        have hmem : MonoidAlgebra.single m (1 : ℂ) ∈ J :=
          le_iSup (rayIdeal hi hσ) r (monomial_mem_rayIdeal hi hσ r a hr)
        have hd : d (MonoidAlgebra.single m 1) = 0 := by
          simpa only [d, a, ofAdd_toAdd] using
            distinguishedPoint_top_single_eq_zero_of_pos hi hσ r a hr
        rw [AlgHom.comp_apply, hd, map_zero]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    · ext
  refine le_antisymm (iSup_le fun r ↦ (rayIdeal_le_iff hi hσ r _).mpr ?_) ?_
  · intro m hm
    rw [MonoidAlgebra.of_apply, RingHom.mem_ker]
    exact distinguishedPoint_top_single_eq_zero_of_pos hi hσ r m hm
  · intro x hx
    have hd : d x = 0 := RingHom.mem_ker.mp hx
    have hq : q x = 0 := by rw [hcomp, AlgHom.comp_apply, hd, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq

namespace Fan

section Disjoint

variable (Φ : Fan i) (hΦ : Φ.IsRegular) {ρ τ : Φ.Ray}

private theorem comap_sup_eq_top_of_not_contains (σ : Φ.cones)
    (h : ¬ (ρ.toCone ≤ σ ∧ τ.toCone ≤ σ)) :
    (Φ.rayBoundaryIdeal hΦ ρ ⊔ Φ.rayBoundaryIdeal hΦ τ).comap (Φ.affineToricChartι σ) = ⊤ := by
  rcases not_and_or.mp h with hρ | hτ
  · simp [Φ.comap_rayBoundaryIdeal_eq_top hΦ ρ σ hρ]
  · simp [Φ.comap_rayBoundaryIdeal_eq_top hΦ τ σ hτ]

/-- If two ray divisors have no common cone, their scheme-theoretic intersection is empty. -/
theorem sup_rayBoundaryIdeal_eq_top (h : ¬ ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ) :
    Φ.rayBoundaryIdeal hΦ ρ ⊔ Φ.rayBoundaryIdeal hΦ τ = ⊤ := by
  apply ext_of_comap_openCover Φ.affineToricOpenCover
  intro σ
  rw [comap_top]
  exact comap_sup_eq_top_of_not_contains Φ hΦ σ (fun hh ↦ h ⟨σ, hh⟩)

end Disjoint

variable {N : Type} [AddCommGroup N] {i : N →+ V}
  (Φ : Fan i) (hΦ : Φ.IsRegular) (hN : Module.finrank ℤ N = 2) {ρ τ : Φ.Ray}

include hΦ hN in
private theorem eq_cone_of_two_rays (hne : ρ ≠ τ) {σ σ' : Φ.cones}
    (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ)
    (hρ' : ρ.toCone ≤ σ') (hτ' : τ.toCone ≤ σ') : σ = σ' := by
  exact Subtype.ext ((cone_eq_sup_of_ray_ne_of_le hΦ hN hne hρ hτ).trans
    (cone_eq_sup_of_ray_ne_of_le hΦ hN hne hρ' hτ').symm)

include hN in
private theorem comap_sup_rayBoundaryIdeal_eq_ker (hne : ρ ≠ τ) (σ : Φ.cones)
    (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ) :
    (Φ.rayBoundaryIdeal hΦ ρ ⊔ Φ.rayBoundaryIdeal hΦ τ).comap (Φ.affineToricChartι σ) =
      (Spec.map (CommRingCat.ofHom (distinguishedPoint Φ.lattice
        (⊤ : σ.val.Face)).toRingHom)).ker := by
  classical
  let r := ρ.toToricRay Φ σ hρ
  let t := τ.toToricRay Φ σ hτ
  have hpair : ({r, t} : Set (ToricRay σ.val)) = Set.univ :=
    Φ.toricRays_eq_pair ((isRegular_iff.1 hΦ) _ σ.property) hN hne hρ hτ
  have hcard : Nat.card (ToricRay σ.val) = Module.finrank ℤ N :=
    (Φ.card_toricRay_eq_two_of_ray_ne_of_le hΦ hN hne hρ hτ).trans hN.symm
  let I := rayIdeal Φ.lattice (Φ.isToricCone σ.property)
  have hsup : (⨆ u, I u) = I r ⊔ I t := by
    rw [← iSup_pair, hpair]
    simp
  rw [comap_sup, Φ.comap_rayBoundaryIdeal_eq_ofIdealTop hΦ ρ σ hρ,
    Φ.comap_rayBoundaryIdeal_eq_ofIdealTop hΦ τ σ hτ, Scheme.Hom.ker_Spec_map]
  let f := (Scheme.ΓSpecIso (.of (affineCoordinateRing Φ.lattice σ.val))).inv.hom
  let e := (equivOfIsAffine (X := Φ.affineToricChart σ)).symm.toOrderIso
  -- On the affine chart, ideals of global sections compute ideal sheaves and their sup.
  change e ((I r).map f) ⊔ e ((I t).map f) =
    e ((RingHom.ker (distinguishedPoint Φ.lattice (⊤ : σ.val.Face)).toRingHom).map f)
  rw [← e.map_sup, ← Ideal.map_sup, ← hsup,
    iSup_rayIdeal_eq_ker_distinguishedPoint Φ.lattice _ (isRegular_iff.1 hΦ _ σ.property) hcard]

include hN in
/-- The scheme-theoretic intersection of distinct ray divisors in a common cone is the
reduced distinguished point of that cone. -/
theorem sup_rayBoundaryIdeal_eq_ker_distinguishedPoint (hne : ρ ≠ τ) (σ : Φ.cones)
    (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ) :
    Φ.rayBoundaryIdeal hΦ ρ ⊔ Φ.rayBoundaryIdeal hΦ τ =
      (Spec.map (CommRingCat.ofHom (distinguishedPoint Φ.lattice (⊤ : σ.val.Face)).toRingHom) ≫
        Φ.affineToricChartι σ).ker := by
  let J := Φ.rayBoundaryIdeal hΦ ρ ⊔ Φ.rayBoundaryIdeal hΦ τ
  let j := Φ.affineToricChartι σ
  have hsupport : (J.support : Set Φ.algebraicRealization) ⊆ Set.range j := by
    intro x hx
    obtain ⟨σ', y, rfl⟩ := Φ.exists_affineToricChartι_apply_eq x
    suffices σ' = σ by subst σ'; exact ⟨y, rfl⟩
    have hy : y ∈ ((J.comap (Φ.affineToricChartι σ')).support : Set (Φ.affineToricChart σ')) := by
      rwa [support_comap]
    by_contra hne'
    have ht := comap_sup_eq_top_of_not_contains Φ hΦ σ' (ρ := ρ) (τ := τ)
      (fun hh ↦ hne' (eq_cone_of_two_rays Φ hΦ hN hne hh.1 hh.2 hρ hτ))
    rw [ht, support_top] at hy
    exact hy
  let f := IsOpenImmersion.lift j J.subschemeι (by rwa [range_subschemeι])
  have hf : f ≫ j = J.subschemeι := IsOpenImmersion.lift_fac _ _ _
  have hj : J = (J.comap j).map j := by
    rw [← J.ker_subschemeι, ← hf, Scheme.Hom.ker_comp, comap_map_of_isOpenImmersion]
  refine hj.trans ?_
  rw [comap_sup_rayBoundaryIdeal_eq_ker Φ hΦ hN hne σ hρ hτ, map_ker]

private theorem isIso_comp_structureMap_of_ker_eq_distinguishedPoint
    {Z : Scheme} (g : Z ⟶ Φ.algebraicRealization) [IsClosedImmersion g] (σ : Φ.cones)
    (h : g.ker =
      (Spec.map (CommRingCat.ofHom (distinguishedPoint Φ.lattice (⊤ : σ.val.Face)).toRingHom) ≫
        Φ.affineToricChartι σ).ker) :
    IsIso (g ≫ Φ.algebraicRealizationStructureMap) := by
  let d := distinguishedPoint Φ.lattice (⊤ : σ.val.Face)
  let p := Spec.map (CommRingCat.ofHom d.toRingHom) ≫ Φ.affineToricChartι σ
  have hp : p ≫ Φ.algebraicRealizationStructureMap = 𝟙 _ := by
    rw [Category.assoc, Φ.affineToricChartι_comp_algebraicRealizationStructureMap,
      ← Spec.map_comp, ← Spec.map_id]
    apply congrArg Spec.map
    ext c
    exact d.commutes c
  have : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id _ _ hp
  let e := IsClosedImmersion.lift p g h.ge
  have he : e ≫ p = g := IsClosedImmersion.lift_fac _ _ _
  have : IsIso e := IsClosedImmersion.isIso_of_ker_eq g p e he h
  rw [← he, Category.assoc, hp, Category.comp_id]
  infer_instance

include hN in
open Classical in
/-- On a projective regular toric surface, distinct ray classes have intersection number one
when their rays lie in a common cone, and zero otherwise. -/
theorem classIntersectionNumber_rayBoundaryPoint [Φ.algebraicRealization.IsProjectiveOver ℂ]
    (hne : ρ ≠ τ) :
    letI : Nonempty Φ.cones := ⟨ρ.toCone⟩
    letI := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
    classIntersectionNumber ℂ Φ.algebraicRealization
        (LineBundleClass.primeDivisorClass (Φ.rayBoundaryPoint hΦ ρ))
        (LineBundleClass.primeDivisorClass (Φ.rayBoundaryPoint hΦ τ)) =
      if ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ then 1 else 0 := by
  classical
  let X := Φ.algebraicRealization
  let I : X.IdealSheafData :=
    vanishingIdeal ⟨closure {(Φ.rayBoundaryPoint hΦ ρ).val}, isClosed_closure⟩
  let J : X.IdealSheafData :=
    vanishingIdeal ⟨closure {(Φ.rayBoundaryPoint hΦ τ).val}, isClosed_closure⟩
  have : Nonempty Φ.cones := ⟨ρ.toCone⟩
  have := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have hdim : topologicalKrullDim X ≤ 2 := by
    have : SmoothOfRelativeDimension 2 Φ.algebraicRealizationStructureMap :=
      hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    exact (TauCeti.AlgebraicGeometry.relativeDimensionLE_iff_of_field
      Φ.algebraicRealizationStructureMap).mp inferInstance
  have hpq := (Φ.rayBoundaryPoint_injective hΦ).ne hne
  split_ifs with h
  · obtain ⟨σ, hρ, hτ⟩ := h
    let K := I.comap J.subschemeι
    let g := K.subschemeι ≫ J.subschemeι
    have hg : g.ker = I ⊔ J := by simp [g, K, Scheme.Hom.ker_comp]
    have hg' := hg.trans (by
      simpa only [rayBoundaryIdeal_def] using
        Φ.sup_rayBoundaryIdeal_eq_ker_distinguishedPoint hΦ hN hne σ hρ hτ)
    have : IsIso (K.subscheme ↘ Spec (.of ℂ)) := by
      rw [over_eq_subschemeι_comp, over_eq_subschemeι_comp, Fan.algebraicRealization_over,
        ← Category.assoc]
      exact isIso_comp_structureMap_of_ker_eq_distinguishedPoint Φ g σ hg'
    have hrank := Scheme.Hom.finrank_eq_one_of_isIso (K.subscheme ↘ Spec (.of ℂ))
    rw [LineBundleClass.primeDivisorClass_def,
      LineBundleClass.primeDivisorClass_def,
      classIntersectionNumber_eq_finrank_intersection ℂ hdim _ _
        (IsEffectiveCartier.comap_subschemeι_vanishingIdeal_closure_singleton_of_ne
          (isEffectiveCartier_vanishingIdeal_closure_singleton (Φ.rayBoundaryPoint hΦ ρ).property)
          hpq.symm) default]
    have hr : (K.subscheme ↘ Spec (.of ℂ)).finrank default = 1 := congrFun hrank _
    rw [hr, Nat.cast_one]
  · have htop : I ⊔ J = ⊤ := by
      simpa only [rayBoundaryIdeal_def] using Φ.sup_rayBoundaryIdeal_eq_top hΦ h
    rw [classIntersectionNumber_primeDivisorClass_eq_finsum_length ℂ hdim hpq]
    refine (finsum_congr (g := fun _ ↦ (0 : ℤ)) fun x ↦ ?_).trans (by simp)
    have ht : I.stalkIdeal x ⊔ J.stalkIdeal x = ⊤ := by rw [← stalkIdeal_sup, htop, stalkIdeal_top]
    rw [ht]
    simp [Module.length_eq_zero]

include hN in
open Classical in
/-- The self-intersection of a ray divisor gives the integral relation between its
primitive generator and those of the distinct rays sharing a cone with it. -/
theorem rayBoundaryPoint_selfIntersection_smul_add_sum_eq_zero
    [Φ.algebraicRealization.IsProjectiveOver ℂ] [Fintype Φ.Ray] (ρ : Φ.Ray) :
    letI : Nonempty Φ.cones := ⟨ρ.toCone⟩
    letI := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
    let D := LineBundleClass.primeDivisorClass (Φ.rayBoundaryPoint hΦ ρ)
    classIntersectionNumber ℂ Φ.algebraicRealization D D • ρ.primitiveGenerator +
      ∑ τ ∈ Finset.univ.filter (fun τ : Φ.Ray ↦
        ρ ≠ τ ∧ ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ), τ.primitiveGenerator = 0 := by
  classical
  let X := Φ.algebraicRealization
  intro D
  have : Nonempty Φ.cones := ⟨ρ.toCone⟩
  have := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have : Nonempty X := ⟨(Φ.rayBoundaryPoint hΦ ρ).val⟩
  have : SmoothOfRelativeDimension 2 Φ.algebraicRealizationStructureMap :=
    hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  have hdim : topologicalKrullDim X = 2 :=
    TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension
      Φ.algebraicRealizationStructureMap
  have := Φ.lattice.free
  let b := Module.Free.chooseBasis ℤ N
  apply b.ext_elem_iff.mpr
  intro j
  let m := (b.coord j).toAddMonoidHom
  let f := classIntersectionBilinForm ℂ hdim (Additive.ofMul D)
  have hPic : Φ.rayDivisorToPicard hΦ (Φ.characterToRayDivisor m) = 0 :=
    (Φ.exact_characterToRayDivisor_rayDivisorToPicard hΦ _).mpr ⟨m, rfl⟩
  rw [Φ.rayDivisorToPicard_apply] at hPic
  have hz := congrArg f hPic
  simp only [map_sum, map_zsmul, map_zero, Int.zsmul_eq_mul, f,
    classIntersectionBilinForm_apply, toMul_ofMul, characterToRayDivisor_apply] at hz
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ρ)] at hz
  -- Evaluate the representation coordinate using the basis's bundled linear map.
  change b.coord j (_ + _) = b.coord j 0
  simp only [map_add, map_zsmul, map_sum, map_zero, Int.zsmul_eq_mul]
  rw [← hz]
  congr 1
  · exact mul_comm _ _
  · rw [Finset.sum_filter, ← Finset.sum_erase_add _ _ (Finset.mem_univ ρ)]
    simp only [ne_self_iff_false, false_and, ite_false, add_zero]
    apply Finset.sum_congr rfl
    intro τ hτ
    have hne : ρ ≠ τ := Ne.symm (Finset.mem_erase.mp hτ).1
    rw [Φ.classIntersectionNumber_rayBoundaryPoint hΦ hN hne]
    by_cases h : ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ <;> simp [h, hne, m]

end Fan

end TauCeti.Toric
