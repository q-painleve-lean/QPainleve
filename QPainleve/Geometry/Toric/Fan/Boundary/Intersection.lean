/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.ProperIntersection
public import QPainleve.Geometry.Toric.BaseChange.Boundary
public import QPainleve.Geometry.Toric.Fan.Picard.FiniteFanScheme

import Mathlib.Data.Set.Card
import QPainleve.Geometry.Toric.Fan.Adjacency
import QPainleve.Geometry.Toric.BaseChange.FiniteType
import TauCeti.AlgebraicGeometry.IdealSheaf.Extension
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-!
# Intersections of toric boundary divisors

On a rank-two regular toric fan, distinct ray divisors are disjoint unless their rays
share a cone. If they do, the intersection is the single reduced distinguished point
of that cone, as a closed subscheme over the coefficient field. In the projective case
this gives the off-diagonal entries of the Picard intersection pairing. The principal character
relations then give the lattice relation involving each ray's self-intersection.

See Fulton, *Introduction to Toric Varieties*, §§3.1 and 5.1.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry (LineBundleClass)
open TauCeti.AlgebraicGeometry.Chow

namespace TauCeti.Toric.Fan

universe u

variable (k : Type u) [Field k] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

section Disjoint

variable (Φ : Fan i) (hΦ : Φ.IsRegular) {ρ τ : Φ.Ray}

private theorem comap_sup_eq_top_of_not_contains (σ : Φ.cones)
    (h : ¬ (ρ.toCone ≤ σ ∧ τ.toCone ≤ σ)) :
    (Φ.rayDivisorIdeal k hΦ ρ ⊔ Φ.rayDivisorIdeal k hΦ τ).comap (Φ.affineChartι k σ) = ⊤ := by
  rcases not_and_or.mp h with hρ | hτ
  · simp [Φ.comap_rayDivisorIdeal_eq_top k hΦ ρ σ hρ]
  · simp [Φ.comap_rayDivisorIdeal_eq_top k hΦ τ σ hτ]

/-- If two ray divisors have no common cone, their scheme-theoretic intersection is empty. -/
theorem sup_rayBoundaryIdeal_eq_top (h : ¬ ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ) :
    Φ.rayDivisorIdeal k hΦ ρ ⊔ Φ.rayDivisorIdeal k hΦ τ = ⊤ := by
  apply ext_of_comap_openCover (Φ.affineChartOpenCover k)
  intro σ
  rw [comap_top]
  exact comap_sup_eq_top_of_not_contains k Φ hΦ σ (fun hh ↦ h ⟨σ, hh⟩)

end Disjoint

variable (Φ : Fan i) (hΦ : Φ.IsRegular) (hN : Module.finrank ℤ N = 2) {ρ τ : Φ.Ray}

include hΦ hN in
private theorem eq_cone_of_two_rays (hne : ρ ≠ τ) {σ σ' : Φ.cones}
    (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ)
    (hρ' : ρ.toCone ≤ σ') (hτ' : τ.toCone ≤ σ') : σ = σ' := by
  exact Subtype.ext ((cone_eq_sup_of_ray_ne_of_le hΦ hN hne hρ hτ).trans
    (cone_eq_sup_of_ray_ne_of_le hΦ hN hne hρ' hτ').symm)

include hN in
private theorem comap_sup_rayBoundaryIdeal_eq_ker (hne : ρ ≠ τ) (σ : Φ.cones)
    (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ) :
    (Φ.rayDivisorIdeal k hΦ ρ ⊔ Φ.rayDivisorIdeal k hΦ τ).comap (Φ.affineChartι k σ) =
      (Spec.map (CommRingCat.ofHom
        (facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) k).toRingHom)).ker := by
  classical
  let r := ρ.toToricRay Φ σ hρ
  let t := τ.toToricRay Φ σ hτ
  have hpair : ({r, t} : Set (ToricRay σ.val)) = Set.univ :=
    Φ.toricRays_eq_pair ((isRegular_iff.1 hΦ) _ σ.property) hN hne hρ hτ
  have hcard : Nat.card (ToricRay σ.val) = Module.finrank ℤ N :=
    (Φ.card_toricRay_eq_two_of_ray_ne_of_le hΦ hN hne hρ hτ).trans hN.symm
  let I := fun r ↦ rayChartIdeal Φ.lattice (Φ.isToricCone σ.property) r k
  have hsup : (⨆ u, I u) = I r ⊔ I t := by
    rw [← iSup_pair, hpair]
    simp
  rw [comap_sup, Φ.comap_rayDivisorIdeal_eq_ofIdealTop k hΦ ρ σ hρ,
    Φ.comap_rayDivisorIdeal_eq_ofIdealTop k hΦ τ σ hτ, Scheme.Hom.ker_Spec_map]
  let f := (Scheme.ΓSpecIso (.of (affineChartRing k Φ.lattice σ.val))).inv.hom
  let e := (equivOfIsAffine (X := affineChart k Φ.lattice σ.val)).symm.toOrderIso
  -- On the affine chart, ideals of global sections compute ideal sheaves and their sup.
  change e ((I r).map f) ⊔ e ((I t).map f) =
    e ((RingHom.ker (facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) k).toRingHom).map f)
  rw [← e.map_sup, ← Ideal.map_sup, ← hsup,
    iSup_rayChartIdeal_eq_ker_facePointAlgebraHom k Φ.lattice _
      (isRegular_iff.1 hΦ _ σ.property) hcard]

include hN in
/-- The scheme-theoretic intersection of distinct ray divisors in a common cone is the
reduced distinguished point of that cone. -/
theorem sup_rayBoundaryIdeal_eq_ker_distinguishedPoint (hne : ρ ≠ τ) (σ : Φ.cones)
    (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ) :
    Φ.rayDivisorIdeal k hΦ ρ ⊔ Φ.rayDivisorIdeal k hΦ τ =
      (Φ.distinguishedSection (R := k) σ).ker := by
  rw [Φ.distinguishedSection_def (R := k)]
  let J := Φ.rayDivisorIdeal k hΦ ρ ⊔ Φ.rayDivisorIdeal k hΦ τ
  let j := Φ.affineChartι k σ
  have hsupport : (J.support : Set (Φ.finiteFanScheme k)) ⊆ Set.range j := by
    intro x hx
    obtain ⟨σ', y, rfl⟩ := Φ.exists_affineChartι_apply_eq k x
    suffices σ' = σ by subst σ'; exact ⟨y, rfl⟩
    have hy : y ∈ (J.comap (Φ.affineChartι k σ')).support := by
      rwa [support_comap]
    by_contra hne'
    have ht := comap_sup_eq_top_of_not_contains k Φ hΦ σ' (ρ := ρ) (τ := τ)
      (fun hh ↦ hne' (eq_cone_of_two_rays Φ hΦ hN hne hh.1 hh.2 hρ hτ))
    rw [ht, support_top] at hy
    exact hy
  let f := IsOpenImmersion.lift j J.subschemeι (by rwa [range_subschemeι])
  have hf : f ≫ j = J.subschemeι := IsOpenImmersion.lift_fac _ _ _
  have hj : J = (J.comap j).map j := by
    rw [← J.ker_subschemeι, ← hf, Scheme.Hom.ker_comp, comap_map_of_isOpenImmersion]
  refine hj.trans ?_
  rw [comap_sup_rayBoundaryIdeal_eq_ker k Φ hΦ hN hne σ hρ hτ, map_ker]

private theorem isIso_comp_structureMap_of_ker_eq_distinguishedPoint
    {Z : Scheme.{u}} (g : Z ⟶ (Φ.finiteFanScheme k)) [IsClosedImmersion g] (σ : Φ.cones)
    (h : g.ker = (Φ.distinguishedSection (R := k) σ).ker) :
    IsIso (g ≫ (Φ.finiteFanSchemeToSpec k)) := by
  let p := Φ.distinguishedSection (R := k) σ
  have hp := Φ.distinguishedSection_comp_finiteFanSchemeToSpec (R := k) σ
  let e := IsClosedImmersion.lift p g h.ge
  have he : e ≫ p = g := IsClosedImmersion.lift_fac _ _ _
  have : IsIso e := IsClosedImmersion.isIso_of_ker_eq g p e he h
  rw [← he, Category.assoc, hp, Category.comp_id]
  infer_instance

variable [Infinite k]

include hN in
open Classical in
/-- On a projective regular toric surface, distinct ray classes have intersection number one
when their rays lie in a common cone, and zero otherwise. -/
theorem classIntersectionNumber_rayBoundaryPoint [(Φ.finiteFanScheme k).IsProjectiveOver k]
    (hne : ρ ≠ τ) :
    letI : Nonempty Φ.cones := ⟨ρ.toCone⟩
    letI := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := k) hΦ
    classIntersectionNumber k (Φ.finiteFanScheme k)
        (LineBundleClass.primeDivisorClass (Φ.rayBoundaryChartPoint (R := k) hΦ ρ))
        (LineBundleClass.primeDivisorClass (Φ.rayBoundaryChartPoint (R := k) hΦ τ)) =
      if ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ then 1 else 0 := by
  classical
  let X := (Φ.finiteFanScheme k)
  let I : X.IdealSheafData :=
    vanishingIdeal ⟨closure {(Φ.rayBoundaryChartPoint (R := k) hΦ ρ).val}, isClosed_closure⟩
  let J : X.IdealSheafData :=
    vanishingIdeal ⟨closure {(Φ.rayBoundaryChartPoint (R := k) hΦ τ).val}, isClosed_closure⟩
  have : Nonempty Φ.cones := ⟨ρ.toCone⟩
  have := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := k) hΦ
  have hdim : topologicalKrullDim X ≤ 2 := by
    have : SmoothOfRelativeDimension 2 (Φ.finiteFanSchemeToSpec k) :=
      hN ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ
    exact (TauCeti.AlgebraicGeometry.relativeDimensionLE_iff_of_field
      (Φ.finiteFanSchemeToSpec k)).mp inferInstance
  have hpq := (Φ.rayBoundaryChartPoint_injective (R := k) hΦ).ne hne
  split_ifs with h
  · obtain ⟨σ, hρ, hτ⟩ := h
    let K := I.comap J.subschemeι
    let g := K.subschemeι ≫ J.subschemeι
    have hg : g.ker = I ⊔ J := by simp [g, K, Scheme.Hom.ker_comp]
    have hg' := hg.trans (by
      simpa only [rayDivisorIdeal_def k] using
        Φ.sup_rayBoundaryIdeal_eq_ker_distinguishedPoint k hΦ hN hne σ hρ hτ)
    have : IsIso (K.subscheme ↘ Spec (.of k)) := by
      rw [over_eq_subschemeι_comp, over_eq_subschemeι_comp, Fan.finiteFanScheme_over k,
        ← Category.assoc]
      exact isIso_comp_structureMap_of_ker_eq_distinguishedPoint k Φ g σ hg'
    have hrank := Scheme.Hom.finrank_eq_one_of_isIso (K.subscheme ↘ Spec (.of k))
    rw [LineBundleClass.primeDivisorClass_def,
      LineBundleClass.primeDivisorClass_def,
      classIntersectionNumber_eq_finrank_intersection k hdim _ _
        (IsEffectiveCartier.comap_subschemeι_vanishingIdeal_closure_singleton_of_ne
          (isEffectiveCartier_vanishingIdeal_closure_singleton
            (Φ.rayBoundaryChartPoint (R := k) hΦ ρ).property)
          hpq.symm) default]
    have hr : (K.subscheme ↘ Spec (.of k)).finrank default = 1 := congrFun hrank _
    rw [hr, Nat.cast_one]
  · have htop : I ⊔ J = ⊤ := by
      simpa only [rayDivisorIdeal_def k] using Φ.sup_rayBoundaryIdeal_eq_top k hΦ h
    let hI := isEffectiveCartier_vanishingIdeal_closure_singleton
      (Φ.rayBoundaryChartPoint (R := k) hΦ ρ).property
    let hJ := isEffectiveCartier_vanishingIdeal_closure_singleton
      (Φ.rayBoundaryChartPoint (R := k) hΦ τ).property
    let hIJ := IsEffectiveCartier.comap_subschemeι_vanishingIdeal_closure_singleton_of_ne
      hI hpq.symm
    have hzero : ¬ ((I.support : Set X) ∩ (J.support : Set X)).Nonempty := by
      rw [← Closeds.coe_inf, ← support_sup, htop, support_top]
      exact Set.not_nonempty_empty
    rw [LineBundleClass.primeDivisorClass_def, LineBundleClass.primeDivisorClass_def]
    apply le_antisymm (le_of_not_gt
      ((classIntersectionNumber_pos_iff_support_inter_nonempty k hdim hI hJ hIJ).not.mpr hzero))
    rw [classIntersectionNumber_eq_finrank_intersection k hdim hI hJ hIJ default]
    exact Int.natCast_nonneg _

include hN in
open Classical in
/-- The self-intersection of a ray divisor gives the integral relation between its
primitive generator and those of the distinct rays sharing a cone with it. -/
theorem rayBoundaryPoint_selfIntersection_smul_add_sum_eq_zero
    [(Φ.finiteFanScheme k).IsProjectiveOver k] [Fintype Φ.Ray] (ρ : Φ.Ray) :
    letI : Nonempty Φ.cones := ⟨ρ.toCone⟩
    letI := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := k) hΦ
    let D := LineBundleClass.primeDivisorClass (Φ.rayBoundaryChartPoint (R := k) hΦ ρ)
    classIntersectionNumber k (Φ.finiteFanScheme k) D D • ρ.primitiveGenerator +
      ∑ τ ∈ Finset.univ.filter (fun τ : Φ.Ray ↦
        ρ ≠ τ ∧ ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ), τ.primitiveGenerator = 0 := by
  classical
  let X := (Φ.finiteFanScheme k)
  intro D
  have : Nonempty Φ.cones := ⟨ρ.toCone⟩
  have := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := k) hΦ
  have : Nonempty X := ⟨(Φ.rayBoundaryChartPoint (R := k) hΦ ρ).val⟩
  have : SmoothOfRelativeDimension 2 (Φ.finiteFanSchemeToSpec k) :=
    hN ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ
  have hdim : topologicalKrullDim X = 2 :=
    TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension
      (Φ.finiteFanSchemeToSpec k)
  have := Φ.lattice.free
  let b := Module.Free.chooseBasis ℤ N
  apply b.ext_elem_iff.mpr
  intro j
  let m := (b.coord j).toAddMonoidHom
  let f := classIntersectionBilinForm k hdim (Additive.ofMul D)
  have hPic : Φ.rayChartDivisorToPicard (R := k) hΦ (Φ.characterToRayDivisor m) = 0 :=
    (Φ.exact_characterToRayDivisor_rayChartDivisorToPicard (R := k) hΦ _).mpr ⟨m, rfl⟩
  rw [Φ.rayChartDivisorToPicard_apply (R := k)] at hPic
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
    rw [Φ.classIntersectionNumber_rayBoundaryPoint k hΦ hN hne]
    by_cases h : ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ <;> simp [h, hne, m]

end TauCeti.Toric.Fan
