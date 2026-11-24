/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.RankOne
public import QPainleve.AlgebraicGeometry.Curves.GenusZero
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.TwistingSheaf
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Basic

import QPainleve.AlgebraicGeometry.Chow.PrimeDivisor
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Effectivity
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Effectivity
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Twist
import QPainleve.AlgebraicGeometry.IdealSheaf.Tensor.Restriction
import QPainleve.AlgebraicGeometry.IntersectionNumber.Ample
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Cohomology
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.GlobalGeneration
import TauCeti.AlgebraicGeometry.LineBundle.BaseChange

/-!
# The plane linear system on a rational surface

The ample generator of the Picard group of a rank-one rational surface cuts out
projective lines. Its complete linear system is base-point-free, has three
independent sections, and defines a finite morphism to the projective plane.
The section calculation applies to any ample line bundle of square one and
canonical intersection minus three.

See [Vakil, *Complex Algebraic Surfaces*, Class 17, §2][Vakil], for the use of
the complete linear system of a rational curve in the classification of minimal
rational surfaces.

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass17A.pdf
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace QPainleve
open Scheme.IdealSheafData Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open LineBundleClass

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [hRat : Scheme.IsRationalOver (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "K" => LineBundleClass.mk (canonicalBundle k X 2)
local notation "B" => Chow.classIntersectionNumber k X
local notation "O(" h ")" => InvertibleSheaf.dual (IsEffectiveCartier.toInvertibleSheaf h)

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {I : X.IdealSheafData}

include hRat in
/-- An effective Cartier divisor of ample class, square one and canonical degree
minus three on a smooth projective rational surface is a projective line over the
base field. The statement concerns the full divisor scheme. -/
theorem exists_iso_projectiveLine_of_isAmple_of_self_eq_one (hI : I.IsEffectiveCartier)
    (hA : (LineBundleClass.mk (O(hI))).IsAmple)
    (hsq : B (LineBundleClass.mk (O(hI))) (LineBundleClass.mk (O(hI))) = 1)
    (hcan : B (LineBundleClass.mk (O(hI))) K = -3) :
    ∃ e : I.subscheme ≅ projectiveLine k, e.hom.IsOver S := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := hRat.isIntegral_of_smooth
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  have : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  simp only [← inv_mk] at hA hsq hcan
  obtain ⟨p, hp⟩ := hI.exists_eq_vanishingIdeal_of_classIntersectionNumber_eq_one k hX hA hsq
  have : IsIntegral I.subscheme := hp ▸ isIntegral_subscheme_vanishingIdeal_closure_singleton p.val
  have : I.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
  have : I.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, hp ▸ topologicalKrullDim_vanishingIdeal_subscheme k hX p⟩
  have hg := I.subschemeι.two_mul_genus_sub_two_eq_intersection_of_isRationalOver k
  dsimp only at hg
  rw [LineBundleClass.mk_toInvertibleSheaf_congr _ hI I.ker_subschemeι, hsq, hcan] at hg
  exact genus_eq_zero_iff_exists_iso_projectiveLine.mp (by omega)

omit hRat in
/-- The ample class of a square-one Cartier divisor restricts to degree one on
any chosen projective-line identification of the divisor. -/
private theorem intersectionNumber_dual_eq_one_of_iso_projectiveLine
    (hI : I.IsEffectiveCartier) (e : projectiveLine k ≅ I.subscheme)
    [e.hom.IsOver S] (hsq : B (LineBundleClass.mk (O(hI))) (LineBundleClass.mk (O(hI))) = 1) :
    intersectionNumber k (e.hom ≫ I.subschemeι) (LineBundleClass.mk (O(hI))) = 1 := by
  have : IsIntegral I.subscheme := IsIntegral.of_isIso e.hom
  have : Nonempty X := Nonempty.map I.subschemeι inferInstance
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have hdim : topologicalKrullDim I.subscheme = 1 :=
    e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.symm.trans
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := projectiveLine k) k)
  rw [← intersectionNumber_pullback, intersectionNumber_def,
    eulerDegree_pullback_of_isIso e.hom (HomIsOver.comp_over (f := e.hom)),
    ← intersectionNumber_def,
    ← Chow.classIntersectionNumber_eq_intersectionNumber_subschemeι k hX.le hI hdim,
    inv_mk]
  exact hsq

include hRat in
private theorem subsingleton_cohomology_one_tensor_ideal (hI : I.IsEffectiveCartier) :
    Subsingleton (Cohomology ((O(hI)).obj ⊗ I.sheaf) 1) := by
  have := X.subsingleton_cohomology_trivial_of_isRationalOver k (i := 1) Nat.one_pos
  let e := whiskerRightIso (InvertibleSheaf.tensorTrivialLeftIsoSheaf (O(hI))) I.sheaf
  let d := e.symm ≪≫ hI.tensorDualCancelIso (InvertibleSheaf.trivial X)
  exact (cohomologyBaseLinearEquivOfIso k d 1).injective.subsingleton

include hRat in
private theorem isGloballyGenerated_dual_of_iso_projectiveLine
    (hI : I.IsEffectiveCartier) (e : projectiveLine k ≅ I.subscheme)
    (hdeg : 0 ≤ intersectionNumber k (e.hom ≫ I.subschemeι) (LineBundleClass.mk (O(hI)))) :
    (O(hI)).IsGloballyGenerated := by
  let L := O(hI)
  let M := (InvertibleSheaf.pullback I.subschemeι).obj L
  have hd : 0 ≤ ((InvertibleSheaf.pullback e.hom).obj M).eulerDegree k := by
    rw [← eulerDegree_mk, ← pullback_mk, ← pullback_mk, pullback_comp,
      ← intersectionNumber_def]
    exact hdeg
  have hM := M.isGloballyGenerated_of_nonneg_eulerDegree_projectiveLine e hd
  have hlift := I.surjective_pullbackSectionsLE_of_subsingleton_cohomology_one L
    (hI.subsingleton_cohomology_one_tensor_ideal (k := k))
  refine InvertibleSheaf.isGloballyGenerated_iff.mpr fun x ↦ ?_
  by_cases hx : x ∈ I.support
  · obtain ⟨y, rfl⟩ := I.range_subschemeι.ge hx
    obtain ⟨t, ht⟩ := InvertibleSheaf.isGloballyGenerated_iff.mp hM y
    let a := eqToIso (InvertibleSheaf.pullback_obj_obj I.subschemeι L)
    obtain ⟨s, hs⟩ := hlift (a.hom.app ⊤ t)
    have ht' : y ∈ ((Scheme.Modules.pullback I.subschemeι).obj L.obj).nonvanishingLocus
        (a.hom.app ⊤ t) := by
      rwa [nonvanishingLocus_hom_app]
    rw [← hs, nonvanishingLocus_pullbackSectionsLE, top_inf_eq] at ht'
    exact ⟨s, I.subschemeι.mem_preimage.mp ht'⟩
  · obtain ⟨s, hs⟩ := hI.exists_zeroIdeal_eq_dual
    exact ⟨s, (L.mem_nonvanishingLocus_iff_notMem_support_zeroIdeal s x).mpr (hs.symm ▸ hx)⟩

include hRat in
private theorem finrank_globalSections_dual_eq_three_of_iso_projectiveLine
    (hI : I.IsEffectiveCartier) (e : projectiveLine k ≅ I.subscheme)
    (hdeg : intersectionNumber k (e.hom ≫ I.subschemeι) (LineBundleClass.mk (O(hI))) = 1)
    (hA : (LineBundleClass.mk (O(hI))).IsAmple)
    (hsq : B (LineBundleClass.mk (O(hI))) (LineBundleClass.mk (O(hI))) = 1)
    (hcan : B (LineBundleClass.mk (O(hI))) K = -3) :
    Module.finrank k Γ((O(hI)).obj, ⊤) = 3 := by
  let L := O(hI)
  have hIdeal : Subsingleton (Cohomology (L.obj ⊗ I.sheaf) 1) :=
    hI.subsingleton_cohomology_one_tensor_ideal (k := k)
  have hDivisor : Subsingleton (Cohomology (L.obj ⊗ I.pushforwardSubscheme) 1) :=
    I.subsingleton_cohomology_one_tensor_pushforwardSubscheme_of_projectiveLine L e
      (hdeg ▸ (by decide : (-1 : ℤ) ≤ 1))
  have hmiddle : Subsingleton (Cohomology (L.obj ⊗ 𝟙_ X.Modules) 1) :=
    subsingleton_cohomology_X₂ (I.shortExact_tensor_toPushforwardSubscheme L.obj) 1
      hIdeal hDivisor
  have : Subsingleton (Cohomology L.obj 1) :=
    (cohomologyBaseLinearEquivOfIso k (ρ_ L.obj).symm 1).injective.subsingleton
  have hpos : 0 < B (LineBundleClass.mk L) (LineBundleClass.mk L) := hsq ▸ zero_lt_one
  have := X.subsingleton_cohomology_two_of_self_pos_of_intersection_pos k L hA hpos hpos
  have h₁ : Module.finrank k (Cohomology L.obj 1) = 0 := Module.finrank_zero_of_subsingleton
  have h₂ : Module.finrank k (Cohomology L.obj 2) = 0 := Module.finrank_zero_of_subsingleton
  have hχ := eulerCharBelow_eq_riemannRoch_of_isRationalOver k (LineBundleClass.mk L)
  rw [eulerCharBelow_mk, Scheme.Modules.eulerCharBelow_succ, Scheme.Modules.eulerCharBelow_two,
    finrank_cohomology_zero_eq_finrank_globalSections, h₁, h₂, hsq, hcan] at hχ
  exact_mod_cast (show (Module.finrank k Γ(L.obj, ⊤) : ℤ) = 3 by omega)

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

variable (L : InvertibleSheaf X)

include hRat in
/-- An ample line bundle of square one and canonical degree minus three on a smooth
projective rational surface is globally generated and has exactly three independent
global sections. -/
theorem isGloballyGenerated_and_finrank_globalSections_eq_three_of_self_eq_one
    (hA : (LineBundleClass.mk L).IsAmple)
    (hsq : B (LineBundleClass.mk L) (LineBundleClass.mk L) = 1)
    (hcan : B (LineBundleClass.mk L) K = -3) :
    L.IsGloballyGenerated ∧ Module.finrank k Γ(L.obj, ⊤) = 3 := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := hRat.isIntegral_of_smooth
  have hχ := eulerCharBelow_eq_riemannRoch_of_isRationalOver k (LineBundleClass.mk L)
  have hvan := X.subsingleton_cohomology_two_of_self_pos_of_intersection_pos k L hA
    (by omega) (by omega)
  obtain ⟨I, hI, hclass⟩ := L.exists_effectiveCartier_of_eulerCharBelow_pos k (by omega) hvan
  have hclass' : LineBundleClass.mk (O(hI)) = LineBundleClass.mk L := by
    rw [← inv_mk, hclass, inv_inv]
  obtain ⟨a⟩ := LineBundleClass.mk_eq_mk_iff.mp hclass'
  obtain ⟨e, he⟩ := hI.exists_iso_projectiveLine_of_isAmple_of_self_eq_one
    (hclass'.symm ▸ hA) (hclass'.symm ▸ hsq) (hclass'.symm ▸ hcan)
  have : e.symm.hom.IsOver S := by
    let := he
    exact (inferInstance : e.inv.IsOver S)
  have hdeg := hI.intersectionNumber_dual_eq_one_of_iso_projectiveLine e.symm (hclass'.symm ▸ hsq)
  refine ⟨(isGloballyGenerated_iff_of_iso a).mp
    (hI.isGloballyGenerated_dual_of_iso_projectiveLine e.symm (hdeg ▸ zero_le_one)), ?_⟩
  rw [← finrank_cohomology_zero_eq_finrank_globalSections,
    ← (cohomologyBaseLinearEquivOfIso k a 0).finrank_eq,
    finrank_cohomology_zero_eq_finrank_globalSections]
  exact hI.finrank_globalSections_dual_eq_three_of_iso_projectiveLine e.symm hdeg
    (hclass'.symm ▸ hA) (hclass'.symm ▸ hsq) (hclass'.symm ▸ hcan)

end TauCeti.AlgebraicGeometry.InvertibleSheaf

namespace AlgebraicGeometry.Scheme

variable (k X)

include hRat in
/-- On a smooth projective rational surface of Picard rank one, the ample Picard
generator is globally generated and has a three-dimensional space of sections. -/
theorem exists_ample_picard_generator_linear_system_of_finrank_eq_one
    (hrank : Module.finrank ℤ (Additive (LineBundleClass X)) = 1) :
    ∃ L : InvertibleSheaf X, (LineBundleClass.mk L).IsAmple ∧
      B (LineBundleClass.mk L) (LineBundleClass.mk L) = 1 ∧
      K = (LineBundleClass.mk L) ^ (-3 : ℤ) ∧
      Function.Bijective ((LineBundleClass.mk L) ^ · : ℤ → LineBundleClass X) ∧
      L.IsGloballyGenerated ∧ Module.finrank k Γ(L.obj, ⊤) = 3 := by
  obtain ⟨H, hH, hsq, hK, hgen⟩ := X.exists_ample_picard_generator_of_finrank_eq_one k hrank
  obtain ⟨L, rfl⟩ := LineBundleClass.mk_surjective H
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := hRat.isIntegral_of_smooth
  have : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have hcan : B (LineBundleClass.mk L) K = -3 := by
    let f := Chow.classIntersectionBilinForm k hX (Additive.ofMul (LineBundleClass.mk L))
    have h := map_zsmul f (-3 : ℤ) (Additive.ofMul (LineBundleClass.mk L))
    simpa only [f, ← ofMul_zpow, Chow.classIntersectionBilinForm_apply, toMul_ofMul,
      hK, hsq, zsmul_eq_mul, mul_one, Int.cast_id] using h
  obtain ⟨hglob, hdim⟩ :=
    L.isGloballyGenerated_and_finrank_globalSections_eq_three_of_self_eq_one hH hsq hcan
  exact ⟨L, hH, hsq, hK, hgen, hglob, hdim⟩

attribute [local instance] MvPolynomial.gradedAlgebra

include hRat in
/-- The complete linear system of the ample generator of a rank-one rational surface
gives a finite morphism to the projective plane over the base. Its pullback of
`𝒪(1)` has square one and generates the Picard group. -/
theorem exists_finite_to_projectivePlane_of_finrank_eq_one
    (hrank : Module.finrank ℤ (Additive (LineBundleClass X)) = 1) :
    let 𝒜 := MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 3)) k
    let H : InvertibleSheaf (Proj 𝒜) := ⟨Proj.twistingSheaf 𝒜 1, inferInstance⟩
    ∃ f : X ⟶ Proj 𝒜, f ≫ Proj.toSpecCoeff 𝒜 = X ↘ S ∧ IsFinite f ∧
      let a := LineBundleClass.pullback f (LineBundleClass.mk H)
      a.IsAmple ∧ B a a = 1 ∧ Function.Bijective (a ^ · : ℤ → LineBundleClass X) := by
  intro 𝒜 H
  obtain ⟨L, hA, hsq, -, hgen, hglob, hnum⟩ :=
    X.exists_ample_picard_generator_linear_system_of_finrank_eq_one k hrank
  obtain ⟨f, hf, hfin, ha⟩ := L.exists_finite_to_projectivePlane hA hglob hnum
  refine ⟨f, hf, hfin, ?_⟩
  dsimp only
  rw [ha]
  exact ⟨hA, hsq, hgen⟩

end AlgebraicGeometry.Scheme
