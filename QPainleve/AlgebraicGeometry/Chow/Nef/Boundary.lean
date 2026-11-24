/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Nef.Basic

import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Chow.BoundaryMultiplicity
import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Picard

/-!
# Nef square-zero divisors and their prime classes

The class of a nef effective Cartier divisor has square zero precisely when it is
orthogonal to all the prime curves in its support.

On a smooth projective surface, the Picard classes distinguish the components
of a connected effective Cartier divisor whose class is nef of square zero. This
forces automorphisms acting trivially on the Picard group to fix each component
when they preserve the divisor.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

open TauCeti.AlgebraicGeometry.Chow

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

/-- For a nef effective Cartier divisor, membership of its class in the boundary orthogonal
is equivalent to vanishing self-intersection. -/
theorem effectiveCartierClass_mem_boundaryOrthogonal_iff_of_isNef
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    (hnef : (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹.IsNef k (X ↘ Spec (.of k))) :
    Additive.ofMul (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ ∈ D.boundaryOrthogonal k ↔
      Chow.classIntersectionNumber k X (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹
        (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ = 0 := by
  let f := X ↘ Spec (.of k)
  let : IsNoetherian X := isNoetherian_of_finiteType f
  let := f.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let W := hD.toCartierDivisor.toWeilDivisor
  have hW : 0 ≤ W :=
    (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
      hD.isEffective_toCartierDivisor
  have hclass : (Scheme.CartierDivisor.weilToLineBundleClassHom X W).toMul =
      (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ := by
    rw [Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor, toMul_ofMul,
      hD.toLineBundleClass_toCartierDivisor]
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have h := Chow.classIntersectionNumber_weilToLineBundleClassHom_self_eq_zero_iff
    k hdim hW (hclass.symm ▸ hnef)
  rw [hclass] at h
  let U : X.Opens := D.support.compl
  have hs (p : CodimensionOnePoint X) : p ∈ W.support ↔ (p : X) ∉ U := by
    calc
      p ∈ W.support ↔ W p ≠ 0 := Finsupp.mem_support_iff
      _ ↔ (p : X) ∈ D.support := by
        simpa only [W, WeilDivisor.coeff, not_not] using
          not_congr (hD.coeff_toWeilDivisor_eq_zero_iff p)
      _ ↔ (p : X) ∉ U := not_not.symm
  have hspan := U.primeDivisorSpanCompl_eq_span_of_mem_iff
    (Subtype.val : W.support → CodimensionOnePoint X) fun p ↦ by
      simpa only [Subtype.range_val_subtype, Set.mem_ofPred_eq, Finset.mem_coe] using (hs p).symm
  rw [h, D.boundaryOrthogonal_def k, hspan, LinearMap.BilinForm.orthogonal,
    Submodule.mem_orthogonalBilin_span]
  simp only [Set.forall_mem_range, Subtype.forall, Chow.intersectionBilinForm_apply,
    toMul_ofMul,
    Chow.classIntersectionNumber_comm (b := (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹)]

local notation "s" => (X ↘ Spec (CommRingCat.of k))
local notation "cl" => Scheme.CartierDivisor.weilToLineBundleClassHom X
local notation "b" => classIntersectionNumber k X

/-- The components of a preconnected effective Cartier divisor with nef square-zero
class have distinct Picard classes. This applies also when the divisor has
multiplicities. -/
theorem primeDivisorClass_injOn_of_isPreconnected_of_isNef
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    (hconn : _root_.IsPreconnected (D.support : Set X))
    (hnef : ((LineBundleClass.mk hD.toInvertibleSheaf)⁻¹).IsNef k s)
    (hsq : b (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹
      (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ = 0) :
    letI : IsNoetherian X := isNoetherian_of_finiteType s
    letI : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (s).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    Set.InjOn primeDivisorClass {p : CodimensionOnePoint X | (p : X) ∈ D.support} := by
  classical
  let : IsNoetherian X := isNoetherian_of_finiteType s
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (s).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  intro p hp q hq hclass
  by_contra hne
  have hpq : p ≠ q := hne
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension s (n := 2)
  have : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let W := hD.toCartierDivisor.toWeilDivisor
  have hW : 0 ≤ W := (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
    hD.isEffective_toCartierDivisor
  have hline : (cl W).toMul = (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ := by
    rw [Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor,
      hD.toLineBundleClass_toCartierDivisor, toMul_ofMul]
  have hWD : W.idealSheaf hW = D :=
    (SchemeWeilDivisor.idealSheaf_toWeilDivisor hD.isEffective_toCartierDivisor).trans
      hD.idealSheaf_toCartierDivisor
  have hmem (r : CodimensionOnePoint X) : r ∈ W.support ↔ (r : X) ∈ D.support := by
    rw [Finsupp.mem_support_iff, ← WeilDivisor.coeff, ← hWD]
    exact (not_congr (W.coeff_eq_zero_iff_notMem_support hW r)).trans not_not
  let E : SchemeWeilDivisor X := Finsupp.single p 1 - Finsupp.single q 1
  have hpW := (hmem p).mpr hp
  have hqW := (hmem q).mpr hq
  have hE : E.support ⊆ W.support := by
    intro r hr
    by_contra hrW
    have hrp : r ≠ p := fun h ↦ hrW (h.symm ▸ hpW)
    have hrq : r ≠ q := fun h ↦ hrW (h.symm ▸ hqW)
    exact (Finsupp.mem_support_iff.mp hr) (by
      simp [E, hrp, hrq])
  have hclassE : cl E = 0 := by
    simp only [E, map_sub, Scheme.CartierDivisor.weilToLineBundleClassHom_single,
      ← LineBundleClass.primeDivisorClass_def, one_zsmul, hclass, sub_self]
  have horth (r : CodimensionOnePoint X) (_ : r ∈ W.support) :
      b (cl E).toMul (primeDivisorClass r) = 0 := by
    rw [hclassE, toMul_zero, classIntersectionNumber_one_left]
  -- The difference is orthogonal to the boundary, so its coefficients are proportional to W.
  have hcoeff := mul_coeff_eq_mul_coeff_of_orthogonal_of_nef_square_zero k hX hW
    (hWD.symm ▸ hconn) (hline.symm ▸ hnef) (hline.symm ▸ hsq) hE horth p q
  simp [E, hpq, hpq.symm] at hcoeff
  have hpPos : 0 < W p := (hW p).lt_of_ne (Finsupp.mem_support_iff.mp hpW).symm
  have hqPos : 0 < W q := (hW q).lt_of_ne (Finsupp.mem_support_iff.mp hqW).symm
  omega

/-- A Picard-trivial automorphism preserving a nef square-zero boundary with
connected support fixes all its prime components. -/
theorem fixes_boundary_components_of_picard_trivial
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    (hconn : _root_.IsPreconnected (D.support : Set X))
    (hnef : ((LineBundleClass.mk hD.toInvertibleSheaf)⁻¹).IsNef k s)
    (hsq : Chow.classIntersectionNumber k X (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹
      (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ = 0)
    (e : X ≅ X) (he : D.comap e.hom = D) (hPic : ∀ L, pullback e.hom L = L) :
    ∀ x : CodimensionOnePoint X, (x : X) ∈ D.support → e.hom x = x := by
  have : IsNoetherian X := isNoetherian_of_finiteType s
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (s).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hmaps : Set.MapsTo e.hom (D.support : Set X) D.support := by
    intro x hx
    rw [← he, support_comap, Closeds.coe_preimage, Set.mem_preimage] at hx
    exact hx
  exact D.fixes_boundary_primes_of_pullback_eq e hmaps
    (hD.primeDivisorClass_injOn_of_isPreconnected_of_isNef hconn hnef hsq)
    (fun _ _ ↦ hPic _)

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
