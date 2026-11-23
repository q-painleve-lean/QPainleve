/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Nef
public import QPainleve.AlgebraicGeometry.WeilDivisor.IdealSheaf
import QPainleve.AlgebraicGeometry.Chow.ProperIntersection
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import TauCeti.LinearAlgebra.Matrix.NegSemidef
import TauCeti.Topology.Connected.Basic

/-!
# Multiplicities of connected nef divisors of square zero

On a locally factorial projective surface, the prime components of a connected
effective nef divisor of square zero have a one-dimensional space of numerical
relations for their intersection matrix. The coefficient vector spans the kernel.
In particular, two nef effective Cartier divisors of square zero with the same
connected support and each having a component of multiplicity one agree as divisors.

The connectedness argument follows Tau Ceti's
`Scheme.Hom.specialFiberIntersectionMatrix_reflTransGen`. The linear algebra is
Tau Ceti's
`Matrix.dotProduct_mulVec_eq_zero_iff_of_mulVec_eq_zero`, which formalizes
[Stacks Project, Lemma 55.2.3](https://stacks.math.columbia.edu/tag/0C5X).
-/

public section

open AlgebraicGeometry TopologicalSpace Matrix
open TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable (k : Type u) [Field k] [Infinite k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

local notation "cl" => Scheme.CartierDivisor.weilToLineBundleClassHom X
local notation "primeClass" => (LineBundleClass.primeDivisorClass (X := X))

private theorem intersection_mulVec_eq_zero (hX : topologicalKrullDim X = 2)
    (D E : SchemeWeilDivisor X) (hED : E.support ⊆ D.support)
    (hE : ∀ p ∈ D.support, classIntersectionNumber k X (cl E).toMul (primeClass p) = 0) :
    (fun p q : D.support ↦ (classIntersectionNumber k X (primeClass p) (primeClass q) : ℚ)) *ᵥ
      (fun p : D.support ↦ (E p : ℚ)) = 0 := by
  funext p
  have hp := hE p p.property
  rw [classIntersectionNumber_comm, classIntersectionNumber_weilToLineBundleClassHom k hX,
    Finsupp.sum, Finset.sum_subset hED (fun q _ hq ↦ by simp [Finsupp.notMem_support_iff.mp hq]),
    ← Finset.sum_coe_sort] at hp
  simpa [Matrix.mulVec, dotProduct, mul_comm] using congrArg (Int.castRingHom ℚ) hp

private theorem intersection_connected (hX : topologicalKrullDim X = 2)
    (D : SchemeWeilDivisor X) (hD : 0 ≤ D)
    (hconnected : IsPreconnected ((D.idealSheaf hD).support : Set X))
    (p q : D.support) :
    Relation.ReflTransGen (fun a b : D.support ↦ a ≠ b ∧
      0 < classIntersectionNumber k X (primeClass a) (primeClass b)) p q := by
  let C (a : D.support) : Set X := closure {((a : CodimensionOnePoint X) : X)}
  have hmem (r : CodimensionOnePoint X) :
      r ∈ D.support ↔ (r : X) ∈ (D.idealSheaf hD).support := by
    simpa only [Finsupp.mem_support_iff, WeilDivisor.coeff, not_not] using
      not_congr (D.coeff_eq_zero_iff_notMem_support hD r)
  have hcover : (⋃ a, C a) = ((D.idealSheaf hD).support : Set X) := by
    let hI := D.isEffectiveCartier_idealSheaf hD
    ext x
    rw [Set.mem_iUnion, SetLike.mem_coe, hI.mem_support_iff_exists_codimensionOnePoint]
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨r, (hmem r).mp r.property, specializes_iff_mem_closure.mpr hr⟩
    · rintro ⟨r, hr, hrx⟩
      exact ⟨⟨r, (hmem r).mpr hr⟩, specializes_iff_mem_closure.mp hrx⟩
  have hpre : IsPreconnected (⋃ a, C a) := hcover.symm ▸ hconnected
  have hchain := hpre.transGen_of_iUnion_of_isClosed (locallyFinite_of_finite C)
    (fun _ ↦ isClosed_closure) p q (Set.singleton_nonempty _).closure
    (Set.singleton_nonempty _).closure
  refine Relation.reflTransGen_closed (fun a b hab ↦ ?_) p q hchain.to_reflTransGen
  by_cases h : a = b
  · exact h ▸ .refl
  · have hne : (a : CodimensionOnePoint X) ≠ b := fun h' ↦ h (Subtype.ext h')
    exact .single ⟨h, (classIntersectionNumber_primeDivisorClass_pos_iff k hX.le hne).mpr hab⟩

/-- Let `D` be a nef effective divisor of square zero with preconnected support.
Any Weil divisor `E` supported on `D` that is orthogonal to its prime components
has coefficient vector proportional to that of `D`. The cross-product identity
expresses proportionality over the integers. -/
theorem mul_coeff_eq_mul_coeff_of_orthogonal_of_nef_square_zero
    (hX : topologicalKrullDim X = 2) {D E : SchemeWeilDivisor X}
    (hD : 0 ≤ D) (hconnected : IsPreconnected ((D.idealSheaf hD).support : Set X))
    (hnef : LineBundleClass.IsNef k (X ↘ Spec (.of k)) (cl D).toMul)
    (hzero : classIntersectionNumber k X (cl D).toMul (cl D).toMul = 0)
    (hED : E.support ⊆ D.support)
    (hE : ∀ p ∈ D.support, classIntersectionNumber k X (cl E).toMul (primeClass p) = 0)
    (p q : CodimensionOnePoint X) :
    D p * E q = E p * D q := by
  by_cases hp : p ∈ D.support
  case neg =>
    have hpE : p ∉ E.support := fun h ↦ hp (hED h)
    simp [Finsupp.notMem_support_iff.mp hp, Finsupp.notMem_support_iff.mp hpE]
  by_cases hq : q ∈ D.support
  case neg =>
    have hqE : q ∉ E.support := fun h ↦ hq (hED h)
    simp [Finsupp.notMem_support_iff.mp hq, Finsupp.notMem_support_iff.mp hqE]
  let A : Matrix D.support D.support ℚ :=
    fun a b ↦ classIntersectionNumber k X (primeClass a) (primeClass b)
  let m (a : D.support) : ℚ := D a
  let w (a : D.support) : ℚ := E a
  have hsymm : A.IsSymm := by
    ext a b
    rw [transpose_apply]
    exact congrArg (fun z : ℤ ↦ (z : ℚ))
      (classIntersectionNumber_comm (k := k) (primeClass b) (primeClass a))
  have hnonneg (a b : D.support) (hab : a ≠ b) : 0 ≤ A a b := by
    exact Int.cast_nonneg
      (classIntersectionNumber_primeDivisorClass_nonneg_of_ne k hX (fun h ↦ hab (Subtype.ext h)))
  have hconn (a b : D.support) : Relation.ReflTransGen (fun i j ↦ i ≠ j ∧ 0 < A i j) a b :=
    (intersection_connected k hX D hD hconnected a b).lift id fun _ _ h ↦
      ⟨h.1, by simpa only [A, id_eq, Int.cast_pos] using h.2⟩
  have hm (a : D.support) : 0 < m a := by
    have hnonneg : 0 ≤ D a := hD a
    exact Int.cast_pos.mpr (hnonneg.lt_of_ne (Finsupp.mem_support_iff.mp a.property).symm)
  have hAm : A *ᵥ m = 0 := intersection_mulVec_eq_zero k hX D D subset_rfl
    ((classIntersectionNumber_weilToLineBundleClassHom_self_eq_zero_iff k hX hD hnef).mp hzero)
  have hAw : A *ᵥ w = 0 := intersection_mulVec_eq_zero k hX D E hED hE
  obtain ⟨c, hc⟩ := (Matrix.dotProduct_mulVec_eq_zero_iff_of_mulVec_eq_zero
    hsymm hnonneg hconn hm hAm w).mp (by rw [hAw, dotProduct_zero])
  have hp' : (E p : ℚ) = c * D p := congrFun hc ⟨p, hp⟩
  have hq' : (E q : ℚ) = c * D q := congrFun hc ⟨q, hq⟩
  exact_mod_cast (show (D p : ℚ) * E q = (E p : ℚ) * D q by rw [hp', hq']; ring)

/-- Two effective nef Weil divisors of square zero with the same preconnected support
are equal if each has a prime component of multiplicity one. The two components
used to normalize the coefficient vectors can be different. -/
theorem eq_of_nef_square_zero_boundary_multiplicities
    (hX : topologicalKrullDim X = 2) {D E : SchemeWeilDivisor X}
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hsupport : D.support = E.support)
    (hconnected : IsPreconnected ((D.idealSheaf hD).support : Set X))
    (hnefD : LineBundleClass.IsNef k (X ↘ Spec (.of k)) (cl D).toMul)
    (hnefE : LineBundleClass.IsNef k (X ↘ Spec (.of k)) (cl E).toMul)
    (hzeroD : classIntersectionNumber k X (cl D).toMul (cl D).toMul = 0)
    (hzeroE : classIntersectionNumber k X (cl E).toMul (cl E).toMul = 0)
    {p q : CodimensionOnePoint X} (hp : D p = 1) (hq : E q = 1) : D = E := by
  have hpair := mul_coeff_eq_mul_coeff_of_orthogonal_of_nef_square_zero k hX hD
    hconnected hnefD hzeroD hsupport.ge
    (hsupport ▸ (classIntersectionNumber_weilToLineBundleClassHom_self_eq_zero_iff
      k hX hE hnefE).mp hzeroE)
  have hprod : E p * D q = 1 := by simpa [hp, hq] using (hpair p q).symm
  have hp' : E p = 1 := Int.eq_one_of_mul_eq_one_right (hE p) hprod
  apply Finsupp.ext
  intro r
  simpa [hp, hp'] using (hpair p r).symm

open Scheme.IdealSheafData in
/-- On a locally factorial projective surface, the scheme structures of two effective Cartier
divisors with the same preconnected support are equal if both are nef of square zero and
each has multiplicity one at some prime component. -/
theorem eq_of_nef_square_zero_of_support_eq
    (hX : topologicalKrullDim X = 2) {I J : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)
    (hsupport : I.support = J.support) (hconnected : IsPreconnected (I.support : Set X))
    (hnefI : LineBundleClass.IsNef k (X ↘ Spec (.of k))
      (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹)
    (hnefJ : LineBundleClass.IsNef k (X ↘ Spec (.of k))
      (LineBundleClass.mk hJ.toInvertibleSheaf)⁻¹)
    (hzeroI : classIntersectionNumber k X (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
      (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ = 0)
    (hzeroJ : classIntersectionNumber k X (LineBundleClass.mk hJ.toInvertibleSheaf)⁻¹
      (LineBundleClass.mk hJ.toInvertibleSheaf)⁻¹ = 0)
    {p q : CodimensionOnePoint X}
    (hp : hI.toCartierDivisor.toWeilDivisor p = 1)
    (hq : hJ.toCartierDivisor.toWeilDivisor q = 1) : I = J := by
  have : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let D := hI.toCartierDivisor.toWeilDivisor
  let E := hJ.toCartierDivisor.toWeilDivisor
  have hD := (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
    hI.isEffective_toCartierDivisor
  have hE := (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
    hJ.isEffective_toCartierDivisor
  have hID : D.idealSheaf hD = I :=
    (SchemeWeilDivisor.idealSheaf_toWeilDivisor hI.isEffective_toCartierDivisor).trans
      hI.idealSheaf_toCartierDivisor
  have hsupp : D.support = E.support := by
    ext r
    have h := (hI.coeff_toWeilDivisor_eq_zero_iff r).trans
      ((hsupport.symm ▸ hJ.coeff_toWeilDivisor_eq_zero_iff r :
        WeilDivisor.coeff E r = 0 ↔ (r : X) ∉ I.support)).symm
    simpa only [Finsupp.mem_support_iff, WeilDivisor.coeff] using not_congr h
  have hclI : (cl D).toMul = (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ := by
    rw [Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor, toMul_ofMul,
      hI.toLineBundleClass_toCartierDivisor]
  have hclJ : (cl E).toMul = (LineBundleClass.mk hJ.toInvertibleSheaf)⁻¹ := by
    rw [Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor, toMul_ofMul,
      hJ.toLineBundleClass_toCartierDivisor]
  have heq := eq_of_nef_square_zero_boundary_multiplicities k hX hD hE hsupp
    (hID.symm ▸ hconnected) (hclI.symm ▸ hnefI) (hclJ.symm ▸ hnefJ)
    (by rwa [hclI]) (by rwa [hclJ]) hp hq
  apply (hI.toCartierDivisor_eq_iff hJ).mp
  apply Scheme.CartierDivisor.toWeilDivisorHom_injective
  simpa only [Scheme.CartierDivisor.toWeilDivisorHom_apply] using heq

end TauCeti.AlgebraicGeometry.Chow
