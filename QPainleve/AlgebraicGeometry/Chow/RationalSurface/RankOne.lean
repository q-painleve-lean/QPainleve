/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Ample

import QPainleve.AlgebraicGeometry.Chow.Ample
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Pluricanonical
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.LineBundle.Power
import TauCeti.LinearAlgebra.PerfectPairing.Basis

/-!
# The ample generator of a rank-one rational surface

A smooth projective rational surface of Picard rank one has an ample integral
generator of square one, and its canonical class is minus three times that
generator. The square follows from perfection of the Picard pairing via
`Module.Basis.isUnit_det_of_isPerfPair`. This excludes the cyclic canonical case in
[Vakil, *Complex Algebraic Surfaces*, Class 16, §2][Vakil].

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass16A.pdf
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve
open TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] [algClosed : IsAlgClosed k]
  (X : Scheme.{u}) [X.Over (Spec (.of k))] [projective : X.IsProjectiveOver k]
  [smooth : SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [rational : Scheme.IsRationalOver (X ↘ Spec (.of k))]

local notation "Pic" => Additive (LineBundleClass X)
local notation "f" => X ↘ Spec (CommRingCat.of k)
local notation "ω" => canonicalBundle k X 2
local notation "K" => LineBundleClass.mk ω
local notation "B" => Chow.classIntersectionNumber k X

private theorem not_isAmple_of_pow_eq_canonicalBundle {h : LineBundleClass X} {d : ℕ}
    (hd : 0 < d) (he : h ^ d = K) : ¬ h.IsAmple := by
  intro hh
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsIntegral X := rational.isIntegral_of_smooth
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨m, hm, L, hL, s, hxs, -⟩ := hh.exists_isAffineOpen_nonvanishingLocus x
  have hclass : LineBundleClass.mk (L.tensorPow d) = LineBundleClass.mk ((ω).tensorPow m) := by
    rw [LineBundleClass.mk_tensorPow, LineBundleClass.mk_tensorPow, hL, ← he, ← pow_mul,
      ← pow_mul, Nat.mul_comm]
  obtain ⟨e⟩ := LineBundleClass.mk_eq_mk_iff.mp hclass
  let g := (L.tensorPowObjIso d).symm ≪≫ e
  let t := g.hom.app ⊤ (tensorPowSection s d)
  have hxt : x ∈ ((ω).tensorPow m).obj.nonvanishingLocus t := by
    simpa only [t, nonvanishingLocus_hom_app, nonvanishingLocus_tensorPowSection _ hd] using hxs
  have := X.subsingleton_cohomology_zero_pluricanonical_of_isRationalOver k hm
  have : Subsingleton Γ(((ω).tensorPow m).obj, ⊤) :=
    (cohomologyZeroBaseLinearEquiv k X _).surjective.subsingleton
  simp only [Subsingleton.elim t 0, nonvanishingLocus_zero, TopologicalSpace.Opens.mem_bot] at hxt

include algClosed projective smooth rational in
private theorem exists_ample_picard_basis_of_finrank_eq_one
    (hrank : Module.finrank ℤ Pic = 1) :
    ∃ b : Module.Basis Unit ℤ Pic, (b ()).toMul.IsAmple := by
  have : Module.Free ℤ Pic := X.free_picard_of_isRationalOver k
  let b := Module.basisUnique Unit hrank
  obtain ⟨A, hA⟩ := X.exists_isAmple_of_isProjectiveOver k
  let n := b.repr (Additive.ofMul A) ()
  have hnA : n • b () = Additive.ofMul A := by
    simpa only [Fintype.sum_unique] using b.sum_repr (Additive.ofMul A)
  have hAeq : (b ()).toMul ^ n = A := by
    simpa only [toMul_zsmul, toMul_ofMul] using congrArg Additive.toMul hnA
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsIntegral X := rational.isIntegral_of_smooth
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have hn : n ≠ 0 := by
    intro hz
    have hpos := Chow.classIntersectionNumber_pos_of_isAmple k hdim hA hA
    rw [← hAeq, hz, zpow_zero, Chow.classIntersectionNumber_one_left] at hpos
    exact (lt_irrefl 0) hpos
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · refine ⟨b.unitsSMul (fun _ ↦ (-1 : ℤˣ)), ?_⟩
    rw [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_neg, Units.val_one, neg_one_smul,
      toMul_neg]
    rw [zpow_eq_inv_pow_natAbs _ hneg.le] at hAeq
    exact LineBundleClass.IsAmple.of_pow (Int.natAbs_pos.mpr hn) (hAeq ▸ hA)
  · refine ⟨b, LineBundleClass.IsAmple.of_pow (Int.natAbs_pos.mpr hn) ?_⟩
    rwa [← zpow_natCast, Int.natAbs_of_nonneg hpos.le, hAeq]

/-- On a smooth projective rational surface of Picard rank one there is an ample class
of square one which freely generates the Picard group. The canonical class is its
inverse cube. -/
theorem exists_ample_picard_generator_of_finrank_eq_one
    (hrank : Module.finrank ℤ Pic = 1) :
    ∃ h : LineBundleClass X, h.IsAmple ∧ B h h = 1 ∧ K = h ^ (-3 : ℤ) ∧
      Function.Bijective (h ^ · : ℤ → LineBundleClass X) := by
  obtain ⟨b, hb⟩ := X.exists_ample_picard_basis_of_finrank_eq_one k hrank
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsIntegral X := rational.isIntegral_of_smooth
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  let Q := Chow.classIntersectionBilinForm k hdim
  have hp : Q.IsPerfPair := Chow.isPerfPair_classIntersectionBilinForm_of_isRationalOver k X
  have hunit : IsUnit (Q (b ()) (b ())) := by
    simpa only [Matrix.det_unique, LinearMap.toMatrix₂_apply] using
      b.isUnit_det_of_isPerfPair b Q hp
  have hpos : 0 < Q (b ()) (b ()) := by
    simpa only [Q, Chow.classIntersectionBilinForm_apply] using
      Chow.classIntersectionNumber_pos_of_isAmple k hdim hb hb
  have hsq : Q (b ()) (b ()) = 1 := by
    rcases Int.isUnit_iff.mp hunit with h | h <;> omega
  let h := (b ()).toMul
  have hcoord (a : Pic) : b.repr a () • b () = a := by
    simpa only [Fintype.sum_unique] using b.sum_repr a
  have hs (n : ℤ) : Q (b ()) (n • b ()) = n := by
    rw [LinearMap.BilinForm.smul_right, hsq, mul_one]
  let n := b.repr (Additive.ofMul K) ()
  have hn : n • b () = Additive.ofMul K := hcoord _
  have hK : B K K = 9 := by
    have hnum := Chow.finrank_picard_add_canonical_square_of_isRationalOver k X
    rw [hrank] at hnum
    omega
  have hn₂ : n ^ 2 = (3 : ℤ) ^ 2 := by
    have he : Q (n • b ()) (n • b ()) = 9 := by
      simpa only [hn, Q, Chow.classIntersectionBilinForm_apply, toMul_ofMul] using hK
    rw [LinearMap.BilinForm.smul_left, hs] at he
    nlinarith only [he]
  have hneg : n = -3 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hn₂ with hn' | hn'
    · have he : h ^ (3 : ℕ) = K := by
        rw [← zpow_natCast, Nat.cast_ofNat]
        simpa only [h, toMul_zsmul, toMul_ofMul, hn'] using
          congrArg Additive.toMul hn
      exact (X.not_isAmple_of_pow_eq_canonicalBundle k (by decide) he hb).elim
    · exact hn'
  refine ⟨h, hb, by simpa only [Q, h, Chow.classIntersectionBilinForm_apply] using hsq, ?_, ?_, ?_⟩
  · simpa only [h, toMul_zsmul, toMul_ofMul, hneg] using
      (congrArg Additive.toMul hn).symm
  · intro a c hac
    have he := congrArg (Q (b ()) ∘ Additive.ofMul) hac
    simpa only [Function.comp_apply, h, ofMul_zpow, ofMul_toMul, hs] using he
  · intro a
    refine ⟨b.repr (Additive.ofMul a) (), ?_⟩
    simpa only [h, toMul_zsmul, toMul_ofMul] using
      congrArg Additive.toMul (hcoord (Additive.ofMul a))

/-- The Picard group of a smooth projective rational surface is never generated by
the canonical class alone. -/
theorem not_surjective_zpow_canonicalBundle_of_isRationalOver :
    ¬ Function.Surjective (K ^ · : ℤ → LineBundleClass X) := by
  intro hgen
  have : Module.Free ℤ Pic := X.free_picard_of_isRationalOver k
  have : Module.Finite ℤ Pic := X.finite_picard_of_isRationalOver k
  have hle : Module.finrank ℤ Pic ≤ 1 := finrank_le_one_iff.mpr
    ⟨Additive.ofMul K, fun a ↦ by
      obtain ⟨n, hn⟩ := hgen a.toMul
      exact ⟨n, by simpa only [ofMul_zpow, ofMul_toMul] using congrArg Additive.ofMul hn⟩⟩
  have hpos : 0 < Module.finrank ℤ Pic := by
    by_contra! h
    have hz : Module.finrank ℤ Pic = 0 := Nat.eq_zero_of_le_zero h
    have : Subsingleton Pic := Module.finrank_zero_iff.mp hz
    have hk : K = 1 := congrArg Additive.toMul (Subsingleton.elim (Additive.ofMul K) 0)
    have hnum := Chow.finrank_picard_add_canonical_square_of_isRationalOver k X
    rw [hz, hk, Chow.classIntersectionNumber_one_left] at hnum
    norm_num at hnum
  obtain ⟨H, -, -, hk, hH⟩ := X.exists_ample_picard_generator_of_finrank_eq_one k (by omega)
  obtain ⟨n, hn⟩ := hgen H
  have he : H ^ ((-3 : ℤ) * n) = H ^ (1 : ℤ) := by
    simpa only [hk, zpow_mul, zpow_one] using hn
  have := hH.injective he
  omega

end AlgebraicGeometry.Scheme
