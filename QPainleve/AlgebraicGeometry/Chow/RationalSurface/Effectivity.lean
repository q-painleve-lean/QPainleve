/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef

import QPainleve.AlgebraicGeometry.Blowup.Tower.Cohomology
import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Blowup.Tower.SecondCohomology
import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.RiemannRoch
import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef.Pullback
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.ZeroLocus
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample

/-!
# Effectivity on rational surfaces

Second cohomology vanishes for nef line bundles on smooth projective rational surfaces over
an algebraically closed field. On a common resolution with the projective plane, intersection
with a pulled-back hyperplane class makes the plane degree nonnegative. The point-blowup
calculation propagates vanishing from the plane for every choice of exceptional coefficients.

Riemann–Roch then gives a nonempty effective Cartier divisor in a positive tensor power of
any nef class of positive square. This supplies the effective divisor in the proof of the
numerical ampleness criterion. See [Debarre, *Introduction to Mori Theory*, §4.1][Debarre].

A class of positive Euler characteristic is effective if its canonical complement
has negative intersection with a nef class.

[Debarre]: https://perso.imj-prg.fr/wp-content/uploads/debarre-pub/M22.pdf#page=42
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.LineBundleClass TauCeti.SymmetricAlgebra
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

variable (k : Type u) [Field k] [algClosed : IsAlgClosed k]

include algClosed

local notation "S" => Spec (CommRingCat.of k)
local notation "P" => Proj (homogeneousSubmodule k (Fin 3 → k))
local notation "O[" d "]" => Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) d
local notation "degree" => Module.Basis.picardTwistEquiv (Pi.basisFun k (Fin 3))

variable (X : Scheme.{u}) [X.Over (Spec (.of k))] [projective : X.IsProjectiveOver k]
  [smooth : SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [rational : Scheme.IsRationalOver (X ↘ Spec (.of k))]

namespace AlgebraicGeometry.Scheme

private theorem plane_degree_nonneg_of_nef_marking {W : Scheme.{u}} {n : ℕ}
    {U : BlowupTower P n W} (hU : IsClosedPointTower P U)
    (a : Additive (LineBundleClass P)) (b : Fin n → ℤ)
    (ha : IsNef k (U.toBase ≫ (P ↘ S)) (U.picardHom (a, b)).toMul) :
    0 ≤ degree a := by
  let : W.Over S := ⟨U.toBase ≫ (P ↘ S)⟩
  have : W.IsProjectiveOver k := U.isProjectiveOver k
  have : IsIntegral W := hU.isIntegral (P ↘ S)
  have : SmoothOfRelativeDimension 2 (W ↘ S) := hU.smoothOfRelativeDimension (P ↘ S)
  have (w : W) : UniqueFactorizationMonoid (W.presheaf.stalk w) :=
    (W ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two w
  have hP := topologicalKrullDim_eq_of_smoothOfRelativeDimension (P ↘ S) (n := 2)
  have hW := topologicalKrullDim_eq_of_smoothOfRelativeDimension (W ↘ S) (n := 2)
  have hample : (LineBundleClass.mk (O[1])).IsAmple :=
    isAmple_twistingSheaf k (Fin 3 → k) Nat.one_pos
  obtain ⟨r, hr, I, hI, -, hc⟩ := hample.exists_effectiveCartier_pow_ne_top (P ↘ S)
    (hP.symm ▸ (by decide : (0 : WithBot ℕ∞) < 2))
  have htotal := hU.isEffectiveCartier_totalTransform (P ↘ S) hI
  have h := Chow.classIntersectionNumber_nonneg_of_isNef_of_isEffectiveCartier k hW ha htotal
  rw [← hI.pullback_mk_toInvertibleSheaf htotal, ← pullback_inv, hc] at h
  have he := classIntersectionNumber_picardMarking k hU (a, b)
    (Additive.ofMul ((LineBundleClass.mk (O[1])) ^ r), 0)
  simp only [picardMarking_apply, picardHom_apply_zero, toMul_ofMul, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, sub_zero, Chow.classIntersectionNumber_projectivePlane,
    ofMul_toMul] at he
  rw [he] at h
  simp only [ofMul_pow, map_nsmul, Module.Basis.picardTwistEquiv_apply_twist,
    nsmul_eq_mul, mul_one] at h
  exact nonneg_of_mul_nonneg_left h (Int.natCast_pos.mpr hr)

private theorem subsingleton_cohomology_two_of_nef_plane_tower {W : Scheme.{u}} {n : ℕ}
    {U : BlowupTower P n W} (hU : IsClosedPointTower P U) (L : InvertibleSheaf W)
    (hL : IsNef k (U.toBase ≫ (P ↘ S)) (LineBundleClass.mk L)) :
    Subsingleton (Cohomology L.obj 2) := by
  have : IsNoetherian P := isNoetherian_of_finiteType (P ↘ S)
  obtain ⟨⟨a, b⟩, hab⟩ :=
    (hU.bijective_picardHom (P ↘ S)).surjective (Additive.ofMul (LineBundleClass.mk L))
  have hmark := congrArg Additive.toMul hab
  have hd : 0 ≤ degree a := plane_degree_nonneg_of_nef_marking k hU a b (hmark.symm ▸ hL)
  exact hU.subsingleton_cohomology_two_of_plane_degree_gt_neg_three k (a, b) L hab
    (show -3 < degree a by omega)

include projective smooth rational

/-- Every nef line bundle on a smooth projective rational surface over an algebraically
closed field has vanishing second cohomology. -/
theorem subsingleton_cohomology_two_of_isNef_of_isRationalOver (L : InvertibleSheaf X)
    (hL : IsNef k (X ↘ S) (LineBundleClass.mk L)) : Subsingleton (Cohomology L.obj 2) := by
  obtain ⟨_, _, V, W, T, U, e, hT, hU, he⟩ :=
    X.exists_common_pointBlowup_resolution_projectivePlane k
  let : V.Over S := ⟨T.toBase ≫ X ↘ S⟩
  let : W.Over S := ⟨U.toBase ≫ P ↘ S⟩
  have : V.IsProjectiveOver k := T.isProjectiveOver k
  have : T.toBase.IsOver S := ⟨rfl⟩
  have : e.hom.IsOver S := ⟨he⟩
  let M := (InvertibleSheaf.pullback T.toBase).obj L
  let N := (InvertibleSheaf.pullback e.hom).obj M
  have hN : IsNef k (W ↘ S) (LineBundleClass.mk N) := by
    rw [← pullback_mk, ← pullback_mk]
    exact (hL.pullback T.toBase).pullback e.hom
  have := subsingleton_cohomology_two_of_nef_plane_tower k hU N hN
  obtain ⟨eT⟩ := hT.nonempty_cohomologyPullbackLinearEquiv k
    ((InvertibleSheaf.toFiniteLocallyFree X).obj L) 2
  have eLM : Cohomology L.obj 2 ≃ₗ[k] Cohomology M.obj 2 := by
    dsimp only [M]
    rw [InvertibleSheaf.pullback_obj_obj]
    exact eT
  have eMN : Cohomology M.obj 2 ≃ₗ[k] Cohomology N.obj 2 := by
    dsimp only [N]
    rw [InvertibleSheaf.pullback_obj_obj]
    exact (e.hom.cohomologyPullbackBaseLinearEquivOfIsIso k M.obj 2).symm
  exact (eLM.trans eMN).injective.subsingleton

end AlgebraicGeometry.Scheme

namespace TauCeti.AlgebraicGeometry.LineBundleClass

open Scheme.IdealSheafData

variable {X}

include projective smooth rational

private theorem exists_pow_pos_eulerCharBelow_of_self_pos
    (a : LineBundleClass X) (hX : topologicalKrullDim X = 2)
    [IsIntegral X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    (ha : 0 < Chow.classIntersectionNumber k X a a) :
    ∃ n : ℕ, 0 < n ∧ 0 < eulerCharBelow k (a ^ n) 3 := by
  let B := Chow.classIntersectionBilinForm k hX
  let x := Additive.ofMul a
  let K := Additive.ofMul (mk (canonicalBundle k X 2))
  let n := (B x K).toNat + 1
  have hn : 0 < n := Nat.succ_pos _
  have hs : 0 < B x x := by
    simpa only [B, x, Chow.classIntersectionBilinForm_apply, toMul_ofMul] using ha
  have hnK : B x K < (n : ℤ) := by dsimp [n]; omega
  have hpos : 0 < (n : ℤ) * B x x - B x K :=
    sub_pos.mpr (hnK.trans_le (le_mul_of_one_le_right (Int.natCast_nonneg n) (by omega)))
  have hRR := eulerCharBelow_eq_riemannRoch_of_isRationalOver k (a ^ n)
  have hRR' : 2 * (eulerCharBelow k (a ^ n) 3 - 1) =
      (n : ℤ) * ((n : ℤ) * B x x - B x K) := by
    calc
      _ = B (Additive.ofMul (a ^ n)) (Additive.ofMul (a ^ n)) -
          B (Additive.ofMul (a ^ n)) K := by
        simpa only [B, K, Chow.classIntersectionBilinForm_apply, toMul_ofMul] using hRR
      _ = _ := by
        rw [mul_sub]
        simp only [x, ofMul_pow, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  exact ⟨n, hn, by linarith only [hRR', mul_pos (Int.natCast_pos.mpr hn) hpos]⟩

/-- A nef line bundle of positive self-intersection on a smooth projective rational
surface has a positive power represented by a nonempty effective Cartier divisor. -/
theorem exists_effectiveCartier_pow_of_isNef_of_self_pos (a : LineBundleClass X)
    (hnef : IsNef k (X ↘ S) a) (ha : 0 < Chow.classIntersectionNumber k X a a) :
    ∃ (n : ℕ) (_ : 0 < n) (I : X.IdealSheafData) (hI : I.IsEffectiveCartier),
      I ≠ ⊤ ∧ (mk hI.toInvertibleSheaf)⁻¹ = a ^ n := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := rational.isIntegral_of_smooth
  have (x : X) : UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two x
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  obtain ⟨n, hn, hχ⟩ := exists_pow_pos_eulerCharBelow_of_self_pos k a hX ha
  obtain ⟨L, hL⟩ := mk_surjective (a ^ n)
  have hpow (j : ℕ) : IsNef k (X ↘ S) (a ^ j) := by
    induction j with
    | zero => simpa only [pow_zero] using isNef_one k (X ↘ S)
    | succ j ih => simpa only [pow_succ] using ih.mul hnef
  have : Subsingleton (Cohomology L.obj 2) :=
    X.subsingleton_cohomology_two_of_isNef_of_isRationalOver k L (hL.symm ▸ hpow n)
  have h₂ : Module.finrank k (Cohomology L.obj 2) = 0 := Module.finrank_zero_of_subsingleton
  have hs : ∃ s : Γ(L.obj, ⊤), s ≠ 0 := by
    by_contra! hz
    have : Subsingleton Γ(L.obj, ⊤) := (subsingleton_iff_forall_eq 0).mpr hz
    have h₀ : Module.finrank k (Cohomology L.obj 0) = 0 :=
      (finrank_cohomology_zero_eq_finrank_globalSections k L.obj).trans
        Module.finrank_zero_of_subsingleton
    rw [← hL, eulerCharBelow_mk, Scheme.Modules.eulerCharBelow_succ,
      Scheme.Modules.eulerCharBelow_two, h₀, h₂] at hχ
    omega
  obtain ⟨s, hs⟩ := hs
  obtain ⟨I, hI, hclass⟩ := L.exists_isEffectiveCartier_of_ne_zero s hs
  have hEq : (mk hI.toInvertibleSheaf)⁻¹ = a ^ n := by rw [hclass, inv_inv, hL]
  refine ⟨n, hn, I, hI, ?_, hEq⟩
  rintro rfl
  rw [mk_toInvertibleSheaf_top, inv_one] at hEq
  let B := Chow.classIntersectionBilinForm k hX (Additive.ofMul a)
  have hzero := congrArg (fun b : LineBundleClass X ↦ B (Additive.ofMul b)) hEq
  simp only [ofMul_one, ofMul_pow, map_zero, map_nsmul, B, nsmul_eq_mul,
    Chow.classIntersectionBilinForm_apply, toMul_ofMul] at hzero
  exact (mul_pos (Int.natCast_pos.mpr hn) ha).ne hzero

/-- A class of positive Euler characteristic is effective if a nef class has
negative intersection with its canonical complement. -/
theorem exists_effectiveCartier_of_eulerCharBelow_pos_of_intersection_canonical_mul_inv_neg
    {a h : LineBundleClass X} (hχ : 0 < eulerCharBelow k a 3) (hh : h.IsNef k (X ↘ S))
    (hneg : Chow.classIntersectionNumber k X h (mk (canonicalBundle k X 2) * a⁻¹) < 0) :
    ∃ (I : X.IdealSheafData) (hI : I.IsEffectiveCartier), (mk hI.toInvertibleSheaf)⁻¹ = a := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := rational.isIntegral_of_smooth
  have := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  obtain ⟨I, hI, he | he⟩ :=
    exists_effectiveCartier_or_canonical_mul_inv_of_eulerCharBelow_pos k a hχ
  · exact ⟨I, hI, he⟩
  · exact False.elim (hneg.not_ge (he ▸
      Chow.classIntersectionNumber_nonneg_of_isNef_of_isEffectiveCartier k hX hh hI))

end TauCeti.AlgebraicGeometry.LineBundleClass
