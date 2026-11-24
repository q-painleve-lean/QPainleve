/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef
public import QPainleve.AlgebraicGeometry.LineBundle.EffectiveClass

import Mathlib.Data.Nat.Order.Lemmas
import QPainleve.AlgebraicGeometry.Blowup.Tower.Cohomology
import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Blowup.Tower.SecondCohomology
import QPainleve.AlgebraicGeometry.Chow.EffectiveClass
import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
import QPainleve.AlgebraicGeometry.Chow.PositiveCone
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Pluricanonical
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.RiemannRoch
import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Effectivity
import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef.Pullback
import QPainleve.AlgebraicGeometry.LineBundle.Ample
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

An integral class in the ample component of the positive cone also has vanishing
second cohomology. All its sufficiently high powers are effective by Riemann–Roch.
This gives the effectivity used in the curve-cone description of
[Gross, Hacking and Keel, Lemma 2.14][GHK].

A class of positive Euler characteristic is effective if its canonical complement
has negative intersection with a nef class.

[GHK]: https://arxiv.org/html/1211.6367v5#S2
[Debarre]: https://perso.imj-prg.fr/wp-content/uploads/debarre-pub/M22.pdf#page=42
-/

public section

open AlgebraicGeometry CategoryTheory Filter QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.LineBundleClass TauCeti.SymmetricAlgebra
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

open scoped TensorProduct

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
  have hd := plane_degree_nonneg_of_nef_marking k hU a b (hmark.symm ▸ hL)
  exact hU.subsingleton_cohomology_two_of_plane_degree_gt_neg_three k (a, b) L hab
    (show -3 < degree a by omega)

omit smooth rational in
private theorem plane_degree_pos_of_positive_square {n : ℕ} {W : Scheme.{u}}
    {U : BlowupTower P n W} (hU : IsClosedPointTower P U)
    {g : W ⟶ X} (hg : g ≫ X ↘ S = U.toBase ≫ P ↘ S)
    {a h : LineBundleClass X} (hh : h.IsAmple)
    (hpull : letI : W.Over S := ⟨U.toBase ≫ P ↘ S⟩
      ∀ a b, Chow.classIntersectionNumber k W
        (LineBundleClass.pullback g a) (LineBundleClass.pullback g b) =
        Chow.classIntersectionNumber k X a b)
    (hhh : 0 < Chow.classIntersectionNumber k X h h)
    (haa : 0 < Chow.classIntersectionNumber k X a a)
    (hha : 0 < Chow.classIntersectionNumber k X h a)
    (b : Additive (LineBundleClass P) × (Fin n → ℤ))
    (hb : (U.picardHom b).toMul = LineBundleClass.pullback g a) :
    0 < degree b.1 := by
  let : W.Over S := ⟨U.toBase ≫ P ↘ S⟩
  let : g.IsOver S := ⟨hg⟩
  let : U.toBase.IsOver S := ⟨rfl⟩
  let : W.IsProjectiveOver k := U.isProjectiveOver k
  let : IsIntegral W := hU.isIntegral (P ↘ S)
  let : SmoothOfRelativeDimension 2 (W ↘ S) := hU.smoothOfRelativeDimension (P ↘ S)
  have : IsNoetherian P := isNoetherian_of_finiteType (P ↘ S)
  have : Module.Finite ℤ (Additive (LineBundleClass P)) :=
    Module.Finite.of_surjective (degree).symm.toIntLinearEquiv.toLinearMap (degree).symm.surjective
  let marking := U.picardMarking hU (P ↘ S)
  have : Module.Finite ℤ (Additive (LineBundleClass W)) :=
    Module.Finite.of_surjective marking.toLinearMap marking.surjective
  obtain ⟨hQ, hsig, _⟩ :=
    Chow.signature_realIntersectionBilinForm_of_common_resolution_projectivePlane k
      (T := BlowupTower.nil (X := W)) IsClosedPointTower.nil hU (Iso.refl W) (by simp)
  let H := LineBundleClass.mk (O[1])
  have hH : H.IsAmple := isAmple_twistingSheaf k (Fin 3 → k) Nat.one_pos
  have hdegree : degree (Additive.ofMul H) = 1 :=
    (Pi.basisFun k (Fin 3)).picardTwistEquiv_apply_twist 1
  have hplane : Chow.classIntersectionNumber k W (LineBundleClass.pullback U.toBase H)
      (LineBundleClass.pullback U.toBase H) = 1 := by
    rw [hU.classIntersectionNumber_pullback k, Chow.classIntersectionNumber_projectivePlane,
      hdegree, mul_one]
  have hpos := (Chow.classIntersectionNumber_pos_iff_of_isNef k hQ hsig.le
    (hh.isNef.pullback g) (hH.isNef.pullback U.toBase)
    (by rwa [hpull]) (by rw [hplane]; exact Int.zero_lt_one)
    (by rwa [hpull])).mp (by rwa [hpull])
  have hform := classIntersectionNumber_picardMarking k hU (Additive.ofMul H, 0) b
  simp only [picardMarking_apply, picardHom_apply_zero, hb, toMul_ofMul, ofMul_toMul,
    Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero,
    Chow.classIntersectionNumber_projectivePlane, hdegree, one_mul] at hform
  rwa [← hform]

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
  exact hT.subsingleton_cohomology_two_of_pullback_tower_iso k e L
    (subsingleton_cohomology_two_of_nef_plane_tower k hU N hN)

/-- A line bundle of positive square meeting an ample class positively has vanishing
second cohomology on a smooth projective rational surface over an algebraically closed field. -/
theorem subsingleton_cohomology_two_of_self_pos_of_intersection_pos
    (L : InvertibleSheaf X) {h : LineBundleClass X} (hh : h.IsAmple)
    (hLL : 0 < Chow.classIntersectionNumber k X (LineBundleClass.mk L) (LineBundleClass.mk L))
    (hhL : 0 < Chow.classIntersectionNumber k X h (LineBundleClass.mk L)) :
    Subsingleton (Cohomology L.obj 2) := by
  obtain ⟨_, _, V, W, T, U, e, hT, hU, he⟩ :=
    X.exists_common_pointBlowup_resolution_projectivePlane k
  let : V.Over S := ⟨T.toBase ≫ X ↘ S⟩
  let : W.Over S := ⟨U.toBase ≫ P ↘ S⟩
  have : T.toBase.IsOver S := ⟨rfl⟩
  have : e.hom.IsOver S := ⟨he⟩
  have : IsNoetherian P := isNoetherian_of_finiteType (P ↘ S)
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := rational.isIntegral_of_smooth
  let g := e.hom ≫ T.toBase
  have hg : g ≫ X ↘ S = U.toBase ≫ P ↘ S := by simpa only [g, Category.assoc] using he
  have hpull (a b : LineBundleClass X) :
      Chow.classIntersectionNumber k W
        (LineBundleClass.pullback g a) (LineBundleClass.pullback g b) =
        Chow.classIntersectionNumber k X a b := by
    dsimp only [g]
    rw [← LineBundleClass.pullback_comp, ← LineBundleClass.pullback_comp,
      Chow.classIntersectionNumber_pullback_of_isIso k e.hom,
      hT.classIntersectionNumber_pullback k]
  let M := (InvertibleSheaf.pullback e.hom).obj ((InvertibleSheaf.pullback T.toBase).obj L)
  have hM : LineBundleClass.mk M = LineBundleClass.pullback g (LineBundleClass.mk L) := by
    simp only [M, g, ← pullback_mk, LineBundleClass.pullback_comp]
  obtain ⟨⟨a, b⟩, hab⟩ :=
    (hU.bijective_picardHom (P ↘ S)).surjective (Additive.ofMul (LineBundleClass.mk M))
  have hmark : (U.picardHom (a, b)).toMul = LineBundleClass.mk M := congrArg Additive.toMul hab
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hhh := Chow.classIntersectionNumber_pos_of_isAmple k
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)) hh hh
  have hd : 0 < degree a :=
    plane_degree_pos_of_positive_square k X hU hg hh hpull hhh hLL hhL _ (hmark.trans hM)
  exact hT.subsingleton_cohomology_two_of_pullback_tower_iso k e L
    (hU.subsingleton_cohomology_two_of_plane_degree_gt_neg_three k (a, b) M hab
      (show -3 < degree a by omega))

end AlgebraicGeometry.Scheme

namespace TauCeti.AlgebraicGeometry.LineBundleClass

open Scheme.IdealSheafData

variable {X}

include projective smooth rational

private theorem eventually_pos_eulerCharBelow_pow_of_self_pos
    (a : LineBundleClass X) (hX : topologicalKrullDim X = 2)
    [IsIntegral X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    (ha : 0 < Chow.classIntersectionNumber k X a a) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ 0 < eulerCharBelow k (a ^ n) 3 := by
  let B := Chow.classIntersectionBilinForm k hX
  let x := Additive.ofMul a
  let K := Additive.ofMul (mk (canonicalBundle k X 2))
  filter_upwards [eventually_ge_atTop ((B x K).toNat + 1)] with n hn
  have hn₀ : 0 < n := by omega
  have hs : 0 < B x x := by
    simpa only [B, x, Chow.classIntersectionBilinForm_apply, toMul_ofMul] using ha
  have hnK : B x K < (n : ℤ) := by omega
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
  exact ⟨hn₀, by linarith only [hRR', mul_pos (Int.natCast_pos.mpr hn₀) hpos]⟩

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
  obtain ⟨n, hn, hχ⟩ := (eventually_pos_eulerCharBelow_pow_of_self_pos k a hX ha).exists
  obtain ⟨L, hL⟩ := mk_surjective (a ^ n)
  have hpow (j : ℕ) : IsNef k (X ↘ S) (a ^ j) := by
    induction j with
    | zero => simpa only [pow_zero] using isNef_one k (X ↘ S)
    | succ j ih => simpa only [pow_succ] using ih.mul hnef
  have : Subsingleton (Cohomology L.obj 2) :=
    X.subsingleton_cohomology_two_of_isNef_of_isRationalOver k L (hL.symm ▸ hpow n)
  obtain ⟨I, hI, hclass⟩ := L.exists_effectiveCartier_of_eulerCharBelow_pos k
    (hL.symm ▸ hχ) inferInstance
  have hEq : (mk hI.toInvertibleSheaf)⁻¹ = a ^ n := by rw [hclass, inv_inv, hL]
  refine ⟨n, hn, I, hI, ?_, hEq⟩
  rintro rfl
  rw [mk_toInvertibleSheaf_top, inv_one] at hEq
  let B := Chow.classIntersectionBilinForm k hX (Additive.ofMul a)
  have hzero := congrArg (fun b : LineBundleClass X ↦ B (Additive.ofMul b)) hEq
  simp only [ofMul_one, ofMul_pow, map_zero, map_nsmul, B, nsmul_eq_mul,
    Chow.classIntersectionBilinForm_apply, toMul_ofMul] at hzero
  exact (mul_pos (Int.natCast_pos.mpr hn) ha).ne hzero

/-- On a smooth projective rational surface over an algebraically closed field,
every sufficiently high power of a class of positive square that meets an
ample class positively is represented by an effective Cartier divisor. -/
theorem eventually_exists_effectiveCartier_pow_of_positive_cone
    (a : LineBundleClass X) {h : LineBundleClass X} (hh : h.IsAmple)
    (haa : 0 < Chow.classIntersectionNumber k X a a)
    (hha : 0 < Chow.classIntersectionNumber k X h a) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ (I : X.IdealSheafData) (hI : I.IsEffectiveCartier),
      (mk hI.toInvertibleSheaf)⁻¹ = a ^ n := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := rational.isIntegral_of_smooth
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  filter_upwards [eventually_pos_eulerCharBelow_pow_of_self_pos k a hdim haa] with n hn
  obtain ⟨L, hL⟩ := mk_surjective (a ^ n)
  have hb (x y : LineBundleClass X) :
      Chow.intersectionBilinForm k X (Additive.ofMul x) (Additive.ofMul y) =
        Chow.classIntersectionNumber k X x y := by simp
  have h₁ : 0 < Chow.classIntersectionNumber k X (mk L) (mk L) := by
    rw [hL, ← hb]
    simpa only [ofMul_pow, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, hb] using
      mul_pos (Int.natCast_pos.mpr hn.1) (mul_pos (Int.natCast_pos.mpr hn.1) haa)
  have h₂ : 0 < Chow.classIntersectionNumber k X h (mk L) := by
    rw [hL, ← hb, ofMul_pow, map_nsmul, nsmul_eq_mul, hb]
    exact mul_pos (Int.natCast_pos.mpr hn.1) hha
  have hvan := X.subsingleton_cohomology_two_of_self_pos_of_intersection_pos k L hh h₁ h₂
  obtain ⟨I, hI, hclass⟩ := L.exists_effectiveCartier_of_eulerCharBelow_pos k
    (hL.symm ▸ hn.2) hvan
  exact ⟨hn.1, I, hI, by rw [hclass, inv_inv, hL]⟩

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

namespace AlgebraicGeometry.Scheme

open LinearMap.BilinForm TauCeti.AlgebraicGeometry.Chow
open TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

variable {X} [IsIntegral X]

local notation "f" => X ↘ S
local notation "Pic" => Additive (LineBundleClass X)
local notation "K" => Additive.ofMul (LineBundleClass.mk (canonicalBundle k X 2))
local notation "E" => X.effectiveClasses
local notation "B" => intersectionBilinForm k X
local notation "dim₂" => topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)

include rational in
/-- On a smooth projective rational surface of nonnegative canonical square,
the anticanonical class is effective. -/
theorem anticanonical_mem_effectiveClasses (hK : 0 ≤ B K K) : -K ∈ E := by
  have hRR : 2 * (eulerCharBelow k (-K : Pic).toMul 3 - 1) = B (-K) (-K) - B (-K) K := by
    simpa only [intersectionBilinForm_apply, toMul_ofMul] using
      eulerCharBelow_eq_riemannRoch_of_isRationalOver k (-K : Pic).toMul
  simp only [map_neg, LinearMap.neg_apply, neg_neg] at hRR
  rcases mem_effectiveClasses_or_canonical_sub_of_eulerChar_pos k (-K) (by omega) with h | h
  · exact h
  · exact (nsmul_canonical_notMem_effectiveClasses k (by decide : 0 < 2)
      (by simpa only [sub_neg_eq_add, two_nsmul] using h)).elim

variable [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

omit rational in
/-- If a nef class has negative canonical degree, an effective class has a canonical
twist that is effective while its next canonical twist is ineffective. -/
theorem exists_last_effective_adjoint {h a : Pic}
    (hnef : h.toMul.IsNef k f) (hK : B h K < 0) (ha : a ∈ E) :
    ∃ n : ℕ, a + n • K ∈ E ∧ a + (n + 1) • K ∉ E := by
  have hlarge : ∃ n : ℕ, a + n • K ∉ E := by
    refine ⟨(B h a).toNat + 1, fun he ↦ ?_⟩
    have hpos : 0 ≤ B h (a + ((B h a).toNat + 1) • K) := by
      simpa only [intersectionBilinForm_apply] using
        intersection_nonneg_of_mem_effectiveClasses k dim₂ hnef he
    rw [map_add, map_nsmul] at hpos
    have hm := mul_le_mul_of_nonneg_left (show B h K ≤ -1 by omega)
      (Int.natCast_nonneg ((B h a).toNat + 1))
    simp only [nsmul_eq_mul, mul_neg, mul_one] at hpos hm
    omega
  simpa only [not_not] using
    Nat.exists_not_and_succ_of_not_zero_of_exists (by simpa using ha) hlarge

omit rational [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)] in
private theorem exists_positive_class_of_canonical_square_neg {h : Pic}
    (hh : 0 < B h h) (hd₀ : 0 ≤ B h K) (hn : B K K < 0) :
    ∃ y : Pic, 0 < B y y ∧ 0 < B h y ∧ B y K < 0 := by
  have hsym (a b : Pic) : B a b = B b a := by
    simp only [intersectionBilinForm_apply, classIntersectionNumber_comm]
  let q : ℤ := -(B K K)
  let d : ℤ := B h K
  have hq : 0 < q := neg_pos.mpr hn
  -- First move onto the orthogonal of the canonical class, then add it once.
  let x : Pic := q • h + d • K
  have hxK : B x K = 0 := by
    simp only [x, add_left, smul_left, q, d]
    ring
  have hhx : 0 < B h x := by
    simp only [x, add_right, smul_right]
    exact add_pos_of_pos_of_nonneg (mul_pos hq hh) (mul_self_nonneg d)
  have hxx : B x x = q * B h x := by
    calc
      B x x = B x (q • h + d • K) := rfl
      _ = q * B x h + d * B x K := by rw [add_right, smul_right, smul_right]
      _ = q * B h x := by rw [hsym x h, hxK, mul_zero, add_zero]
  let y : Pic := (q + 1) • x + K
  have hyK : B y K = B K K := by simp only [y, add_left, smul_left, hxK, mul_zero, zero_add]
  refine ⟨y, ?_, ?_, hyK.trans_lt hn⟩
  · have hxy : B x y = (q + 1) * B x x := by
      simp only [y, add_right, smul_right, hxK, add_zero]
    have hyy : B y y = (q + 1) * ((q + 1) * B x x) + B K K := calc
      B y y = B ((q + 1) • x + K) y := rfl
      _ = _ := by rw [add_left, smul_left, hxy, hsym K y, hyK]
    have hlt : q < (q + 1) * ((q + 1) * (q * B h x)) := by
      have hhx₁ : 1 ≤ B h x := by omega
      have h₁ : q ≤ q * B h x := le_mul_of_one_le_right hq.le hhx₁
      have h₂ : q * B h x < (q + 1) * (q * B h x) := by
        simpa only [one_mul] using mul_lt_mul_of_pos_right
          (show (1 : ℤ) < q + 1 by omega) (mul_pos hq hhx)
      have h₃ : (q + 1) * (q * B h x) ≤ (q + 1) * ((q + 1) * (q * B h x)) := by
        exact le_mul_of_one_le_left (mul_nonneg (by omega) (mul_pos hq hhx).le) (by omega)
      exact h₁.trans_lt (h₂.trans_le h₃)
    rw [hyy, hxx]
    have h : -(B K K) < (q + 1) * ((q + 1) * (q * B h x)) := hlt
    omega
  · simp only [y, add_right, smul_right]
    exact add_pos_of_pos_of_nonneg (mul_pos (by omega) hhx) hd₀

variable [IsNoetherian X]

include rational in
/-- A smooth projective rational surface of nonpositive canonical square has an effective
Picard class of negative canonical degree. -/
theorem exists_effectiveClass_of_canonical_degree_neg (hK : B K K ≤ 0) :
    ∃ a : Pic, a ∈ E ∧ B a K < 0 := by
  obtain ⟨H, hH⟩ := X.exists_isAmple_of_isProjectiveOver k
  let h : Pic := Additive.ofMul H
  have hh : 0 < B h h := by
    simpa only [h, intersectionBilinForm_apply, toMul_ofMul] using
      classIntersectionNumber_pos_of_isAmple k dim₂ hH hH
  suffices ∃ a : Pic, 0 < B a a ∧ 0 < B h a ∧ B a K < 0 by
    obtain ⟨a, haa, hha, haK⟩ := this
    simp only [intersectionBilinForm_apply, h, toMul_ofMul] at haa hha
    obtain ⟨n, hn, I, hI, he⟩ :=
      (eventually_exists_effectiveCartier_pow_of_positive_cone k a.toMul hH haa hha).exists
    refine ⟨n • a, mem_effectiveClasses.mpr
      ⟨hI.toCartierDivisor, hI.isEffective_toCartierDivisor, by
        rw [hI.toLineBundleClass_toCartierDivisor, he, ofMul_pow, ofMul_toMul]⟩, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℤ, smul_left]
    exact mul_neg_of_pos_of_neg (Int.natCast_pos.mpr hn) haK
  by_cases hneg : B h K < 0
  · exact ⟨h, hh, hh, hneg⟩
  have hkne : K ≠ (0 : Pic) := by
    intro hz
    exact nsmul_canonical_notMem_effectiveClasses k (X := X) (by decide : 0 < 2)
      (by rw [hz, nsmul_zero]; exact (X.effectiveClasses).zero_mem)
  have hn : B K K < 0 := by
    by_contra! hzero
    have heq := le_antisymm hK hzero
    have hA := anticanonical_mem_effectiveClasses k heq.ge
    have hpos : 0 < B h (-K) := by
      simpa only [h, intersectionBilinForm_apply, toMul_ofMul] using
        intersection_pos_of_mem_effectiveClasses k dim₂ hH hA (neg_ne_zero.mpr hkne)
    rw [map_neg] at hpos
    omega
  exact exists_positive_class_of_canonical_square_neg k hh (le_of_not_gt hneg) hn

end AlgebraicGeometry.Scheme
