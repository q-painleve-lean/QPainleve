/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.NakaiMoishezon
public import QPainleve.AlgebraicGeometry.LineBundle.EffectiveClass

import QPainleve.AlgebraicGeometry.Chow.Ample
import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.IntersectionNumber.GlobalGeneration
import QPainleve.AlgebraicGeometry.LineBundle.Ample

/-!
# Ample and nef classes on rational surfaces

A nef class on a smooth projective rational surface has nonnegative square.
Tensoring an ample class with a nef class is therefore ample by Nakai–Moishezon.
The ample twists by powers of one nef class also show that any two nef classes
have nonnegative intersection. A Picard isometry identifying the effective-class
monoids preserves ampleness in both directions.

See [Debarre, *Introduction to Mori Theory*, §4.2]
(https://perso.imj-prg.fr/wp-content/uploads/debarre-pub/M22.pdf).
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.LineBundleClass

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [rational : Scheme.IsRationalOver (X ↘ Spec (.of k))]

local notation "f" => (X ↘ Spec (CommRingCat.of k))
local notation "B" => Chow.classIntersectionNumber k X

private theorem isAmple_pow_mul_pow_of_self_pos {h a : LineBundleClass X}
    (hh : h.IsAmple) (ha : a.IsNef k f) {m n : ℕ} (hm : 0 < m)
    (hsq : 0 < B (h ^ m * a ^ n) (h ^ m * a ^ n)) :
    (h ^ m * a ^ n).IsAmple := by
  refine (isAmple_iff_self_pos_and_intersectionNumber_pos _).mpr ⟨hsq, ?_⟩
  intro C _ _ i _ hi
  have : RelativeDimensionLE 1 (C ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  rw [intersectionNumber_mul_of_isIntegral, intersectionNumber_pow_of_isIntegral,
    intersectionNumber_pow_of_isIntegral]
  exact add_pos_of_pos_of_nonneg
    (mul_pos (Int.natCast_pos.mpr hm) (hh.intersectionNumber_pos i))
    (mul_nonneg (Int.natCast_nonneg n) (ha.intersectionNumber_nonneg i hi))

/-- A nef line-bundle class on a smooth projective rational surface has nonnegative
self-intersection. -/
theorem IsNef.classIntersectionNumber_self_nonneg {a : LineBundleClass X}
    (ha : a.IsNef k f) : 0 ≤ B a a := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := rational.isIntegral_of_smooth
  obtain ⟨h, hh⟩ := X.exists_isAmple_of_isProjectiveOver k
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have (x : X) : UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two x
  have hab := ha.classIntersectionNumber_nonneg_of_isAmple hX hh
  have hhh := Chow.classIntersectionNumber_pos_of_isAmple k hX hh hh
  by_contra! hneg
  let c := -B a a
  let b := B a h
  have hc : 0 < c := neg_pos.mpr hneg
  -- The twist is just past the orthogonal direction: its intersection with `a` is `-c`,
  -- while its square is still positive.
  let m := (2 * c).toNat
  let n := (2 * b + 1).toNat
  have hm : (m : ℤ) = 2 * c := Int.toNat_of_nonneg (by omega)
  have hn : (n : ℤ) = 2 * b + 1 := Int.toNat_of_nonneg (by omega)
  have hm' : 0 < m := by omega
  have hsq : 0 < B (h ^ m * a ^ n) (h ^ m * a ^ n) := by
    simp only [Chow.classIntersectionNumber_mul_left k hX,
      Chow.classIntersectionNumber_mul_right k hX, Chow.classIntersectionNumber_pow_left k hX,
      Chow.classIntersectionNumber_pow_right k hX, hm, hn, Chow.classIntersectionNumber_comm h a]
    have hca : 1 ≤ c * B h h := by
      exact Int.add_one_le_iff.mpr (mul_pos hc hhh)
    have hpos : 0 < 4 * (c * B h h) + 4 * b ^ 2 - 1 := by nlinarith [sq_nonneg b]
    calc
      0 < c * (4 * (c * B h h) + 4 * b ^ 2 - 1) := mul_pos hc hpos
      _ = _ := by dsimp [b, c]; ring
  have htest := ha.classIntersectionNumber_nonneg_of_isAmple hX
    (isAmple_pow_mul_pow_of_self_pos hh ha hm' hsq)
  have hpair : B a (h ^ m * a ^ n) = -c := by
    simp only [Chow.classIntersectionNumber_mul_right k hX,
      Chow.classIntersectionNumber_pow_right k hX, hm, hn]
    dsimp [b, c]
    ring
  omega

/-- Tensoring an ample line-bundle class with a nef class on a smooth projective
rational surface preserves ampleness. -/
theorem IsAmple.mul_of_isNef {h a : LineBundleClass X} (hh : h.IsAmple)
    (ha : a.IsNef k f) : (h * a).IsAmple := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := rational.isIntegral_of_smooth
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have (x : X) : UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two x
  have hhh := Chow.classIntersectionNumber_pos_of_isAmple k hX hh hh
  have hmix := ha.classIntersectionNumber_nonneg_of_isAmple hX hh
  have hself := ha.classIntersectionNumber_self_nonneg
  suffices hsq : 0 < B (h * a) (h * a) by
    simpa only [pow_one] using
      isAmple_pow_mul_pow_of_self_pos hh ha (m := 1) (n := 1) Nat.one_pos (by simpa using hsq)
  rw [Chow.classIntersectionNumber_mul_left k hX, Chow.classIntersectionNumber_mul_right k hX,
    Chow.classIntersectionNumber_mul_right k hX, Chow.classIntersectionNumber_comm h a]
  omega

/-- A homomorphism of Picard groups that sends nef classes to nef classes preserves
ampleness on a rational target if its image contains an ample class. -/
theorem IsAmple.map_of_isNef_preserving {Y : Scheme.{u}} {a h : LineBundleClass Y} (ha : a.IsAmple)
    (fY : Y ⟶ Spec (.of k)) (g : LineBundleClass Y →* LineBundleClass X)
    (hnef : ∀ b : LineBundleClass Y, b.IsNef k fY → (g b).IsNef k f) (hh : (g h).IsAmple) :
    (g a).IsAmple := by
  obtain ⟨n, hn, hb⟩ := ((Filter.eventually_gt_atTop (0 : ℕ)).and
    (ha.eventually_isNef_mul_pow h⁻¹ fY)).exists
  apply IsAmple.of_pow hn
  have ht := hh.mul_of_isNef (hnef _ hb)
  simpa only [map_mul, map_inv, map_pow, ← mul_assoc, mul_inv_cancel, one_mul] using ht

/-- Two nef line-bundle classes on a smooth projective rational surface have nonnegative
intersection. -/
theorem IsNef.classIntersectionNumber_nonneg {a b : LineBundleClass X}
    (ha : a.IsNef k f) (hb : b.IsNef k f) : 0 ≤ B a b := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := rational.isIntegral_of_smooth
  obtain ⟨h, hh⟩ := X.exists_isAmple_of_isProjectiveOver k
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have (x : X) : UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two x
  have hample (n : ℕ) : (h * b ^ n).IsAmple := by
    induction n with
    | zero => simpa using hh
    | succ n ih => simpa only [pow_succ, ← mul_assoc] using ih.mul_of_isNef hb
  by_contra! hneg
  -- A negative intersection would eventually make the intersection with an ample twist negative.
  obtain ⟨n, hn⟩ := exists_nat_gt (B a h)
  have hnonneg := ha.classIntersectionNumber_nonneg_of_isAmple hX (hample n)
  rw [Chow.classIntersectionNumber_mul_right k hX,
    Chow.classIntersectionNumber_pow_right k hX] at hnonneg
  have hbound : (n : ℤ) * B a b ≤ (n : ℤ) * (-1) :=
    mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg n)
  omega

end TauCeti.AlgebraicGeometry.LineBundleClass

namespace TauCeti.AlgebraicGeometry.Chow

open LineBundleClass TopologicalSpace

variable (k : Type u) [Field k] [IsAlgClosed k]

local notation "S" => Spec (CommRingCat.of k)
local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "B(" X ")" => classIntersectionNumber k X
local notation "Bℤ(" X ")" => intersectionBilinForm k X
local notation "P" => primeDivisorClass
local notation "cl(" X ")" => Scheme.CartierDivisor.weilToLineBundleClassHom X

section

variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [Y.IsProjectiveOver k] [IsIntegral X] [IsIntegral Y]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]

variable [IsNoetherian X] [IsNoetherian Y]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]

variable (e : LinearMap.BilinForm.IsometryEquiv (intersectionBilinForm k X)
  (intersectionBilinForm k Y))

variable [rationalY : Scheme.IsRationalOver (Y ↘ Spec (.of k))]

include rationalY in
private theorem ample_of_effective_preimage
    (hmap : Set.MapsTo e.symm (Y.effectiveClasses : Set Pic(Y)) (X.effectiveClasses : Set Pic(X)))
    {a : LineBundleClass X} (ha : a.IsAmple) : (e (Additive.ofMul a)).toMul.IsAmple := by
  let b := (e (Additive.ofMul a)).toMul
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have hY := topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y ↘ S) (n := 2)
  apply (isAmple_iff_self_pos_and_intersectionNumber_pos (k := k) b).mpr
  have hself : B(Y) b b = B(X) a a := by
    simpa only [b, intersectionBilinForm_apply, toMul_ofMul] using
      e.map_app (Additive.ofMul a) (Additive.ofMul a)
  refine ⟨hself.symm ▸ classIntersectionNumber_pos_of_isAmple k hX ha ha, ?_⟩
  intro C _ _ i _ hi
  let : i.IsOver S := ⟨hi.symm⟩
  have hC := Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := C) k
  let r : CodimensionOnePoint Y :=
    ⟨i (genericPoint C), i.coheight_apply_genericPoint_eq_one_of_dim_eq_two k hY hC⟩
  rw [← classIntersectionNumber_primeDivisorClass_eq_intersectionNumber_of_isClosedImmersion
    k hY i hC]
  obtain ⟨A, hA, hclass⟩ :=
    Scheme.mem_effectiveClasses_iff_exists_weilDivisor.mp
      (hmap (Scheme.primeDivisorClass_mem_effectiveClasses r))
  have hm : e (cl(X) A) = Additive.ofMul (P r) :=
    (congrArg e hclass).trans (e.apply_symm_apply _)
  have hne : A ≠ 0 := by
    rintro rfl
    have h := congrArg Additive.toMul hm
    simp only [map_zero, toMul_zero, toMul_ofMul] at h
    obtain ⟨H, hH⟩ := Y.exists_isAmple_of_isProjectiveOver k
    have hy : 0 < B(Y) H (P r) :=
      classIntersectionNumber_primeDivisorClass_pos_of_isAmple k hY hH r
    rw [← h, classIntersectionNumber_one_right] at hy
    exact (lt_irrefl 0) hy
  have hpos := classIntersectionNumber_weilToLineBundleClassHom_pos_of_isAmple k hX ha hA hne
  have he := e.map_app (cl(X) A) (Additive.ofMul a)
  simp only [intersectionBilinForm_apply, hm, toMul_ofMul] at he
  exact he.symm ▸ hpos

end

variable {F G : Scheme.{u}} [F.Over (Spec (.of k))] [G.Over (Spec (.of k))]
  [F.IsProjectiveOver k] [G.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (F ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (G ↘ Spec (.of k))]
  [hF : Scheme.IsRationalOver (F ↘ Spec (.of k))]
  [hG : Scheme.IsRationalOver (G ↘ Spec (.of k))]

/-- An isometry identifying the effective-class monoids of smooth projective rational surfaces
preserves ampleness in both directions. -/
theorem isAmple_iff_of_map_effectiveClasses (a : LineBundleClass F) :
    let : Smooth (F ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : Smooth (G ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : IsIntegral F := hF.isIntegral_of_smooth
    let : IsIntegral G := hG.isIntegral_of_smooth
    let : IsNoetherian F := isNoetherian_of_finiteType (F ↘ S)
    let : IsNoetherian G := isNoetherian_of_finiteType (G ↘ S)
    let : ∀ x : F, UniqueFactorizationMonoid (F.presheaf.stalk x) :=
      (F ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let : ∀ y : G, UniqueFactorizationMonoid (G.presheaf.stalk y) :=
      (G ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    ∀ (e : (Bℤ(F)).IsometryEquiv (Bℤ(G))),
      F.effectiveClasses.map e.toLinearEquiv.toAddMonoidHom = G.effectiveClasses →
      ((e (Additive.ofMul a)).toMul.IsAmple ↔ a.IsAmple) := by
  intro _ _ _ _ _ _ _ _ e h
  have hf : Set.MapsTo e (F.effectiveClasses : Set Pic(F)) (G.effectiveClasses : Set Pic(G)) := by
    intro x hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  have hb : Set.MapsTo e.symm (G.effectiveClasses : Set Pic(G))
      (F.effectiveClasses : Set Pic(F)) := by
    intro y hy
    rw [← h] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    have heq : e x = y := hxy
    have hsymm : e.symm y = x := (congrArg e.symm heq.symm).trans (e.symm_apply_apply x)
    exact hsymm.symm ▸ hx
  refine ⟨fun ha ↦ ?_, ample_of_effective_preimage k e hb⟩
  have hi := ample_of_effective_preimage k e.symm hf ha
  rw [ofMul_toMul] at hi
  have heq : (e.symm (e (Additive.ofMul a))).toMul = a :=
    congrArg Additive.toMul (e.symm_apply_apply (Additive.ofMul a))
  exact heq ▸ hi

end TauCeti.AlgebraicGeometry.Chow
