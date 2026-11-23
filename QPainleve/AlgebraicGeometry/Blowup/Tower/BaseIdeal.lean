/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Intersection
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
public import QPainleve.AlgebraicGeometry.WeilDivisor.LinearSystem.BaseIdeal
import QPainleve.AlgebraicGeometry.Blowup.LinearSystem
import QPainleve.AlgebraicGeometry.Blowup.Projective.Global
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.WeilDivisor.LinearSystem.Intersection
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Principalization of base ideals on surfaces

The base ideal of a nonempty family of linearly equivalent effective divisors on a smooth
integral projective surface becomes effective Cartier after finitely many point blowups.
The self-intersection of the moving class bounds the number of blowups. The result keeps
the actual pullback ideal, so it can be used to divide a family of sections by its common divisor.

## References

* [P. Hacking, *583C Lecture notes*, Proposition 7.3](https://paulhacking.github.io/surfaces.pdf#page=38).
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open QPainleve QPainleve.BlowupTower

universe u

namespace TauCeti.AlgebraicGeometry.SchemeWeilDivisor

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

local notation "cl[" Y ", " D "]" =>
  Additive.toMul (Scheme.CartierDivisor.weilToLineBundleClassHom Y D)
local notation "sq[" Y ", " a "]" => Chow.classIntersectionNumber k Y a a

private theorem exists_isClosedPointTower_of_moving_bound (bound : ℕ)
    {S : Set (SchemeWeilDivisor X)} {a : LineBundleClass X}
    (hS : ∀ D ∈ S, 0 ≤ D) (hne : S.Nonempty)
    (hclass : ∀ D ∈ S, cl[X, D] = a)
    (hmove : ∀ p : CodimensionOnePoint X, (p : X) ∉ (baseIdeal S hS).support)
    (hbound : sq[X, a] ≤ bound) :
    ∃ (n : ℕ) (Y : Scheme.{u}) (T : BlowupTower X n Y),
      IsClosedPointTower X T ∧ n ≤ bound ∧
        ((baseIdeal S hS).comap T.toBase).IsEffectiveCartier := by
  induction bound using Nat.strong_induction_on generalizing X with
  | ind bound ih =>
    let B := baseIdeal S hS
    by_cases hB : B = ⊤
    · refine ⟨0, X, .nil, .nil, Nat.zero_le _, ?_⟩
      rw [show baseIdeal S hS = ⊤ from hB, comap_top]
      exact isEffectiveCartier_top X
    have hnonempty : (B.support : Set X).Nonempty :=
      Set.ne_empty_iff_nonempty.mp fun h ↦
        hB ((support_eq_bot_iff B).mp (Closeds.coe_eq_empty.mp h))
    obtain ⟨p, hpB, hp⟩ := B.support.isClosed.exists_closed_singleton hnonempty
    -- Supply the surface structure on the first blowup to the transform and the induction.
    let P := (X.fromSpecResidueField p).ker
    let Y := P.blowup
    let f := X ↘ Spec (.of k)
    let E := P.comap P.blowupToBase
    let m := (B.stalkOrder p).toNat
    let first : BlowupTower X 1 Y := BlowupTower.nil.snoc P
    have hfirst : IsClosedPointTower X first := IsClosedPointTower.nil.snoc p hp rfl
    have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
    have : IsRegularLocalRing (X.presheaf.stalk p) := isRegularLocalRing_stalk_of_smooth f p
    have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp inferInstance).2 p hp
    let : Y.Over (Spec (.of k)) := ⟨P.blowupToBase ≫ f⟩
    have hproj : Y.IsProjectiveOver k := P.isProjectiveOver_blowup_of_isNoetherianRing k
    have : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) := by
      have h := hfirst.smoothOfRelativeDimension f
      simp only [first, toBase_snoc, toBase_nil, Category.comp_id] at h
      exact h
    have : IsIntegral Y := hfirst.isIntegral f
    have : IsNoetherian Y := first.isNoetherian
    have : Smooth (Y ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
    have : IsRegular Y := IsRegular.of_smooth (Y ↘ Spec (.of k))
    have hY := topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y ↘ Spec (.of k)) (n := 2)
    have : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y) := fun y ↦
      IsRegular.uniqueFactorizationMonoid_stalk y
        (WithBot.coe_le_coe.mp ((TauCeti.coheight_le_topologicalKrullDim y).trans hY.le))
    let transform := pointBlowupTransform p hS hne hp hdim
    let hS' : ∀ D ∈ Set.range transform, 0 ≤ D :=
      fun _ ⟨D, hD⟩ ↦ hD ▸ pointBlowupTransform_nonneg p hS hne hp hdim D
    let a' := LineBundleClass.pullback P.blowupToBase a *
      LineBundleClass.mk P.isEffectiveCartier_comap_blowupToBase.toInvertibleSheaf ^ m
    have hclass' : ∀ D ∈ Set.range transform, cl[Y, D] = a' := by
      rintro _ ⟨D, rfl⟩
      rw [toMul_weilToLineBundleClassHom_pointBlowupTransform, hclass _ D.property]
    have hmove' (y : CodimensionOnePoint Y) : (y : Y) ∉ (baseIdeal _ hS').support := by
      obtain ⟨D, hD⟩ := exists_pointBlowupTransform_coeff_eq_zero p hS hne hp hdim
        (fun x ↦ (notMem_support_baseIdeal_iff hS).mp (hmove x)) y
      exact (notMem_support_baseIdeal_iff hS').mpr ⟨transform D, Set.mem_range_self D, hD⟩
    have hne' : (Set.range transform).Nonempty := hne.to_subtype.elim fun D ↦
      ⟨transform D, Set.mem_range_self D⟩
    -- The new family is moving, so the smaller self-intersection is still nonnegative.
    let next := (sq[Y, a']).toNat
    have hnext : (next : ℤ) = sq[Y, a'] := Int.toNat_of_nonneg
      (Chow.classIntersectionNumber_self_nonneg_of_no_fixed_components k hY hS' hne' hclass' hmove')
    have hlt : sq[Y, a'] < sq[X, a] := by
      have hmember := hne
      obtain ⟨D, hD⟩ := hmember
      have hlt := classIntersectionNumber_pointBlowupTransform_lt p hS hne hp hdim
        k ⟨D, hD⟩ hpB hproj
      rw [hclass' _ (Set.mem_range_self ⟨D, hD⟩), hclass _ hD] at hlt
      exact hlt
    have hnextlt : next < bound := by
      exact_mod_cast hnext.trans_lt (hlt.trans_le hbound)
    obtain ⟨n, Z, T, hT, hn, hcartier⟩ :=
      ih next hnextlt hS' hne' hclass' hmove' hnext.ge
    refine ⟨1 + n, Z, first.append T, hfirst.append hT, by omega, ?_⟩
    -- The tail principalizes the moving ideal. Its pullback of the removed power is Cartier too.
    have hE := isEffectiveCartier_pow P.isEffectiveCartier_comap_blowupToBase m
    have hm : (m : ℕ∞) ≤ B.stalkOrder p :=
      (ENat.natCast_toNat (stalkOrder_baseIdeal_lt_top hS hne p).ne).le
    have hle : B.comap P.blowupToBase ≤ E ^ m := by
      rw [← comap_pow]
      exact comap_mono _
        ((natCast_le_stalkOrder_iff_le_pow_ker_fromSpecResidueField p B hp m).mp hm)
    have hfactor : B.comap P.blowupToBase = baseIdeal _ hS' * E ^ m := by
      rw [baseIdeal_range_pointBlowupTransform p hS hne hp hdim]
      exact eq_colon_mul _ _ hE.locallyPrincipal hle
    simp only [toBase_append, first, toBase_snoc, toBase_nil, Category.comp_id, comap_comp]
    rw [(show (baseIdeal S hS).comap P.blowupToBase = _ from hfactor), comap_mul]
    have : Surjective T.toBase := hT.surjective (Y ↘ Spec (.of k))
    have : IsIntegral Z := hT.isIntegral (Y ↘ Spec (.of k))
    exact isEffectiveCartier_mul hcartier (hE.comap_of_isDominant T.toBase)

/-- A nonempty family of linearly equivalent effective divisors on a smooth integral
projective surface has a base ideal whose pullback to a finite tower of closed point blowups
is effective Cartier. The number of blowups is bounded by the self-intersection of the
moving class. -/
theorem exists_isClosedPointTower_isEffectiveCartier_comap_baseIdeal
    {S : Set (SchemeWeilDivisor X)} {a : LineBundleClass X}
    (hS : ∀ D ∈ S, 0 ≤ D) (hne : S.Nonempty) (hclass : ∀ D ∈ S, cl[X, D] = a) :
    let b := a / cl[X, WeilDivisor.fixedPart S hne hS]
    ∃ (n : ℕ) (Y : Scheme.{u}) (T : BlowupTower X n Y),
      IsClosedPointTower X T ∧ (n : ℤ) ≤ sq[X, b] ∧
        ((baseIdeal S hS).comap T.toBase).IsEffectiveCartier := by
  dsimp only
  let F : SchemeWeilDivisor X := WeilDivisor.fixedPart S hne hS
  let b := a / cl[X, F]
  have hclass' : ∀ D ∈ WeilDivisor.movingPart S hne hS, cl[X, D] = b := by
    intro D hD
    apply eq_div_iff_mul_eq'.mpr
    simpa only [← toMul_add, ← map_add] using hclass (D + F)
      ((WeilDivisor.mem_movingPart_iff hne hS).mp hD)
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)
  have hnonneg := Chow.classIntersectionNumber_movingPart_self_nonneg k hX hS hne hclass
  have hcast : ((sq[X, b]).toNat : ℤ) = sq[X, b] := Int.toNat_of_nonneg hnonneg
  obtain ⟨n, Y, T, hT, hn, hM⟩ := exists_isClosedPointTower_of_moving_bound k (sq[X, b]).toNat
    (fun _ ↦ WeilDivisor.nonneg_of_mem_movingPart hne hS)
    (WeilDivisor.movingPart_nonempty hne hS) hclass'
    (notMem_support_baseIdeal_movingPart hS hne) hcast.ge
  have hlength : (n : ℤ) ≤ sq[X, b] := hcast ▸ (Int.ofNat_le.mpr hn)
  refine ⟨n, Y, T, hT, hlength, ?_⟩
  rw [baseIdeal_eq_mul_movingPart hS hne, comap_mul]
  have : Surjective T.toBase := hT.surjective (X ↘ Spec (.of k))
  have : IsIntegral Y := hT.isIntegral (X ↘ Spec (.of k))
  exact isEffectiveCartier_mul
    ((isEffectiveCartier_idealSheaf F (WeilDivisor.fixedPart_nonneg hne hS)).comap_of_isDominant
      T.toBase) hM

end TauCeti.AlgebraicGeometry.SchemeWeilDivisor

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

open SchemeWeilDivisor

/-- The common zero ideal of a family of sections of a line bundle on a smooth integral
projective surface becomes effective Cartier after a finite tower of closed point blowups.
At least one section must be nonzero. -/
theorem exists_isClosedPointTower_isEffectiveCartier_comap_iSup_zeroIdeal
    {X : Scheme.{u}} (L : InvertibleSheaf X) (k : Type u) [Field k] [IsAlgClosed k]
    [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    {ι : Type*} (s : ι → Γ(L.obj, ⊤)) (hs : ∃ i, s i ≠ 0) :
    ∃ (n : ℕ) (Y : Scheme.{u}) (T : BlowupTower X n Y),
      IsClosedPointTower X T ∧ ((⨆ i, L.zeroIdeal (s i)).comap T.toBase).IsEffectiveCartier := by
  let f := X ↘ Spec (.of k)
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsNoetherian X := isNoetherian_of_finiteType f
  have : IsRegular X := IsRegular.of_smooth f
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) := fun x ↦
    IsRegular.uniqueFactorizationMonoid_stalk x
      (WithBot.coe_le_coe.mp ((TauCeti.coheight_le_topologicalKrullDim x).trans hX.le))
  let D (i : {i // s i ≠ 0}) := (L.zeroDivisor i.property).toWeilDivisor
  have hD : ∀ i, 0 ≤ D i := fun i ↦
    (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
      (L.isEffective_zeroDivisor i.property)
  let hS : ∀ C ∈ Set.range D, 0 ≤ C := fun _ ⟨i, hi⟩ ↦ hi ▸ hD i
  have hne : (Set.range D).Nonempty := by
    obtain ⟨i, hi⟩ := hs
    exact ⟨D ⟨i, hi⟩, Set.mem_range_self _⟩
  have hclass : ∀ C ∈ Set.range D,
      (Scheme.CartierDivisor.weilToLineBundleClassHom X C).toMul = LineBundleClass.mk L := by
    rintro _ ⟨i, rfl⟩
    dsimp only [D]
    rw [Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor, toMul_ofMul,
      toLineBundleClass_zeroDivisor]
  have hsum : baseIdeal (Set.range D) hS = ⨆ i, L.zeroIdeal (s i) := by
    refine (baseIdeal_range_toWeilDivisor_zeroDivisor L (fun i : {i // s i ≠ 0} ↦ s i)
      (fun i ↦ i.property)).trans ?_
    simpa only [iSup_subtype, ne_eq, zeroIdeal_eq_bot_iff] using
      iSup_ne_bot_subtype (fun i ↦ L.zeroIdeal (s i))
  obtain ⟨n, Y, T, hT, _, hI⟩ :=
    exists_isClosedPointTower_isEffectiveCartier_comap_baseIdeal k hS hne hclass
  exact ⟨n, Y, T, hT, hsum ▸ hI⟩

end TauCeti.AlgebraicGeometry.InvertibleSheaf
