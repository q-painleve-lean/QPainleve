/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
public import QPainleve.AlgebraicGeometry.CartierDivisor.ZeroDivisor
public import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
public import QPainleve.AlgebraicGeometry.WeilDivisor.LinearSystem.BaseIdeal
public import TauCeti.AlgebraicGeometry.Chow.SurfaceIntersection
public import TauCeti.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.LinearSystem
import QPainleve.AlgebraicGeometry.Blowup.Projective.Global
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.WeilDivisor.LinearSystem.Intersection
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Principalization of surface linear systems by point blowups

For a nonempty family of effective divisors in a common Picard class on a smooth
integral projective surface, a finite tower of closed point blowups makes the
total transform of its base ideal effective Cartier. The length of the tower is
bounded by the square of the moving class.

Each step removes the common exceptional multiplicity. The square of the moving
class decreases strictly when the center is a base point and stays nonnegative
because the residual system has no fixed components.

## References

* [P. Hacking, *583C Lecture notes*, Proposition 7.3](https://paulhacking.github.io/surfaces.pdf#page=38).
-/

open AlgebraicGeometry CategoryTheory Order TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open QPainleve TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.SchemeWeilDivisor

variable {X : Scheme.{u}}

section BaseLocus

variable [IsIntegral X] [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
  {S : Set (SchemeWeilDivisor X)} (hS : ∀ D ∈ S, 0 ≤ D) (hne : S.Nonempty)

include hne in
private theorem isClosed_of_mem_support_baseIdeal_of_no_fixed_components
    (hX : topologicalKrullDim X ≤ 2)
    (hmove : ∀ p : CodimensionOnePoint X, ∃ D ∈ S, D p = 0)
    {p : X} (hp : p ∈ (baseIdeal S hS).support) : IsClosed ({p} : Set X) := by
  have hfixed := (WeilDivisor.fixedPart_eq_zero_iff hne hS).mpr hmove
  have htop (D : SchemeWeilDivisor X) (hD : 0 ≤ D) (hzero : D = 0) :
      idealSheaf D hD = ⊤ := by
    subst D
    exact idealSheaf_zero
  have hI := baseIdeal_eq_mul_movingPart hS hne
  rw [htop _ _ hfixed, ← one_eq_top, one_mul] at hI
  exact mem_closedPoints_iff.mp
    (support_baseIdeal_movingPart_subset_closedPoints hS hne hX (hI ▸ hp))

end BaseLocus

section SmoothSurface

variable (k : Type u) [Field k] [IsAlgClosed k]

variable [X.Over (Spec (.of k))] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

private theorem exists_residual_system_of_base_point
    [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    {S : Set (SchemeWeilDivisor X)} (hS : ∀ D ∈ S, 0 ≤ D) (hne : S.Nonempty)
    (a : LineBundleClass X)
    (hclass : ∀ D ∈ S, (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul = a)
    (hmove : ∀ q : CodimensionOnePoint X, ∃ D ∈ S, D q = 0)
    (p : X) [IsRegularLocalRing (X.presheaf.stalk p)] (hpclosed : IsClosed ({p} : Set X))
    (hpdim : ringKrullDim (X.presheaf.stalk p) = 2) (hp : p ∈ (baseIdeal S hS).support) :
    let I := (X.fromSpecResidueField p).ker
    let _ : I.blowup.Over (Spec (.of k)) := ⟨I.blowupToBase ≫ X ↘ Spec (.of k)⟩
    ∀ [IsIntegral I.blowup] [IsNoetherian I.blowup]
      [∀ x : I.blowup, UniqueFactorizationMonoid (I.blowup.presheaf.stalk x)],
    I.blowup.IsProjectiveOver k →
    ∃ (S' : Set (SchemeWeilDivisor I.blowup)) (hS' : ∀ D ∈ S', 0 ≤ D)
      (_ : S'.Nonempty) (a' : LineBundleClass I.blowup),
      (∀ D ∈ S', (Scheme.CartierDivisor.weilToLineBundleClassHom I.blowup D).toMul = a') ∧
        (∀ q : CodimensionOnePoint I.blowup, ∃ D ∈ S', D q = 0) ∧
        Chow.classIntersectionNumber k I.blowup a' a' < Chow.classIntersectionNumber k X a a ∧
        (baseIdeal S hS).comap I.blowupToBase = baseIdeal S' hS' *
          (I.comap I.blowupToBase) ^ ((baseIdeal S hS).stalkOrder p).toNat := by
  dsimp only
  intro hIntegral hNoetherian hFactorial hprojective
  let I := (X.fromSpecResidueField p).ker
  let : I.blowup.Over (Spec (.of k)) := ⟨I.blowupToBase ≫ X ↘ Spec (.of k)⟩
  have : IsNormalScheme I.blowup := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let transform := pointBlowupTransform p hS hne hpclosed hpdim
  let S' := Set.range transform
  have hS' : ∀ D ∈ S', 0 ≤ D :=
    fun _ ⟨D, hD⟩ ↦ hD ▸ pointBlowupTransform_nonneg p hS hne hpclosed hpdim D
  have hne' : S'.Nonempty := ⟨transform ⟨hne.choose, hne.choose_spec⟩, Set.mem_range_self _⟩
  have hmove' (q : CodimensionOnePoint I.blowup) : ∃ D ∈ S', D q = 0 := by
    obtain ⟨D, hD⟩ := exists_pointBlowupTransform_coeff_eq_zero p hS hne hpclosed hpdim hmove q
    exact ⟨transform D, Set.mem_range_self _, hD⟩
  let m := ((baseIdeal S hS).stalkOrder p).toNat
  let a' := LineBundleClass.pullback I.blowupToBase a *
    (LineBundleClass.mk I.isEffectiveCartier_comap_blowupToBase.toInvertibleSheaf) ^ m
  have hclass' (D : SchemeWeilDivisor I.blowup) (hD : D ∈ S') :
      (Scheme.CartierDivisor.weilToLineBundleClassHom I.blowup D).toMul = a' := by
    obtain ⟨d, rfl⟩ := hD
    rw [toMul_weilToLineBundleClassHom_pointBlowupTransform p hS hne hpclosed hpdim,
      hclass d.val d.property]
  have hlt :
      Chow.classIntersectionNumber k I.blowup a' a' < Chow.classIntersectionNumber k X a a := by
    let D : S := ⟨hne.choose, hne.choose_spec⟩
    rw [← hclass D.val D.property, ← hclass' _ (Set.mem_range_self D)]
    exact classIntersectionNumber_pointBlowupTransform_lt p hS hne hpclosed hpdim k D hp
      hprojective
  refine ⟨S', hS', hne', a', hclass', hmove', hlt, ?_⟩
  rw [baseIdeal_range_pointBlowupTransform p hS hne hpclosed hpdim]
  apply eq_colon_mul _ _
    (TauCeti.isEffectiveCartier_pow I.isEffectiveCartier_comap_blowupToBase m).locallyPrincipal
  rw [← comap_pow]
  exact comap_mono _ ((natCast_le_stalkOrder_iff_le_pow_ker_fromSpecResidueField
    p _ hpclosed m).mp (ENat.natCast_toNat_le_self _))

variable [X.IsProjectiveOver k]

private theorem exists_moving_baseIdeal_resolution (bound : ℕ)
    [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    {S : Set (SchemeWeilDivisor X)} (hS : ∀ D ∈ S, 0 ≤ D) (hne : S.Nonempty)
    (a : LineBundleClass X)
    (hclass : ∀ D ∈ S, (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul = a)
    (hmove : ∀ p : CodimensionOnePoint X, ∃ D ∈ S, D p = 0)
    (hbound : Chow.classIntersectionNumber k X a a ≤ bound) :
    ∃ (n : ℕ) (Y : Scheme.{u}) (T : BlowupTower X n Y),
      n ≤ bound ∧ T.IsClosedPointTower ∧ Surjective T.toBase ∧
        ((baseIdeal S hS).comap T.toBase).IsEffectiveCartier := by
  classical
  induction bound using Nat.strong_induction_on generalizing X with
  | ind bound ih =>
    by_cases htop : baseIdeal S hS = ⊤
    · refine ⟨0, X, .nil, Nat.zero_le _, .nil, ?_, ?_⟩
      · simpa only [BlowupTower.toBase_nil] using (inferInstance : Surjective (𝟙 X))
      · simpa only [htop, BlowupTower.toBase_nil, comap_id] using isEffectiveCartier_top X
    have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)
    obtain ⟨p, hp⟩ : (↑(baseIdeal S hS).support : Set X).Nonempty := by
      by_contra hempty
      apply htop
      apply (support_eq_bot_iff _).mp
      exact SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.mp hempty)
    have hpclosed := isClosed_of_mem_support_baseIdeal_of_no_fixed_components hS hne hX.le hmove hp
    let I := (X.fromSpecResidueField p).ker
    have hpdim :=
      ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (X ↘ Spec (.of k)) 2).mp
        inferInstance).2 p hpclosed
    have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
    have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
    let T₁ : BlowupTower X 1 I.blowup := BlowupTower.nil.snoc I
    have hT₁ : T₁.IsClosedPointTower := .snoc .nil p hpclosed rfl
    let : I.blowup.Over (Spec (.of k)) := ⟨I.blowupToBase ≫ X ↘ Spec (.of k)⟩
    have : I.blowup.IsProjectiveOver k := I.isProjectiveOver_blowup_of_isNoetherianRing k
    have : IsNoetherian I.blowup := T₁.isNoetherian
    have : IsIntegral I.blowup := hT₁.isIntegral (X ↘ Spec (.of k))
    have hover : I.blowup ↘ Spec (.of k) = I.blowupToBase ≫ X ↘ Spec (.of k) := rfl
    have : SmoothOfRelativeDimension 2 (I.blowup ↘ Spec (.of k)) := by
      rw [hover]
      simpa only [T₁, BlowupTower.toBase_snoc, BlowupTower.toBase_nil, Category.comp_id]
        using hT₁.smoothOfRelativeDimension (X ↘ Spec (.of k))
    have : Surjective I.blowupToBase := by
      dsimp only [I]
      rw [X.ker_fromSpecResidueField_eq_vanishingIdeal]
      exact surjective_blowupToBase_point hpclosed hpdim
    have : ∀ x : I.blowup, UniqueFactorizationMonoid (I.blowup.presheaf.stalk x) :=
      (I.blowup ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    obtain ⟨S', hS', hne', a', hclass', hmove', hlt, hprod⟩ :=
      exists_residual_system_of_base_point k hS hne a hclass hmove p hpclosed hpdim hp
        inferInstance
    have hnonneg := Chow.classIntersectionNumber_self_nonneg_of_no_fixed_components k
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension (I.blowup ↘ Spec (.of k)) (n := 2))
      hS' hne' hclass' (fun q ↦ (notMem_support_baseIdeal_iff hS').mpr (hmove' q))
    let b := (Chow.classIntersectionNumber k I.blowup a' a').toNat
    have hb : (b : ℤ) = Chow.classIntersectionNumber k I.blowup a' a' := Int.toNat_of_nonneg hnonneg
    have hbLt : b < bound := Int.ofNat_lt.mp (hb.trans_lt (hlt.trans_le hbound))
    obtain ⟨n, Y, U, hn, hU, hsurj, hcart⟩ := ih b hbLt hS' hne' a' hclass' hmove' hb.ge
    have hcomp : (T₁.append U).toBase = U.toBase ≫ I.blowupToBase := by
      simp [T₁]
    refine ⟨1 + n, Y, T₁.append U, by omega, hT₁.append hU, ?_, ?_⟩
    · rw [hcomp]
      infer_instance
    have : IsIntegral Y := hU.isIntegral (I.blowup ↘ Spec (.of k))
    have hE := I.isEffectiveCartier_comap_blowupToBase
    have hE' := hE.comap_of_isIntegral U.toBase (by
      rw [U.toBase.genericPoint_eq_of_isDominant]
      exact hE.genericPoint_notMem_support)
    rw [hcomp, comap_comp, hprod, comap_mul, comap_pow]
    exact TauCeti.isEffectiveCartier_mul hcart (TauCeti.isEffectiveCartier_pow hE' _)

/-- A finite tower of closed point blowups principalizes the base ideal of a nonempty family
of effective divisors of the same Picard class. The length is at most the self-intersection
of the moving class, and the tower projection is surjective. -/
public theorem exists_closedPointTower_isEffectiveCartier_baseIdeal
    {S : Set (SchemeWeilDivisor X)}
    (hS : ∀ D ∈ S, 0 ≤ D) (hne : S.Nonempty)
    (a : LineBundleClass X) :
    letI : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
    letI : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (∀ D ∈ S, (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul = a) →
    let b := a / (Scheme.CartierDivisor.weilToLineBundleClassHom X
      (WeilDivisor.fixedPart S hne hS)).toMul
    ∃ (n : ℕ) (Y : Scheme.{u}) (T : BlowupTower X n Y),
      (n : ℤ) ≤ Chow.classIntersectionNumber k X b b ∧ T.IsClosedPointTower ∧
        Surjective T.toBase ∧ ((baseIdeal S hS).comap T.toBase).IsEffectiveCartier := by
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  have : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  dsimp only
  intro hclass
  let F := WeilDivisor.fixedPart S hne hS
  let b := a / (Scheme.CartierDivisor.weilToLineBundleClassHom X F).toMul
  let M := WeilDivisor.movingPart S hne hS
  have hM (D : SchemeWeilDivisor X) (hD : D ∈ M) : 0 ≤ D :=
    WeilDivisor.nonneg_of_mem_movingPart hne hS hD
  have hclassM (D : SchemeWeilDivisor X) (hD : D ∈ M) :
      (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul = b := by
    have h := hclass _ ((WeilDivisor.mem_movingPart_iff hne hS).mp hD)
    rw [map_add, toMul_add] at h
    exact eq_div_iff_mul_eq'.mpr h
  have hnonneg := Chow.classIntersectionNumber_movingPart_self_nonneg k
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2))
    hS hne hclass
  have hb : ((Chow.classIntersectionNumber k X b b).toNat : ℤ) =
      Chow.classIntersectionNumber k X b b := Int.toNat_of_nonneg hnonneg
  obtain ⟨n, Y, T, hn, hT, hsurj, hCartier⟩ := exists_moving_baseIdeal_resolution k _
    hM (WeilDivisor.movingPart_nonempty hne hS) b hclassM
    (WeilDivisor.exists_mem_movingPart_apply_eq_zero hne hS) hb.ge
  have hn' : (n : ℤ) ≤ Chow.classIntersectionNumber k X b b := (Int.ofNat_le.mpr hn).trans hb.le
  refine ⟨n, Y, T, hn', hT, hsurj, ?_⟩
  have : IsIntegral Y := hT.isIntegral (X ↘ Spec (.of k))
  have hF := isEffectiveCartier_idealSheaf F (WeilDivisor.fixedPart_nonneg hne hS)
  rw [baseIdeal_eq_mul_movingPart hS hne, comap_mul]
  exact TauCeti.isEffectiveCartier_mul (hF.comap_of_isIntegral _ (by
    rw [T.toBase.genericPoint_eq_of_isDominant]
    exact hF.genericPoint_notMem_support)) hCartier

end SmoothSurface

end TauCeti.AlgebraicGeometry.SchemeWeilDivisor

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

/-- For a family of global sections of a line bundle with at least one nonzero section,
a finite tower of closed point blowups makes the total transform of the sum of their
zero ideals effective Cartier. -/
public theorem exists_closedPointTower_isEffectiveCartier_iSup_zeroIdeal
    {X : Scheme.{u}} (L : InvertibleSheaf X) (k : Type u) [Field k] [IsAlgClosed k]
    [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    {ι : Type*} (s : ι → Γ(L.obj, ⊤)) (hs : ∃ i, s i ≠ 0) :
    ∃ (n : ℕ) (Y : Scheme.{u}) (T : BlowupTower X n Y),
      T.IsClosedPointTower ∧ Surjective T.toBase ∧
        ((⨆ i, L.zeroIdeal (s i)).comap T.toBase).IsEffectiveCartier := by
  classical
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  have : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let J := {i // s i ≠ 0}
  let D (i : J) := (L.zeroDivisor i.property).toWeilDivisor
  let S := Set.range D
  have hS : ∀ E ∈ S, 0 ≤ E := fun _ ⟨i, hi⟩ ↦ hi ▸
    (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
      (L.isEffective_zeroDivisor i.property)
  have hne : S.Nonempty := ⟨D ⟨hs.choose, hs.choose_spec⟩, Set.mem_range_self _⟩
  have hclass : ∀ E ∈ S, (Scheme.CartierDivisor.weilToLineBundleClassHom X E).toMul =
      LineBundleClass.mk L := by
    rintro _ ⟨i, rfl⟩
    dsimp only [D]
    rw [Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor, toMul_ofMul,
      L.toLineBundleClass_zeroDivisor]
  have hideal : SchemeWeilDivisor.baseIdeal S hS = ⨆ i : J, L.zeroIdeal (s i) :=
    SchemeWeilDivisor.baseIdeal_range_toWeilDivisor_zeroDivisor L
      (fun i : J ↦ s i) (fun i ↦ i.property)
  have hsum : (⨆ i : J, L.zeroIdeal (s i)) = ⨆ i, L.zeroIdeal (s i) := by
    rw [iSup_subtype]
    calc
      _ = ⨆ i, ⨆ _ : L.zeroIdeal (s i) ≠ ⊥, L.zeroIdeal (s i) := by
        refine iSup_congr fun i ↦ iSup_congr_Prop
          ((not_congr (L.zeroIdeal_eq_bot_iff (s i))).symm) (fun _ ↦ rfl)
      _ = _ := by
        simpa only [iSup_subtype] using iSup_ne_bot_subtype (fun i ↦ L.zeroIdeal (s i))
  obtain ⟨n, Y, T, _, hT, hsurj, hcart⟩ :=
    SchemeWeilDivisor.exists_closedPointTower_isEffectiveCartier_baseIdeal k hS hne _ hclass
  exact ⟨n, Y, T, hT, hsurj, (hideal.trans hsum) ▸ hcart⟩

end TauCeti.AlgebraicGeometry.InvertibleSheaf
