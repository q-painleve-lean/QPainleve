/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Intersection
public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Residual
public import QPainleve.AlgebraicGeometry.WeilDivisor.LinearSystem.BaseIdeal
public import TauCeti.AlgebraicGeometry.IdealSheaf.Colon
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Dominant

/-!
# Moving linear systems on point blowups

On the blowup of a base point, divide the ideal of every pulled-back member by the same
exceptional power. Its exponent is the least vanishing order in the original family.
The transformed base ideal has no divisorial support if the original family has no fixed
components. The common divisor class has self-intersection lower by the square of this order.

## References

* P. Hacking, *583C Lecture notes*, Proposition 7.3.
-/

public section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace
open TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} (p : X)

local notation "P" => Scheme.Hom.ker (Scheme.fromSpecResidueField X p)
local notation "π" => blowupToBase P
local notation "E" => comap P π
local notation "hE" => isEffectiveCartier_comap_blowupToBase P

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Dividing every total-transform ideal by a common admissible exceptional power divides the
total transform of their sum by the same power. -/
theorem iSup_comap_blowupToBase_colon_exceptional_pow
    (hp : IsClosed ({p} : Set X)) {ι : Type*} (J : ι → X.IdealSheafData) (n : ℕ)
    (hn : (n : ℕ∞) ≤ (⨆ i, J i).stalkOrder p) :
    (⨆ i, ((J i).comap π).colon (E ^ n)) = ((⨆ i, J i).comap π).colon (E ^ n) := by
  have hn' : (⨆ i, J i).comap π ≤ E ^ n := by
    rw [← comap_pow]
    exact comap_mono π ((natCast_le_stalkOrder_iff_le_pow_ker_fromSpecResidueField p _ hp n).mp hn)
  have hle (i : ι) : (J i).comap π ≤ E ^ n :=
    (comap_mono π (le_iSup J i)).trans hn'
  have hF := TauCeti.isEffectiveCartier_pow hE n
  apply hF.mul_left_cancel
  rw [mul_comm (E ^ n), (gc_mul_colon (E ^ n)).l_iSup,
    mul_comm (E ^ n), ← eq_colon_mul _ _ hF.locallyPrincipal hn',
    (map_gc π).l_iSup]
  exact iSup_congr fun i ↦ (eq_colon_mul _ _ hF.locallyPrincipal (hle i)).symm

section Support

variable [IsIntegral X] [IsLocallyNoetherian X] [IsRegularLocalRing (X.presheaf.stalk p)]
  (hp : IsClosed ({p} : Set X)) (hdim : ringKrullDim (X.presheaf.stalk p) = 2)

include hp hdim

private theorem notMem_support_colon_exceptional_of_mem_exceptional (J : X.IdealSheafData)
    (m : ℕ) (hm : J.stalkOrder p = m) (x : CodimensionOnePoint (P).blowup)
    (hx : (x : (P).blowup) ∈ (E).support) :
    (x : (P).blowup) ∉ (((J.comap π).colon (E ^ m)).support) := by
  have : IsLocallyNoetherian (P).blowup := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsIntegral (E).subscheme :=
    (isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hdim).isIntegral_subscheme
  have hxη := ((hE).mem_support_iff_eq_subschemeι_genericPoint x.property).mp hx
  let R := (J.comap π).colon (E ^ m)
  intro hxR
  have hsub : ((E).support : Set (P).blowup) ⊆ (R.support : Set (P).blowup) := by
    rw [(E).support_eq_closure_subschemeι_genericPoint, ← hxη]
    exact R.support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hxR)
  have hRE : R ≤ E := by
    have hclosed : (E).support ≤ R.support := fun _ hx ↦ hsub hx
    have hs := le_support_iff_le_vanishingIdeal.mp hclosed
    rw [vanishingIdeal_support, ((E).isReduced_subscheme_iff_radical_eq).mp inferInstance] at hs
    exact hs
  have hF := TauCeti.isEffectiveCartier_pow hE m
  have hle := (comap_blowupToBase_le_exceptional_pow_iff p hp hdim J m).mpr hm.ge
  have hle' : J.comap π ≤ E ^ (m + 1) := calc
    J.comap π = R * E ^ m := eq_colon_mul _ _ hF.locallyPrincipal hle
    _ ≤ E * E ^ m := fun U ↦ by
      simpa only [ideal_mul, Pi.mul_apply] using Ideal.mul_mono (hRE U) le_rfl
    _ = E ^ (m + 1) := (pow_succ' _ _).symm
  have h := (comap_blowupToBase_le_exceptional_pow_iff p hp hdim J (m + 1)).mp hle'
  rw [hm, ENat.natCast_le_natCast] at h
  omega

/-- A base ideal with no codimension-one support keeps that property after pullback and division
by the exceptional power of its exact stalk order. -/
theorem notMem_support_comap_blowupToBase_colon_exceptional_pow (J : X.IdealSheafData)
    (hJ : ∀ x : CodimensionOnePoint X, (x : X) ∉ J.support) (m : ℕ) (hm : J.stalkOrder p = m)
    (x : CodimensionOnePoint (P).blowup) :
    (x : (P).blowup) ∉ (((J.comap π).colon (E ^ m)).support) := by
  by_cases hx : (x : (P).blowup) ∈ (E).support
  · exact notMem_support_colon_exceptional_of_mem_exceptional p hp hdim J m hm x hx
  let U := (P).support.compl
  have hxU : (x : (P).blowup) ∈ π ⁻¹ᵁ U := by
    rw [← compl_support_comap]
    exact hx
  let y : (π ⁻¹ᵁ U).toScheme := ⟨x, hxU⟩
  have hι : IsOpenImmersion ((π ⁻¹ᵁ U).ι ≫ π) := by
    have : IsIso (π ∣_ U) := (P).isIso_blowupToBase_restrict_compl_support
    rw [← morphismRestrict_ι]
    exact IsOpenImmersion.comp _ _
  have hcodim := (coheight_eq_of_isOpenImmersion (x := y) ((π ⁻¹ᵁ U).ι ≫ π)).trans
    (coheight_eq_of_isOpenImmersion (x := y) (π ⁻¹ᵁ U).ι).symm
  have hpull : (x : (P).blowup) ∉ (J.comap π).support :=
    fun h ↦ hJ ⟨π x, hcodim.trans x.property⟩ (by
      simpa only [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage] using h)
  exact fun h ↦ hpull (support_antitone (le_colon _ _) h)

end Support

end AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry.SchemeWeilDivisor

variable [IsIntegral X] [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
  {S : Set (SchemeWeilDivisor X)} (hS : ∀ D ∈ S, 0 ≤ D) (hne : S.Nonempty)

local notation "m" => ENat.toNat (stalkOrder (baseIdeal S hS) p)
local notation "R" => fun D : S ↦ colon (comap (D.val.idealSheaf (hS D D.property)) π) (E ^ m)

include hne

private theorem stalkOrder_baseIdeal_eq_natCast :
    (baseIdeal S hS).stalkOrder p = (m : ℕ∞) :=
  (ENat.natCast_toNat (stalkOrder_baseIdeal_lt_top hS hne p).ne).symm

/-- After subtracting the common exceptional power, the base ideal is the sum of the
transformed member ideals. This version keeps the original indexing by divisors. -/
private theorem iSup_comap_idealSheaf_colon_exceptional_pow (hp : IsClosed ({p} : Set X)) :
    (⨆ D : S, R D) = ((baseIdeal S hS).comap π).colon (E ^ m) := by
  let J := fun D : S ↦ D.val.idealSheaf (hS D D.property)
  have hn : (m : ℕ∞) ≤ (⨆ D, J D).stalkOrder p :=
    baseIdeal_eq_iSup hS ▸ (stalkOrder_baseIdeal_eq_natCast p hS hne).ge
  exact (iSup_comap_blowupToBase_colon_exceptional_pow p hp J m hn).trans
    (congrArg (fun I : X.IdealSheafData ↦ (I.comap π).colon (E ^ m)) (baseIdeal_eq_iSup hS).symm)

/-- A nonempty moving system on a regular point blowup has no new fixed components after
each member is reduced by the common exceptional power. -/
private theorem notMem_support_iSup_comap_idealSheaf_colon_exceptional_pow
    [IsRegularLocalRing (X.presheaf.stalk p)]
    (hp : IsClosed ({p} : Set X)) (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (hmove : ∀ x : CodimensionOnePoint X, ∃ D ∈ S, D x = 0) (x : CodimensionOnePoint (P).blowup) :
    (x : (P).blowup) ∉ (⨆ D : S, R D).support := by
  rw [iSup_comap_idealSheaf_colon_exceptional_pow p hS hne hp]
  exact notMem_support_comap_blowupToBase_colon_exceptional_pow p hp hdim _
    (fun y ↦ (notMem_support_baseIdeal_iff hS).mpr (hmove y)) m
    (stalkOrder_baseIdeal_eq_natCast p hS hne) x

private theorem natCast_baseIdeal_stalkOrder_le_member (D : S) :
    (m : ℕ∞) ≤ (D.val.idealSheaf (hS D D.property)).stalkOrder p :=
  (stalkOrder_baseIdeal_eq_natCast p hS hne).symm.le.trans
    (stalkOrder_anti ((le_iSup (fun D : S ↦ D.val.idealSheaf (hS D D.property)) D).trans
      (baseIdeal_eq_iSup hS).ge) p)

/-- Each transformed member is an effective Cartier divisor. -/
private theorem isEffectiveCartier_comap_idealSheaf_colon_exceptional_pow
    [IsRegularLocalRing (X.presheaf.stalk p)]
    (hp : IsClosed ({p} : Set X)) (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (D : S) :
    (R D).IsEffectiveCartier :=
  IsEffectiveCartier.comap_blowupToBase_colon_exceptional_pow p hp hdim
    (D.val.isEffectiveCartier_idealSheaf (hS D D.property)) m
    (natCast_baseIdeal_stalkOrder_le_member p hS hne D)

section WeilTransform

variable [IsRegularLocalRing (X.presheaf.stalk p)]
  [IsIntegral (X.fromSpecResidueField p).ker.blowup]
  [IsNoetherian (X.fromSpecResidueField p).ker.blowup]
  (hp : IsClosed ({p} : Set X)) (hdim : ringKrullDim (X.presheaf.stalk p) = 2)

section Normal

variable [IsNormalScheme (X.fromSpecResidueField p).ker.blowup]

/-- The transform of a member of an effective divisor system on a point blowup.
Subtract the same exceptional multiplicity, computed from the entire system, from each
total transform. -/
noncomputable def pointBlowupTransform (D : S) : SchemeWeilDivisor (P).blowup :=
  let hR := isEffectiveCartier_comap_idealSheaf_colon_exceptional_pow p hS hne hp hdim D
  hR.toCartierDivisor.toWeilDivisor

/-- The transformed divisor is effective, even when its original order exceeds the base order. -/
@[simp]
theorem pointBlowupTransform_nonneg (D : S) : 0 ≤ pointBlowupTransform p hS hne hp hdim D :=
  let hR := isEffectiveCartier_comap_idealSheaf_colon_exceptional_pow p hS hne hp hdim D
  (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp hR.isEffective_toCartierDivisor

end Normal

variable [∀ x : (X.fromSpecResidueField p).ker.blowup,
  UniqueFactorizationMonoid ((X.fromSpecResidueField p).ker.blowup.presheaf.stalk x)]

attribute [local instance] IsNormalScheme.of_uniqueFactorizationMonoid_stalk

/-- The ideal of a transformed member is the residual of its total-transform ideal. -/
theorem idealSheaf_pointBlowupTransform (D : S) :
    (pointBlowupTransform p hS hne hp hdim D).idealSheaf
        (pointBlowupTransform_nonneg p hS hne hp hdim D) = R D := by
  let hR := isEffectiveCartier_comap_idealSheaf_colon_exceptional_pow p hS hne hp hdim D
  exact (idealSheaf_toWeilDivisor hR.isEffective_toCartierDivisor).trans
    hR.idealSheaf_toCartierDivisor

/-- The base ideal of the transformed system is the total transform of the original
base ideal divided by the common exceptional power. -/
theorem baseIdeal_range_pointBlowupTransform :
    baseIdeal (Set.range (pointBlowupTransform p hS hne hp hdim))
        (fun _ ⟨D, hD⟩ ↦ hD ▸ pointBlowupTransform_nonneg p hS hne hp hdim D) =
      ((baseIdeal S hS).comap π).colon (E ^ m) := by
  let T := pointBlowupTransform p hS hne hp hdim
  let hT : ∀ D ∈ Set.range T, 0 ≤ D :=
    fun _ ⟨D, hD⟩ ↦ hD ▸ pointBlowupTransform_nonneg p hS hne hp hdim D
  let j (D : S) : Set.range T := ⟨T D, Set.mem_range_self D⟩
  have hj : Function.Surjective j := by
    rintro ⟨_, D, rfl⟩
    exact ⟨D, rfl⟩
  calc
    baseIdeal (Set.range T) hT =
        ⨆ D : Set.range T, D.val.idealSheaf (hT D D.property) := baseIdeal_eq_iSup hT
    _ = ⨆ D : S, (T D).idealSheaf (hT (T D) (j D).property) := (hj.iSup_comp _).symm
    _ = ⨆ D : S, R D := iSup_congr (idealSheaf_pointBlowupTransform p hS hne hp hdim)
    _ = _ := iSup_comap_idealSheaf_colon_exceptional_pow p hS hne hp

/-- If the original system has no fixed components, the transformed system also has no fixed
components, including along the exceptional divisor. -/
theorem exists_pointBlowupTransform_coeff_eq_zero
    (hmove : ∀ x : CodimensionOnePoint X, ∃ D ∈ S, D x = 0)
    (x : CodimensionOnePoint (P).blowup) :
    ∃ D : S, pointBlowupTransform p hS hne hp hdim D x = 0 := by
  have hx := notMem_support_iSup_comap_idealSheaf_colon_exceptional_pow p hS hne hp hdim hmove x
  rw [support_iSup, Closeds.mem_iInf] at hx
  push Not at hx
  obtain ⟨D, hD⟩ := hx
  refine ⟨D, (coeff_eq_zero_iff_notMem_support _ (pointBlowupTransform_nonneg p hS hne hp hdim D)
    x).mpr ?_⟩
  rwa [idealSheaf_pointBlowupTransform]

/-- The Picard class of the transformed member is the pullback class with the common exceptional
multiplicity subtracted. -/
theorem toMul_weilToLineBundleClassHom_pointBlowupTransform (D : S) :
    (Scheme.CartierDivisor.weilToLineBundleClassHom (P).blowup
      (pointBlowupTransform p hS hne hp hdim D)).toMul =
      LineBundleClass.pullback π (Scheme.CartierDivisor.weilToLineBundleClassHom X D.val).toMul *
        (LineBundleClass.mk (hE).toInvertibleSheaf) ^ m := by
  let hD := D.val.isEffectiveCartier_idealSheaf (hS D D.property)
  have hWeil : hD.toCartierDivisor.toWeilDivisor = D.val := by
    rw [toCartierDivisor_idealSheaf,
      SchemeWeilDivisor.toWeilDivisor_equivCartierDivisorOfUniqueFactorizationMonoid]
  have hclass := Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor hD.toCartierDivisor
  rw [hWeil] at hclass
  rw [pointBlowupTransform, Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor,
    hclass, toMul_ofMul, toMul_ofMul,
    IsEffectiveCartier.toLineBundleClass_toCartierDivisor,
    IsEffectiveCartier.toLineBundleClass_toCartierDivisor]
  exact IsEffectiveCartier.toLineBundleClass_comap_blowupToBase_colon_exceptional_pow p hp hdim hD
    m (natCast_baseIdeal_stalkOrder_le_member p hS hne D)

section Intersection

variable (k : Type u) [Field k] [IsAlgClosed k] [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

/-- The self-intersection of each transformed member drops by the square of the common
base-point multiplicity. -/
theorem classIntersectionNumber_pointBlowupTransform (D : S) :
    let _ : (P).blowup.Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    (P).blowup.IsProjectiveOver k →
      let a := (Scheme.CartierDivisor.weilToLineBundleClassHom X D.val).toMul
      let b := (Scheme.CartierDivisor.weilToLineBundleClassHom (P).blowup
        (pointBlowupTransform p hS hne hp hdim D)).toMul
      Chow.classIntersectionNumber k (P).blowup b b =
        Chow.classIntersectionNumber k X a a - (m : ℤ) ^ 2 := by
  dsimp only
  intro hproj
  rw [toMul_weilToLineBundleClassHom_pointBlowupTransform]
  let a := (Scheme.CartierDivisor.weilToLineBundleClassHom X D.val).toMul
  simpa only [zpow_neg, zpow_natCast, inv_pow, inv_inv, neg_mul, mul_neg, neg_neg, pow_two]
    using Chow.classIntersectionNumber_pointBlowup p k hp a a (-(m : ℤ)) (-(m : ℤ)) hproj

/-- At a base point the transformed system has strictly smaller self-intersection. -/
theorem classIntersectionNumber_pointBlowupTransform_lt (D : S)
    (hbase : p ∈ (baseIdeal S hS).support) :
    let _ : (P).blowup.Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    (P).blowup.IsProjectiveOver k →
      let a := (Scheme.CartierDivisor.weilToLineBundleClassHom X D.val).toMul
      let b := (Scheme.CartierDivisor.weilToLineBundleClassHom (P).blowup
        (pointBlowupTransform p hS hne hp hdim D)).toMul
      Chow.classIntersectionNumber k (P).blowup b b < Chow.classIntersectionNumber k X a a := by
  dsimp only
  intro hproj
  rw [classIntersectionNumber_pointBlowupTransform p hS hne hp hdim k D hproj]
  have hm : (0 : ℤ) < m := by
    have h := (one_le_stalkOrder_iff (baseIdeal S hS) p).mpr hbase
    rw [stalkOrder_baseIdeal_eq_natCast p hS hne] at h
    exact_mod_cast ENat.natCast_le_natCast.mp h
  exact sub_lt_self _ (sq_pos_of_pos hm)

end Intersection

end WeilTransform

end TauCeti.AlgebraicGeometry.SchemeWeilDivisor
