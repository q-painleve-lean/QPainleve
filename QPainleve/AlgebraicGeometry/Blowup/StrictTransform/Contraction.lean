/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Canonical
public import TauCeti.AlgebraicGeometry.Curves.Node.Relative
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.FinitePresentation

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.Picard
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Regular
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import QPainleve.AlgebraicGeometry.WeilDivisor.Excision
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.Extension
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# Anticanonical boundaries under point blowdown

The schematic image of a reduced anticanonical divisor is reduced anticanonical.
The total transform adds the exceptional divisor once. If the boundary contains
the exceptional curve the center has order two, and otherwise it has order one.
In the order-one case a nodal boundary maps isomorphically to its image.

These are the divisor calculations for the two types of blowups in
[Gross, Hacking and Keel, *Mirror symmetry for log Calabi–Yau surfaces I*,
Proposition 1.3](https://arxiv.org/html/1106.4977v3#S1.Thmproposition3).
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open LineBundleClass

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {p : X}

local notation "I" => vanishingIdeal (Closeds.mk (closure (singleton p)) isClosed_closure)
local notation "π" => blowupToBase I
local notation "E" => comap I π
local notation "strict(" D ")" => Scheme.Hom.ker (blowupMap I (subschemeι D))
local notation "S(" k ")" => Spec (CommRingCat.of k)
local notation "base[" k "," X "]" => (X ↘ Spec (CommRingCat.of k))
local notation "K(" k "," Y ")" => LineBundleClass.mk (QPainleve.canonicalBundle k Y 2)

variable (k : Type u) [Field k] [PerfectField k] [IsIntegral X] [X.Over S(k)]
  [hSmooth : SmoothOfRelativeDimension 2 (base[k,X])] [IsNoetherian X]
  (hp : IsClosed ({p} : Set X))

local notation "off" => Closeds.compl (support E)
local notation "j" => Scheme.Opens.ι (off)
local notation "imageOff(" B ")" => map (comap B j) (j ≫ π)

include hSmooth in
omit [PerfectField k] in
private theorem isEffectiveCartier_imageOff {B : (I).blowup.IdealSheafData}
    (hB : B.IsEffectiveCartier) [IsReduced B.subscheme] :
    (imageOff(B)).IsEffectiveCartier := by
  have := (base[k,X]).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hIso : IsIso (π ∣_ (I).support.compl) :=
    (I).isIso_blowupToBase_restrict_compl_support
  have : IsOpenImmersion (j ≫ π) := by
    rw [compl_support_comap, ← morphismRestrict_ι]
    infer_instance
  have : IsReduced (B.comap j).subscheme := by
    rw [isReduced_subscheme_iff_radical_eq, radical_comap_of_isOpenImmersion,
      B.isReduced_subscheme_iff_radical_eq.mp inferInstance]
  exact (hB.comap j).map_of_isOpenImmersion _

include hp hSmooth in
omit [PerfectField k] [IsIntegral X] in
private theorem strictTransform_imageOff_pow {B : (I).blowup.IdealSheafData}
    (hB : B.IsEffectiveCartier) [IsReduced B.subscheme] :
    ∃ a : ℕ, a ≤ 1 ∧ (a = 1 ↔ (E).support ≤ B.support) ∧
      strict(imageOff(B)) * E ^ a = B := by
  have : Smooth (base[k,X]) := SmoothOfRelativeDimension.smooth 2 _
  have := isRegularLocalRing_stalk_of_smooth (base[k,X]) p
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (base[k,X]) 2).mp
    inferInstance).2 p hp
  have : IsIntegral (E).subscheme := isIntegral_exceptional_blowup_closed_point hdim hp
  have : IsNoetherian (I).blowup := isNoetherian_of_finiteType π
  have : IsOpenImmersion (j ≫ π) := by
    rw [compl_support_comap, ← morphismRestrict_ι]
    have := (I).isIso_blowupToBase_restrict_compl_support
    infer_instance
  let C := (B.comap j).map j
  have hC : strict(imageOff(B)) = C := by
    rw [ker_blowupMap_subschemeι_eq_map_comap, ← comap_comp, comap_map_of_isOpenImmersion]
  by_cases hE : (E).support ≤ B.support
  · refine ⟨1, le_rfl, iff_of_true rfl hE, ?_⟩
    rw [pow_one, ← inf_ker_blowupMap_subschemeι_exceptional, hC]
    have hsup : C.support ⊔ (E).support = B.support := by
      dsimp only [C]
      rw [support_map, support_comap B j]
      apply SetLike.coe_injective
      simp only [Closeds.coe_sup, Closeds.coe_closure, Closeds.coe_preimage,
        Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Closeds.coe_compl, ← Set.sdiff_eq]
      refine (Set.union_subset (closure_minimal Set.sdiff_subset B.support.isClosed) hE).antisymm ?_
      exact (Set.sdiff_union_of_subset (SetLike.coe_subset_coe.mpr hE)).ge.trans
        (Set.union_subset_union_left _ subset_closure)
    have hred : IsReduced C.subscheme := by
      have heq : B = vanishingIdeal B.support :=
        (vanishingIdeal_support.trans (B.isReduced_subscheme_iff_radical_eq.mp inferInstance)).symm
      dsimp only [C]
      rw [heq, comap_vanishingIdeal_of_isOpenImmersion j, map_vanishingIdeal]
      infer_instance
    have hcv : vanishingIdeal C.support = C :=
      vanishingIdeal_support.trans (C.isReduced_subscheme_iff_radical_eq.mp hred)
    have hev : vanishingIdeal (E).support = E :=
      vanishingIdeal_support.trans ((E).isReduced_subscheme_iff_radical_eq.mp inferInstance)
    rw [← hcv, ← hev, ← vanishingIdeal_sup, hsup, vanishingIdeal_support,
      B.isReduced_subscheme_iff_radical_eq.mp inferInstance]
  · refine ⟨0, zero_le_one, iff_of_false (by decide) hE, ?_⟩
    rw [pow_zero, mul_one, hC]
    apply hB.map_comap_eq_of_codimensionOne_mem_range j
    intro q hq
    rw [Scheme.Opens.range_ι]
    intro hqE
    have he :=
      (I).isEffectiveCartier_comap_blowupToBase.mem_support_iff_eq_subschemeι_genericPoint
        q.property |>.mp hqE
    apply hE
    apply SetLike.coe_subset_coe.mp
    rw [(E).support_eq_closure_subschemeι_genericPoint, ← he]
    exact B.support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hq)

include hp in
private theorem stalkOrder_and_canonical_of_strictTransform
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    {B : (I).blowup.IdealSheafData} (hB : B.IsEffectiveCartier)
    (a : ℕ) (hB' : strict(D) * E ^ a = B) :
    let : (I).blowup.Over S(k) := ⟨π ≫ base[k,X]⟩
    letI : SmoothOfRelativeDimension 2 ((I).blowup ↘ S(k)) :=
      smoothOfRelativeDimension_blowup_closed_point (base[k,X]) hp
    LineBundleClass.mk hB.toInvertibleSheaf = K(k,(I).blowup) →
      D.stalkOrder p = (a : ℕ∞) + 1 ∧ LineBundleClass.mk hD.toInvertibleSheaf = K(k,X) := by
  let : (I).blowup.Over S(k) := ⟨π ≫ base[k,X]⟩
  let : SmoothOfRelativeDimension 2 (base[k,(I).blowup]) :=
    smoothOfRelativeDimension_blowup_closed_point (base[k,X]) hp
  dsimp only
  intro hcan
  have := (base[k,X]).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have := ((I).blowup ↘ S(k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have : Smooth (base[k,X]) := SmoothOfRelativeDimension.smooth 2 _
  have := isRegularLocalRing_stalk_of_smooth (base[k,X]) p
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (base[k,X]) 2).mp
    inferInstance).2 p hp
  have hcoh := coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) (base[k,X]) hp
  have hExceptional : (E).IsExceptionalCurveOfFirstKind := by
    exact (congrArg (fun J : X.IdealSheafData ↦
      (J.comap J.blowupToBase).IsExceptionalCurveOfFirstKind)
      (X.ker_fromSpecResidueField_eq_vanishingIdeal p)).mp
        (isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hdim)
  have hI : ((I).support : Set X) = {p} := by
    rw [coe_support_vanishingIdeal, Closeds.coe_mk]
    exact hp.closure_eq
  let e := (I).picardBlowupEquiv hI (by rw [hcoh]; decide) hExceptional
  let m := (D.stalkOrder p).toNat
  let hS := hD.strictTransform_pointBlowup hp hdim
  let hE := (I).isEffectiveCartier_comap_blowupToBase
  have hclass := congrArg Inv.inv (hD.toLineBundleClass_strictTransform_pointBlowup hp hdim)
  simp only [inv_inv, mul_inv_rev, ← pullback_inv, ← zpow_natCast, inv_zpow] at hclass
  have hBclass := mk_toInvertibleSheaf_congr
    (TauCeti.isEffectiveCartier_mul hS (TauCeti.isEffectiveCartier_pow hE a)) hB hB'
  have hExc : LineBundleClass.mk hE.toInvertibleSheaf = (I).blowupExceptionalClass⁻¹ := by
    rw [blowupExceptionalClass_def, inv_inv]
  rw [mk_toInvertibleSheaf_mul hS (TauCeti.isEffectiveCartier_pow hE a),
    mk_toInvertibleSheaf_pow hE, hclass, hExc] at hBclass
  have heq : e (Additive.ofMul (LineBundleClass.mk hD.toInvertibleSheaf), (m : ℤ) - a) =
      e (Additive.ofMul K(k,X), (1 : ℤ)) := by
    apply Additive.toMul.injective
    simp only [e, picardBlowupEquiv_apply_toMul, toMul_ofMul, zpow_one, zpow_sub,
      ← blowupExceptionalClass_def]
    have hK : K(k,(I).blowup) = pullback π K(k,X) * (I).blowupExceptionalClass :=
      mk_canonicalBundle_pointBlowup k hp
    rw [← hK, ← hcan, ← hBclass]
    simp only [inv_pow, zpow_natCast, m]
    ac_rfl
  have hpairs := e.injective heq
  have hm' : (m : ℤ) - a = 1 := congrArg Prod.snd hpairs
  have hm : (D.stalkOrder p).toNat = a + 1 := by dsimp only [m] at hm'; omega
  have hfinite : D.stalkOrder p ≠ ⊤ := by
    rw [stalkOrder_def, ne_eq, Ideal.localOrder_eq_top_iff_eq_bot]
    exact hD.stalkIdeal_ne_bot p
  refine ⟨?_, Additive.ofMul.injective (congrArg Prod.fst hpairs)⟩
  rw [← ENat.natCast_toNat hfinite, hm, Nat.cast_add, Nat.cast_one]

include hp hSmooth in
/-- A reduced anticanonical effective Cartier divisor on a point blowup descends
to its reduced anticanonical schematic image. The total transform is the original
divisor plus one exceptional divisor. The center has order one if the original
divisor omits the exceptional component, and order two if it contains it. -/
theorem IsEffectiveCartier.anticanonical_boundary_point_blowdown
    {B : (I).blowup.IdealSheafData} (hB : B.IsEffectiveCartier) [IsReduced B.subscheme] :
    let : (I).blowup.Over S(k) := ⟨π ≫ base[k,X]⟩
    let : SmoothOfRelativeDimension 2 (base[k,(I).blowup]) :=
      smoothOfRelativeDimension_blowup_closed_point (base[k,X]) hp
    LineBundleClass.mk hB.toInvertibleSheaf = K(k,(I).blowup) →
    let D := B.map π
    ∃ hD : D.IsEffectiveCartier, IsReduced D.subscheme ∧
      LineBundleClass.mk hD.toInvertibleSheaf = K(k,X) ∧ D.comap π = B * E ∧
      ((D.stalkOrder p = 1 ∧ ¬ (E).support ≤ B.support ∧ strict(D) = B) ∨
       (D.stalkOrder p = 2 ∧ (E).support ≤ B.support ∧ strict(D) * E = B)) := by
  let : (I).blowup.Over S(k) := ⟨π ≫ base[k,X]⟩
  let : SmoothOfRelativeDimension 2 (base[k,(I).blowup]) :=
    smoothOfRelativeDimension_blowup_closed_point (base[k,X]) hp
  dsimp only
  intro hcan
  let D := imageOff(B)
  have hD : D.IsEffectiveCartier := isEffectiveCartier_imageOff k hB
  obtain ⟨a, ha, haE, hstrict : strict(D) * E ^ a = B⟩ := strictTransform_imageOff_pow k hp hB
  obtain ⟨hm, hK⟩ := stalkOrder_and_canonical_of_strictTransform k hp hD hB a hstrict hcan
  have : Smooth (base[k,X]) := SmoothOfRelativeDimension.smooth 2 _
  have := isRegularLocalRing_stalk_of_smooth (base[k,X]) p
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (base[k,X]) 2).mp
    inferInstance).2 p hp
  have htotal : D.comap π = B * E := by
    rw [hD.totalTransform_eq_strictTransform_mul_pow_closedPoint hp hdim, hm,
      ← Nat.cast_one (R := ℕ∞), ← Nat.cast_add, ENat.toNat_natCast, pow_succ, ← mul_assoc, hstrict]
  have hmap : B.map π = D := by
    apply le_antisymm
    · dsimp only [D]
      rw [map_comp]
      exact map_mono π (le_map_comap B j)
    · exact (le_map_iff_comap_le).mpr (htotal.trans_le (fun _ ↦ Ideal.mul_le_left))
  have hred : IsReduced (B.map π).subscheme :=
    inferInstanceAs (IsReduced (B.subschemeι ≫ π).image)
  rw [hmap] at hred ⊢
  refine ⟨hD, hred, hK, htotal, ?_⟩
  interval_cases a
  · exact Or.inl ⟨by simpa using hm, fun h ↦ by have := haE.mpr h; omega,
      by simpa only [pow_zero, mul_one] using hstrict⟩
  · exact Or.inr ⟨by simpa only [Nat.cast_one, one_add_one_eq_two] using hm,
      haE.mp rfl, by simpa only [pow_one] using hstrict⟩

omit [PerfectField k] [IsIntegral X] in
include hp hSmooth in
/-- The schematic image of a reduced Cartier divisor's strict transform under
the blowup of a closed point of a smooth surface recovers the original divisor. -/
theorem IsEffectiveCartier.map_strictTransform_blowupToBase
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier) [IsReduced D.subscheme] :
    (strict(D)).map π = D := by
  let U : X.Opens := (I).support.compl
  have : IsIso (π ∣_ U) := (I).isIso_blowupToBase_restrict_compl_support
  have : IsOpenImmersion (j ≫ π) := by
    rw [compl_support_comap, ← morphismRestrict_ι]
    infer_instance
  rw [ker_blowupMap_subschemeι_eq_map_comap, ← map_comp, ← comap_comp]
  apply hD.map_comap_eq_of_codimensionOne_mem_range (j ≫ π)
  intro x _
  have hx : x.val ≠ p := by
    intro h
    have htwo := coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) (base[k,X]) hp
    rw [← h, x.property] at htwo
    norm_num at htwo
  have hxU : x.val ∈ U := by
    have hI := X.support_ker_fromSpecResidueField_of_isClosed hp
    rw [X.ker_fromSpecResidueField_eq_vanishingIdeal] at hI
    simpa only [← SetLike.mem_coe, U, Closeds.coe_compl, hI, Set.mem_compl_iff,
      Set.mem_singleton_iff] using hx
  rw [compl_support_comap, ← morphismRestrict_ι]
  obtain ⟨z, hz⟩ := (π ∣_ U).surjective (⟨x.val, hxU⟩ : U)
  exact ⟨z, by rw [Scheme.Hom.comp_apply, hz]; rfl⟩

omit [PerfectField k] in
include hp hSmooth in
/-- A reduced Cartier divisor that omits the exceptional curve of a closed-point
blowdown is the strict transform of its schematic image. The total pullback of
this image is the original divisor times a power of the exceptional ideal. -/
theorem IsEffectiveCartier.exists_comap_map_eq_mul_pow_of_pointBlowdown
    {Z : Scheme.{u}} {B : Z.IdealSheafData} (hB : B.IsEffectiveCartier) [IsReduced B.subscheme]
    (e : Z ≅ (I).blowup) {f : Z ⟶ X} (hf : e.hom ≫ π = f)
    (hF : ¬ ((I).comap f).support ≤ B.support) :
    (B.map f).IsEffectiveCartier ∧
      ∃ m : ℕ, (B.map f).comap f = B * ((I).comap f) ^ m := by
  let C := B.comap e.inv
  let hC := hB.comap e.inv
  have : IsReduced C.subscheme := by
    rw [isReduced_subscheme_iff_radical_eq, radical_comap_of_isOpenImmersion,
      B.isReduced_subscheme_iff_radical_eq.mp inferInstance]
  have hEC : ¬ (E).support ≤ C.support := by
    intro h
    have h' : ((E).comap e.hom).support ≤ (C.comap e.hom).support := by
      rw [support_comap (E), support_comap C]
      apply SetLike.coe_subset_coe.mp
      rw [Closeds.coe_preimage, Closeds.coe_preimage]
      exact Set.preimage_mono (SetLike.coe_subset_coe.mpr h)
    rw [← comap_comp, ← comap_comp, hf, Iso.hom_inv_id, comap_id] at h'
    exact hF h'
  let D := imageOff(C)
  have : IsNoetherian (I).blowup := isNoetherian_of_finiteType π
  have hD : D.IsEffectiveCartier := isEffectiveCartier_imageOff k hC
  obtain ⟨a, ha, haE, hs⟩ := strictTransform_imageOff_pow k hp hC
  have ha₀ : a = 0 := by
    by_contra h
    exact hEC (haE.mp (by omega))
  have hstrict : strict(D) = C := by simpa only [D, ha₀, pow_zero, mul_one] using hs
  have : IsReduced (C.comap j).subscheme := by
    rw [isReduced_subscheme_iff_radical_eq, radical_comap_of_isOpenImmersion,
      C.isReduced_subscheme_iff_radical_eq.mp inferInstance]
  have : IsReduced D.subscheme := inferInstanceAs
    (IsReduced (Scheme.Hom.image ((C.comap j).subschemeι ≫ (j ≫ π))))
  have hmap : D = B.map f := by
    rw [← hD.map_strictTransform_blowupToBase k hp, hstrict, ← hf, map_comp]
    have hCmap : C = B.map e.hom := by
      dsimp only [C]
      calc
        B.comap e.inv = ((B.map e.hom).comap e.hom).comap e.inv :=
          congrArg (fun J ↦ J.comap e.inv) (B.comap_map_of_isOpenImmersion e.hom).symm
        _ = B.map e.hom := by rw [← comap_comp, Iso.inv_hom_id, comap_id]
    rw [hCmap]
  have : Smooth (base[k,X]) := SmoothOfRelativeDimension.smooth 2 _
  have := isRegularLocalRing_stalk_of_smooth (base[k,X]) p
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (base[k,X]) 2).mp
    inferInstance).2 p hp
  have ht := hD.totalTransform_eq_strictTransform_mul_pow_closedPoint hp hdim
  dsimp only at ht
  rw [hstrict] at ht
  refine ⟨hmap ▸ hD, (D.stalkOrder p).toNat, ?_⟩
  have hh := congrArg (fun J ↦ J.comap e.hom) ht
  simpa only [← comap_comp, comap_mul, comap_pow, hf, C, Iso.hom_inv_id, comap_id,
    hmap] using hh

include hp hSmooth in
/-- If a reduced anticanonical divisor on a point blowup is a strict transform,
it omits the exceptional curve, and taking its image recovers the divisor downstairs. -/
theorem IsEffectiveCartier.map_eq_and_not_le_support_of_eq_strictTransform
    {B : (I).blowup.IdealSheafData} (hB : B.IsEffectiveCartier) [IsReduced B.subscheme]
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier) [IsReduced D.subscheme]
    (hstrict : strict(D) = B) :
    let : (I).blowup.Over S(k) := ⟨π ≫ base[k,X]⟩
    let : SmoothOfRelativeDimension 2 (base[k,(I).blowup]) :=
      smoothOfRelativeDimension_blowup_closed_point (base[k,X]) hp
    LineBundleClass.mk hB.toInvertibleSheaf = K(k,(I).blowup) →
    B.map π = D ∧ ¬ (E).support ≤ B.support := by
  intro _ _ hK
  have hmap := hstrict ▸ hD.map_strictTransform_blowupToBase k hp
  refine ⟨hmap, ?_⟩
  obtain ⟨_, _, _, _, hcases⟩ := hB.anticanonical_boundary_point_blowdown k hp hK
  rw [hmap, hstrict] at hcases
  rcases hcases with h | h
  · exact h.2.1
  · have he : E = ⊤ :=
      hB.mul_left_cancel (h.2.2.trans (mul_top B).symm)
    have hnonempty : Nonempty (E).subscheme := by
      have : Smooth (base[k,X]) := hSmooth.smooth
      have := isRegularLocalRing_stalk_of_smooth (base[k,X]) p
      have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
        (base[k,X]) 2).mp hSmooth).2 p hp
      have : IsIntegral (E).subscheme := isIntegral_exceptional_blowup_closed_point hdim hp
      exact inferInstance
    have hempty := ((E).subschemeι.ker_eq_top_iff_isEmpty).mp
      ((E).ker_subschemeι.trans he)
    exact (hempty.false (Classical.choice hnonempty)).elim

include hp hSmooth in
private theorem exists_smoothPoint_and_isEffectiveCartier_comap_of_stalkOrder_eq_one
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier) (hm : D.stalkOrder p = 1) :
    let : Smooth (base[k,X]) := SmoothOfRelativeDimension.smooth 2 _
    let : LocallyOfFinitePresentation (D.subschemeι ≫ base[k,X]) :=
      TauCeti.locallyOfFinitePresentation_subschemeι_comp_of_isEffectiveCartier hD
    ∃ q : D.subscheme, D.subschemeι q = p ∧
      q ∈ (D.subschemeι ≫ base[k,X]).smoothLocus ∧ ((I).comap D.subschemeι).IsEffectiveCartier := by
  have hpD : p ∈ D.support := (D.one_le_stalkOrder_iff p).mp hm.ge
  obtain ⟨q, hq⟩ : p ∈ Set.range D.subschemeι := D.range_subschemeι.symm ▸ hpD
  have : Smooth (base[k,X]) := SmoothOfRelativeDimension.smooth 2 _
  have := isRegularLocalRing_stalk_of_smooth (base[k,X]) (D.subschemeι q)
  have : IsRegularLocalRing (D.subscheme.presheaf.stalk q) :=
    (hD.stalkOrder_eq_one_iff_isRegularLocalRing q).mp (hq.symm ▸ hm)
  let f := D.subschemeι ≫ base[k,X]
  have : LocallyOfFinitePresentation f :=
    TauCeti.locallyOfFinitePresentation_subschemeι_comp_of_isEffectiveCartier hD
  have hqS := f.mem_smoothLocus_of_isRegularLocalRing_over_perfectField q
  refine ⟨q, hq, hqS, ?_⟩
  let V := f.smoothLocus
  let q' : V.toScheme := ⟨q, hqS⟩
  let J := (D.subscheme.fromSpecResidueField q).ker
  have hqclosed : IsClosed ({q} : Set D.subscheme) :=
    D.subschemeι.isClosedEmbedding.isClosed_iff_image_isClosed.mpr
      (by simpa only [Set.image_singleton, hq] using hp)
  have hJ : (I).comap D.subschemeι = J := by
    exact (congrArg (fun A : X.IdealSheafData ↦ A.comap D.subschemeι)
      (X.ker_fromSpecResidueField_eq_vanishingIdeal p)).symm.trans
      ((congrArg (fun y ↦ ((X.fromSpecResidueField y).ker).comap D.subschemeι) hq.symm).trans
        (D.subschemeι.comap_ker_fromSpecResidueField_apply q))
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (base[k,X]) 2).mp
    inferInstance).2 _ (hq.symm ▸ hp)
  have hdimq := hD.ringKrullDim_stalk_add_one q
  rw [hdim, ringKrullDim_stalk_eq_coheight] at hdimq
  have hqcodim : Order.coheight q = 1 := by
    apply WithBot.coe_injective
    have hdimq' : (↑(Order.coheight q) : WithBot ℕ∞) + (1 : ℕ) =
        (↑(1 : ℕ∞) : WithBot ℕ∞) + (1 : ℕ) := hdimq.trans (by decide)
    exact le_antisymm ((ENat.WithBot.add_le_add_natCast_right_iff (c := 1)).mp hdimq'.le)
      ((ENat.WithBot.add_le_add_natCast_right_iff (c := 1)).mp hdimq'.ge)
  have hdimD := hD.topologicalKrullDim_subscheme_le (d := 1) (by simpa using
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension (base[k,X]) (n := 2)).le)
  have : IsRegular V.toScheme := IsRegular.of_smooth (V.ι ≫ f)
  have hV : (J.comap V.ι).IsEffectiveCartier := by
    dsimp only [J]
    rw [← (show V.ι q' = q from rfl), Scheme.ker_fromSpecResidueField_eq_vanishingIdeal,
      comap_vanishingIdeal_closure_singleton_apply]
    exact isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular
      (fun x ↦ by
        rw [← coheight_eq_of_isOpenImmersion V.ι]
        exact (WithBot.coe_le_coe.mp ((TauCeti.coheight_le_topologicalKrullDim (V.ι x)).trans
          hdimD)).trans (by decide))
      ((coheight_eq_of_isOpenImmersion V.ι).symm.trans hqcodim)
  rw [hJ]
  refine (isEffectiveCartier_comap_iff_of_support_subset_isoLocus V.ι ?_).mp hV
  have hU : V ≤ V.ι.isoLocus :=
    V.ι.le_isoLocus_iff.mpr (V.ι.isIso_morphismRestrict_of_le_opensRange V.opensRange_ι.ge)
  rw [Scheme.support_ker_fromSpecResidueField_of_isClosed hqclosed]
  exact Set.singleton_subset_iff.mpr (hU hqS)

include hp hSmooth in
/-- A nodal anticanonical boundary on a smooth surface blown up at a closed point,
omitting the exceptional component, descends isomorphically to its schematic image.
The image is again nodal and anticanonical. The center is a smooth point of the image
with multiplicity one, and the total transform is the original boundary plus the
exceptional divisor. -/
theorem IsEffectiveCartier.internalBlowdown_of_anticanonical
    {B : (I).blowup.IdealSheafData} (hB : B.IsEffectiveCartier)
    (hE : ¬ (E).support ≤ B.support) :
    let : (I).blowup.Over S(k) := ⟨π ≫ base[k,X]⟩
    let : SmoothOfRelativeDimension 2 (base[k,(I).blowup]) :=
      smoothOfRelativeDimension_blowup_closed_point (base[k,X]) hp
    AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ π ≫ base[k,X]) →
    LineBundleClass.mk hB.toInvertibleSheaf = K(k,(I).blowup) →
    let D := B.map π
    ∃ hD : D.IsEffectiveCartier,
      LineBundleClass.mk hD.toInvertibleSheaf = K(k,X) ∧
      AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ base[k,X]) ∧
      D.stalkOrder p = 1 ∧ D.comap π = B * E ∧ strict(D) = B ∧
      ((I).comap D.subschemeι).IsEffectiveCartier ∧
      (let : Smooth (base[k,X]) := SmoothOfRelativeDimension.smooth 2 _
       let : LocallyOfFinitePresentation (D.subschemeι ≫ base[k,X]) :=
         TauCeti.locallyOfFinitePresentation_subschemeι_comp_of_isEffectiveCartier hD
       ∃ q : D.subscheme, D.subschemeι q = p ∧
        q ∈ (D.subschemeι ≫ base[k,X]).smoothLocus) ∧
      ∃ e : B.subscheme ≅ D.subscheme, e.hom ≫ D.subschemeι = B.subschemeι ≫ π := by
  let : (I).blowup.Over S(k) := ⟨π ≫ base[k,X]⟩
  let : SmoothOfRelativeDimension 2 (base[k,(I).blowup]) :=
    smoothOfRelativeDimension_blowup_closed_point (base[k,X]) hp
  dsimp only
  intro hnodal hcan
  have : IsReduced B.subscheme := hnodal.isReduced
  let D := B.map π
  obtain ⟨hD, -, hcanD, htotal, hcases⟩ := hB.anticanonical_boundary_point_blowdown k hp hcan
  obtain ⟨hm, -, hstrict⟩ := hcases.resolve_right (fun h ↦ hE h.2.1)
  obtain ⟨q, hq, hqs, hJ⟩ :=
    exists_smoothPoint_and_isEffectiveCartier_comap_of_stalkOrder_eq_one k hp hD hm
  obtain ⟨e, he⟩ := (I).exists_subschemeIso_of_strictTransform_eq hstrict hJ
  have hover : e.hom ≫ (D.subschemeι ≫ base[k,X]) =
      B.subschemeι ≫ π ≫ base[k,X] := by rw [← Category.assoc, he, Category.assoc]
  have hsyn : SyntomicOfRelativeDimension 1 (D.subschemeι ≫ base[k,X]) :=
    (MorphismProperty.cancel_left_of_respectsIso
      (P := @SyntomicOfRelativeDimension 1) e.hom _).mp (hover.symm ▸ hnodal.syntomic)
  have hnodalD := AtWorstNodalOfRelativeDimensionOne.of_comp_surjective
    (f := D.subschemeι ≫ base[k,X]) e.hom (hover.symm ▸ hnodal)
  exact ⟨hD, hcanD, hnodalD, hm, htotal, hstrict, hJ, ⟨q, hq, hqs⟩, e, he⟩

include hp hSmooth in
/-- For a specified contraction exhibiting the source as a point blowup, a nodal
anticanonical boundary omitting the contracted curve descends to its schematic image.
The boundary isomorphism commutes with the specified contraction, and the total
transform acquires exactly one copy of the contracted curve. -/
theorem IsEffectiveCartier.internalBlowdown_of_anticanonical_of_blowupIso
    {Y : Scheme.{u}} [Y.Over S(k)] [SmoothOfRelativeDimension 2 (base[k,Y])]
    {B : Y.IdealSheafData} (hB : B.IsEffectiveCartier) (f : Y ⟶ X) [f.IsOver S(k)]
    (e : (I).blowup ≅ Y) (he : e.hom ≫ f = π)
    (hE : ¬ ((I).comap f).support ≤ B.support)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ base[k,Y]))
    (hcan : LineBundleClass.mk hB.toInvertibleSheaf = K(k,Y)) :
    let D := B.map f
    ∃ hD : D.IsEffectiveCartier,
      LineBundleClass.mk hD.toInvertibleSheaf = K(k,X) ∧
      AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ base[k,X]) ∧
      D.stalkOrder p = 1 ∧ D.comap f = B * (I).comap f ∧
      ((I).comap D.subschemeι).IsEffectiveCartier ∧
      (let : Smooth (base[k,X]) := SmoothOfRelativeDimension.smooth 2 _
       let : LocallyOfFinitePresentation (D.subschemeι ≫ base[k,X]) :=
         TauCeti.locallyOfFinitePresentation_subschemeι_comp_of_isEffectiveCartier hD
       ∃ q : D.subscheme, D.subschemeι q = p ∧
        q ∈ (D.subschemeι ≫ base[k,X]).smoothLocus) ∧
      ∃ d : B.subscheme ≅ D.subscheme, d.hom ≫ D.subschemeι = B.subschemeι ≫ f := by
  let : (I).blowup.Over S(k) := ⟨π ≫ base[k,X]⟩
  let : SmoothOfRelativeDimension 2 (base[k,(I).blowup]) :=
    smoothOfRelativeDimension_blowup_closed_point (base[k,X]) hp
  have hover : e.hom ≫ base[k,Y] = π ≫ base[k,X] := by
    rw [← comp_over f, ← Category.assoc, he]
  have : e.hom.IsOver S(k) := ⟨hover⟩
  let B' := B.comap e.hom
  have hB' : B'.IsEffectiveCartier := hB.comap e.hom
  obtain ⟨a, ha⟩ := B.exists_iso_of_comap_eq_ker e B'.subschemeι B'.ker_subschemeι.symm
  have ha' : a.hom ≫ B.subschemeι ≫ f = B'.subschemeι ≫ π := by
    rw [← Category.assoc, ha, Category.assoc, he]
  have hcan' : LineBundleClass.mk hB'.toInvertibleSheaf = K(k,(I).blowup) := by
    rw [← hB.pullback_mk_toInvertibleSheaf hB', hcan, pullback_mk, mk_pullback_canonicalBundle]
  have hnodal' := hnodal.comp_of_etale a.hom
  rw [← Category.assoc, ha, Category.assoc, hover] at hnodal'
  have hE' : ¬ (E).support ≤ B'.support := by
    intro h
    apply hE
    apply SetLike.coe_subset_coe.mp
    apply e.hom.surjective.preimage_subset_preimage_iff.mp
    have hpre : ((I).comap f).comap e.hom = E := by rw [← comap_comp, he]
    have hh : (((I).comap f).comap e.hom).support ≤ (B.comap e.hom).support := hpre.symm ▸ h
    simpa only [support_comap, Closeds.coe_preimage] using (SetLike.coe_subset_coe.mpr hh)
  obtain ⟨hD, hK, hDnodal, hm, htotal, -, hJ, hs, d, hd⟩ :=
    hB'.internalBlowdown_of_anticanonical k hp hE' hnodal' hcan'
  have hmap : B'.map π = B.map f := by
    rw [map, ← ha', Scheme.Hom.ker_comp_of_isIso, map]
  have hf : e.inv ≫ π = f := by rw [← he, Iso.inv_hom_id_assoc]
  have ht := congrArg (·.comap e.inv) htotal
  simp only [comap_mul, ← comap_comp, hf, B', Iso.inv_hom_id, comap_id] at ht
  have hde : (a.symm ≪≫ d).hom ≫ (B'.map π).subschemeι = B.subschemeι ≫ f := by
    rw [Iso.trans_hom, Category.assoc, hd, ← ha', Iso.symm_hom, Iso.inv_hom_id_assoc]
  rw [← hmap]
  exact ⟨hD, hK, hDnodal, hm, ht, hJ, hs, a.symm ≪≫ d, hde⟩

end AlgebraicGeometry.Scheme.IdealSheafData
