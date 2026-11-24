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
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Contracting an internal exceptional curve on an anticanonical pair

When an anticanonical divisor on a point blowup omits the exceptional component,
the downstairs divisor has order one at the center. Its boundary is therefore
isomorphic to the original boundary, and the center is a smooth boundary point
when the original divisor is nodal.

This is the internal blowdown in the construction of the toric models in
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
proof of Theorem 1.8](https://arxiv.org/html/1211.6367v5#S2).
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

include hp hSmooth in
omit [PerfectField k] in
private theorem exists_strictTransform_eq {B : (I).blowup.IdealSheafData}
    (hB : B.IsEffectiveCartier) [IsReduced B.subscheme]
    (hE : ¬ (E).support ≤ B.support) :
    ∃ D : X.IdealSheafData, D.IsEffectiveCartier ∧ strict(D) = B := by
  have : Smooth (base[k,X]) := SmoothOfRelativeDimension.smooth 2 _
  have := (base[k,X]).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have : IsNoetherian (I).blowup := isNoetherian_of_finiteType π
  let U : X.Opens := (I).support.compl
  let V := π ⁻¹ᵁ U
  have hIso : IsIso ((π) ∣_ U) := (I).isIso_blowupToBase_restrict_compl_support
  have : IsOpenImmersion (V.ι ≫ π) := by
    rw [← morphismRestrict_ι]
    infer_instance
  obtain ⟨D, hD, hD'⟩ := (hB.comap V.ι).exists_comap_eq_of_isOpenImmersion (V.ι ≫ π)
  rw [comap_comp] at hD'
  refine ⟨D, hD, ?_⟩
  rw [ker_blowupMap_subschemeι_eq_map_comap, compl_support_comap, hD']
  apply hB.map_comap_eq_of_codimensionOne_mem_range V.ι
  intro q hq
  rw [Scheme.Opens.range_ι]
  dsimp only [V, U]
  rw [← compl_support_comap]
  intro hqE
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (base[k,X]) 2).mp
    inferInstance).2 p hp
  have := isRegularLocalRing_stalk_of_smooth (base[k,X]) p
  have : IsIntegral (E).subscheme := isIntegral_exceptional_blowup_closed_point hdim hp
  have hq' :=
    ((I).isEffectiveCartier_comap_blowupToBase.mem_support_iff_eq_subschemeι_genericPoint
      q.property).mp hqE
  apply hE
  apply SetLike.coe_subset_coe.mp
  rw [(E).support_eq_closure_subschemeι_genericPoint, ← hq']
  exact B.support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hq)

include hp in
private theorem stalkOrder_and_canonical_of_strictTransform
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier) :
    let : (I).blowup.Over S(k) := ⟨π ≫ base[k,X]⟩
    letI : SmoothOfRelativeDimension 2 ((I).blowup ↘ S(k)) :=
      smoothOfRelativeDimension_blowup_closed_point (base[k,X]) hp
    ∀ hB : strict(D).IsEffectiveCartier,
      LineBundleClass.mk hB.toInvertibleSheaf = K(k,(I).blowup) →
      D.stalkOrder p = 1 ∧ LineBundleClass.mk hD.toInvertibleSheaf = K(k,X) := by
  let : (I).blowup.Over S(k) := ⟨π ≫ base[k,X]⟩
  let : SmoothOfRelativeDimension 2 (base[k,(I).blowup]) :=
    smoothOfRelativeDimension_blowup_closed_point (base[k,X]) hp
  dsimp only
  intro hB hcan
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
  have hclass := congrArg Inv.inv (hD.toLineBundleClass_strictTransform_pointBlowup hp hdim)
  simp only [inv_inv, mul_inv_rev, ← pullback_inv, ← zpow_natCast, inv_zpow] at hclass
  have heq : e (Additive.ofMul (LineBundleClass.mk hD.toInvertibleSheaf), (m : ℤ)) =
      e (Additive.ofMul K(k,X), (1 : ℤ)) := by
    apply Additive.toMul.injective
    simp only [e, picardBlowupEquiv_apply_toMul, toMul_ofMul, zpow_one,
      ← blowupExceptionalClass_def]
    have hK : K(k,(I).blowup) =
        pullback π K(k,X) * (I).blowupExceptionalClass := mk_canonicalBundle_pointBlowup k hp
    rw [← hK, ← hcan]
    exact (mul_comm _ _).trans hclass.symm
  have hpairs := e.injective heq
  have hm' : (m : ℤ) = 1 := congrArg Prod.snd hpairs
  have hm : (D.stalkOrder p).toNat = 1 := by exact_mod_cast hm'
  have hfinite : D.stalkOrder p ≠ ⊤ := by
    rw [stalkOrder_def, ne_eq, Ideal.localOrder_eq_top_iff_eq_bot]
    exact hD.stalkIdeal_ne_bot p
  refine ⟨?_, Additive.ofMul.injective (congrArg Prod.fst hpairs)⟩
  rw [← ENat.natCast_toNat hfinite, hm, Nat.cast_one]

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
  obtain ⟨D, hD, hstrict⟩ := exists_strictTransform_eq k hp hB hE
  have hB' : strict(D).IsEffectiveCartier := hstrict.symm ▸ hB
  have hcan' : LineBundleClass.mk hB'.toInvertibleSheaf = K(k,(I).blowup) :=
    (LineBundleClass.mk_toInvertibleSheaf_congr hB' hB hstrict).trans hcan
  obtain ⟨hm, hcanD⟩ := stalkOrder_and_canonical_of_strictTransform k hp hD hB' hcan'
  obtain ⟨q, hq, hqs, hJ⟩ :=
    exists_smoothPoint_and_isEffectiveCartier_comap_of_stalkOrder_eq_one k hp hD hm
  obtain ⟨e, he⟩ := (I).exists_subschemeIso_of_strictTransform_eq hstrict hJ
  have hmap : D = B.map π := by
    rw [← B.ker_subschemeι, map_ker, ← he, Scheme.Hom.ker_comp_of_isIso, D.ker_subschemeι]
  have hover : e.hom ≫ (D.subschemeι ≫ base[k,X]) =
      B.subschemeι ≫ π ≫ base[k,X] := by rw [← Category.assoc, he, Category.assoc]
  have hsyn : SyntomicOfRelativeDimension 1 (D.subschemeι ≫ base[k,X]) :=
    (MorphismProperty.cancel_left_of_respectsIso
      (P := @SyntomicOfRelativeDimension 1) e.hom _).mp (hover.symm ▸ hnodal.syntomic)
  have hnodalD := AtWorstNodalOfRelativeDimensionOne.of_comp_surjective
    (f := D.subschemeι ≫ base[k,X]) e.hom (hover.symm ▸ hnodal)
  have : Smooth (base[k,X]) := SmoothOfRelativeDimension.smooth 2 _
  have := isRegularLocalRing_stalk_of_smooth (base[k,X]) p
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (base[k,X]) 2).mp
    inferInstance).2 p hp
  have htotal : D.comap π = strict(D) * E := by
    simpa only [hm, ENat.toNat_one, pow_one] using
      hD.totalTransform_eq_strictTransform_mul_pow_closedPoint hp hdim
  rw [hstrict] at htotal
  rw [← hmap]
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
