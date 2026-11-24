/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Multiplicity

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.Picard
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Residual
import QPainleve.AlgebraicGeometry.Curves.Degree.Multiplicity
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.ClosedImmersion
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.Stalk
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.AlgebraicGeometry.Scheme.ClosedPoint
import TauCeti.AlgebraicGeometry.Blowup.Pullback
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.Curves.ProjectiveLine
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction

/-!
# Orders after a point blowup

After removing the exact exceptional power from a total-transform ideal, the
order at a closed point of the blowup is bounded by the original order at its
image. On the exceptional line, an element of least order restricts after
division to a nonzero section of degree equal to that order.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti TauCeti.AlgebraicGeometry
open LineBundleClass

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (p : X)

local notation "P" => Scheme.Hom.ker (Scheme.fromSpecResidueField X p)
local notation "π" => blowupToBase P
local notation "E" => comap P π

section AtCenter

variable [IsIntegral X] [IsNoetherian X] [IsRegularLocalRing (X.presheaf.stalk p)]
    (hp : IsClosed ({p} : Set X)) (hdim : ringKrullDim (X.presheaf.stalk p) = 2)

include hp hdim in
private theorem stalkOrder_residual_le_of_cartier {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    {m : ℕ} (hm : D.stalkOrder p = m)
    {y : (P).blowup} (hy : IsClosed ({y} : Set (P).blowup)) (hyE : y ∈ (E).support) :
    ((D.comap π).colon (E ^ m)).stalkOrder y ≤ (m : ℕ∞) := by
  let R := (D.comap π).colon (E ^ m)
  let κ := X.residueField p
  let L := projectiveLine κ
  obtain ⟨e, -, he⟩ := exists_iso_projectiveLine_pullback_exceptionalIdeal_of_closedPoint p hp hdim
  let j : L ⟶ (P).blowup := e.hom ≫ (E).subschemeι
  have : Nonempty (E).subscheme := ⟨e.hom (genericPoint L)⟩
  have : IsIntegral (E).subscheme := isIntegral_of_isOpenImmersion e.inv
  have : IsLocallyNoetherian (P).blowup := LocallyOfFiniteType.isLocallyNoetherian (π)
  have hgen : j (genericPoint L) ∉ R.support := by
    rw [Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion e.hom]
    exact notMem_support_colon_exceptional_of_mem_exceptional p hp hdim D m hm
      ⟨_, (P).isEffectiveCartier_comap_blowupToBase.coheight_subschemeι_genericPoint⟩
      ((E).range_subschemeι.le (Set.mem_range_self _))
  have hm' : (m : ℕ∞) ≤ D.stalkOrder p := hm.ge
  let hR := hD.comap_blowupToBase_colon_exceptional_pow p hp hdim m hm'
  let hC := hR.comap_of_isIntegral j hgen
  obtain ⟨z, rfl⟩ := (E).range_subschemeι.ge hyE
  let q := e.inv z
  have hq : j q = (E).subschemeι z := by simp [j, q]
  have hqClosed : IsClosed ({q} : Set L) := by
    rw [← j.injective.preimage_image {q}, Set.image_singleton, hq]
    exact hy.preimage j.continuous
  have : AlgebraicGeometry.IsRegular L := ⟨fun _ ↦ inferInstance⟩
  have hpoint := L.isEffectiveCartier_ker_fromSpecResidueField_of_dim_eq_one hqClosed
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one κ)
  have := L.moduleFinite_residueField_of_isClosed (k := κ) hqClosed
  have hκ : (1 : ℤ) ≤ ((L ↘ Spec (.of κ)).residueDegree q : ℤ) := by
    rw [Scheme.Hom.residueDegree_eq_finrank, ← Scheme.residueFieldBaseAlgebra_eq_compHom]
    exact_mod_cast Nat.succ_le_of_lt (Module.finrank_pos : 0 < Module.finrank κ (L.residueField q))
  have hdeg : eulerDegree κ (LineBundleClass.mk hC.toInvertibleSheaf)⁻¹ = m := by
    have hEdeg := (projectiveLine.nonempty_iso_twistingSheaf_iff κ _ 1).mp he.1
    have hbase : ((P).support : Set X) = {p} :=
      Scheme.support_ker_fromSpecResidueField_of_isClosed hp
    have htriv (a : LineBundleClass X) : pullback (j ≫ π) a = 1 := by
      dsimp only [j]
      rw [Category.assoc, ← pullback_comp,
        (P).pullback_exceptionalSubschemeι_comp_blowupToBase hbase, pullback_one]
    rw [← hR.pullback_mk_toInvertibleSheaf hC, ← pullback_inv,
      hD.toLineBundleClass_comap_blowupToBase_colon_exceptional_pow p hp hdim m hm',
      pullback_mul, pullback_comp, htriv, one_mul, pullback_pow, ← zpow_natCast,
      eulerDegree_zpow_of_isCurveOver, pullback_mk, eulerDegree_mk, hEdeg, mul_one]
  refine ENat.forall_natCast_le_iff_le.mp fun n hn ↦ ENat.natCast_le_natCast.mpr ?_
  have hqOrder := (R.stalkOrder_le_comap j q)
  rw [hq] at hqOrder
  have hbound := hC.mul_residueDegree_le_eulerDegree_of_le_stalkOrder (k := κ) hqClosed
    hpoint (hn.trans hqOrder)
  rw [hdeg] at hbound
  have hmul := mul_le_mul_of_nonneg_left hκ (Int.natCast_nonneg n)
  rw [mul_one] at hmul
  exact_mod_cast hmul.trans hbound

include hp hdim in
private theorem stalkOrder_residual_le_of_isAffine [IsAffine X] (J : X.IdealSheafData)
    {m : ℕ} (hm : J.stalkOrder p = m) {I : X.IdealSheafData} (hI : I = P)
    {y : I.blowup} (hy : IsClosed ({y} : Set I.blowup))
    (hyE : y ∈ (I.comap I.blowupToBase).support) :
    ((J.comap I.blowupToBase).colon ((I.comap I.blowupToBase) ^ m)).stalkOrder y ≤ (m : ℕ∞) := by
  subst I
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have hm' : (m : ℕ∞) ≤ J.stalkOrder p := hm.ge
  have hn' : ¬ J.ideal U ≤ ((P).ideal U) ^ (m + 1) := by
    rw [← natCast_le_stalkOrder_iff_ideal_le_pow p J hp U (Opens.mem_top p), hm,
      ENat.natCast_le_natCast]
    omega
  -- A section of least order cuts out a Cartier subideal with the same order.
  obtain ⟨s, hs, hs'⟩ := IsConcreteLE.not_le_iff_exists.mp hn'
  let D : X.IdealSheafData := ofIdealTop (Ideal.span {s})
  have hDle : D ≤ J := le_of_isAffine (by
    simpa only [D, ofIdealTop_ideal, homOfLE_refl, op_id, X.presheaf.map_id, CommRingCat.hom_id,
      Ideal.map_id] using (J.ideal U).span_singleton_le_iff_mem.mpr hs)
  have hD : D.IsEffectiveCartier := isEffectiveCartier_ofIdealTop_span_singleton _ fun V ↦
    U.property.isSMulRegular_map le_top
      (IsSMulRegular.of_ne_zero fun he ↦ hs' (he ▸ zero_mem _))
  have hDm : D.stalkOrder p = m := by
    refine le_antisymm (ENat.forall_natCast_le_iff_le.mp fun n hn ↦ ?_)
      (hm'.trans (stalkOrder_anti hDle p))
    rw [ENat.natCast_le_natCast]
    by_contra! h
    have hstep := ENat.natCast_le_natCast.mpr (Nat.succ_le_of_lt h)
    exact hs' ((natCast_le_stalkOrder_iff_ideal_le_pow p D hp U
      (Opens.mem_top p) (m + 1)).mp (hstep.trans hn) (by simp [D, U]))
  exact (stalkOrder_anti (colon_mono (comap_mono _ hDle) le_rfl) y).trans
    (stalkOrder_residual_le_of_cartier p hp hdim hD hDm hy hyE)

end AtCenter

private theorem stalkOrder_residual_le_on_affineOpen [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularLocalRing (X.presheaf.stalk p)] (hp : IsClosed ({p} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (J : X.IdealSheafData)
    (U : X.affineOpens) (hpU : p ∈ U.val) {m : ℕ} (hm : J.stalkOrder p = m)
    (z : ((P).comap U.val.ι).blowup)
    (hz : IsClosed ({(P).blowupMap U.val.ι z} : Set (P).blowup))
    (hzE : π ((P).blowupMap U.val.ι z) = p) :
    ((J.comap π).colon (E ^ m)).stalkOrder ((P).blowupMap U.val.ι z) ≤ (m : ℕ∞) := by
  let u := U.val.ι
  let q : U.val.toScheme := ⟨p, hpU⟩
  let P' := (P).comap u
  let v := (P).blowupMap u
  have hqClosed : IsClosed ({q} : Set U.val.toScheme) := by
    rw [← u.injective.preimage_image {q}, Set.image_singleton]
    exact hp.preimage u.continuous
  have hzClosed : IsClosed ({z} : Set P'.blowup) := by
    rw [← v.injective.preimage_image {z}, Set.image_singleton]
    exact hz.preimage v.continuous
  have hqIso : u q ∈ u.isoLocus := u.le_isoLocus_iff.mpr
    (u.isIso_morphismRestrict_of_le_opensRange U.val.opensRange_ι.ge) hpU
  have hP : P' = (U.val.toScheme.fromSpecResidueField q).ker :=
    u.comap_ker_fromSpecResidueField_of_mem_isoLocus (q := q) hp hqIso
  have hC : (E).comap v = P'.comap P'.blowupToBase := (P).comap_comap_blowupMap u
  have hJ : (J.comap π).comap v = (J.comap u).comap P'.blowupToBase := by
    rw [← comap_comp, blowupMap_blowupToBase, comap_comp]
  have hz' : z ∈ (P'.comap P'.blowupToBase).support := by
    have hpS : π (v z) ∈ (P).support := by
      simpa only [← SetLike.mem_coe, Scheme.support_ker_fromSpecResidueField_of_isClosed hp,
        Set.mem_singleton_iff] using hzE
    have hvS : v z ∈ (E).support := by
      rw [support_comap]
      exact hpS
    rw [← hC, support_comap]
    exact hvS
  have hEs := isEffectiveCartier_pow (P).isEffectiveCartier_comap_blowupToBase m
  have hle := (comap_blowupToBase_le_exceptional_pow_iff p hp hdim J m).mpr hm.ge
  have hv : ((E ^ m).comap v).IsEffectiveCartier := by
    rw [comap_pow, hC]
    exact isEffectiveCartier_pow P'.isEffectiveCartier_comap_blowupToBase m
  rw [← stalkOrder_comap_of_isIso_stalkMap _ v z,
    comap_colon (J.comap π) (E ^ m) hEs.locallyPrincipal hle v hv, hJ, comap_pow, hC]
  have : Nonempty U.val.toScheme := ⟨q⟩
  have : IsIntegral U.val.toScheme := isIntegral_of_isOpenImmersion u
  have : IsLocallyNoetherian U.val.toScheme := isLocallyNoetherian_of_isOpenImmersion u
  have : IsAffine U.val.toScheme := U.property
  have : IsNoetherian U.val.toScheme := ⟨⟩
  have : IsRegularLocalRing (U.val.toScheme.presheaf.stalk q) :=
    (isRegularLocalRing_stalk_iff_of_isOpenImmersion u q).mp
      (inferInstance : IsRegularLocalRing (X.presheaf.stalk p))
  have hdim' : ringKrullDim (U.val.toScheme.presheaf.stalk q) = 2 :=
    (asIso (u.stalkMap q)).commRingCatIsoToRingEquiv.ringKrullDim.symm.trans hdim
  exact stalkOrder_residual_le_of_isAffine q hqClosed hdim' (J.comap u)
    ((J.stalkOrder_comap_of_isIso_stalkMap u q).trans hm) hP hzClosed hz'

/-- After removing the exact exceptional power from the pullback of an ideal, the
order at any closed point above the center is bounded by the order at the center. -/
theorem stalkOrder_colon_exceptional_pow_le [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularLocalRing (X.presheaf.stalk p)] (hp : IsClosed ({p} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (J : X.IdealSheafData)
    {y : (P).blowup} (hy : IsClosed ({y} : Set (P).blowup)) (hyE : π y = p) :
    ((J.comap π).colon (E ^ (J.stalkOrder p).toNat)).stalkOrder y ≤ J.stalkOrder p := by
  by_cases htop : J.stalkOrder p = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top p)
  let v := (P).blowupMap U.ι
  have hyRange : y ∈ Set.range v := by
    rw [← Scheme.Hom.coe_opensRange, (P).opensRange_blowupMap U.ι,
      Scheme.Opens.opensRange_ι, Scheme.Hom.coe_preimage, Set.mem_preimage, hyE]
    exact hpU
  obtain ⟨z, rfl⟩ := hyRange
  exact (stalkOrder_residual_le_on_affineOpen p hp hdim J ⟨U, hU⟩ hpU
    ((ENat.natCast_toNat htop).symm) z hy hyE).trans (ENat.natCast_toNat_le_self _)

/-- Away from the exceptional divisor, removing the exceptional power leaves the
stalk order equal to the order at the corresponding point on the base. -/
theorem stalkOrder_colon_exceptional_pow_eq_of_ne (hp : IsClosed ({p} : Set X))
    (J : X.IdealSheafData) {y : (P).blowup} (hy : π y ≠ p) :
    ((J.comap π).colon (E ^ (J.stalkOrder p).toNat)).stalkOrder y =
      J.stalkOrder (π y) := by
  have hbase : π y ∈ (P).support.compl := by
    simpa only [← SetLike.mem_coe, Closeds.coe_compl,
      Scheme.support_ker_fromSpecResidueField_of_isClosed hp, Set.mem_compl_iff,
      Set.mem_singleton_iff] using hy
  have hloc : π y ∈ (π).isoLocus :=
    (π).le_isoLocus_iff.mpr (P).isIso_blowupToBase_restrict_compl_support hbase
  have := (π).isIso_stalkMap_of_mem_isoLocus hloc
  have hEtop : (E).stalkIdeal y = ⊤ := by
    apply not_ne_iff.mp
    intro h
    exact hbase (by
      simpa only [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage]
        using ((E).mem_support_iff_stalkIdeal_ne_top y).mpr h)
  have hfactor := congrArg (fun I : (P).blowup.IdealSheafData ↦ I.stalkIdeal y)
    (comap_blowupToBase_eq_colon_mul_exceptional_pow p hp J)
  simp only [stalkIdeal_mul, stalkIdeal_pow, hEtop, Ideal.top_pow, Ideal.mul_top] at hfactor
  rw [stalkOrder_def, ← hfactor, ← stalkOrder_def]
  exact J.stalkOrder_comap_of_isIso_stalkMap (π) y

end AlgebraicGeometry.Scheme.IdealSheafData
