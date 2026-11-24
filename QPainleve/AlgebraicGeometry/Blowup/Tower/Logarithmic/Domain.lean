/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Divisor
public import QPainleve.AlgebraicGeometry.RationalMap.Restriction

import QPainleve.AlgebraicGeometry.Blowup.Tower.Contraction
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Regularity off the boundary for a logarithmic birational map

The equality of pulled-back logarithmic divisors on a common point-blowup
resolution forces the target projection to contract every source exceptional
fiber over the complement of the source boundary. Thus the specified rational
map is defined off that boundary. This works even when the common resolution
has extra blowups and the two pulled-back forms acquire zeros.

This is the boundary restriction used to select centers in Proposition 8.11 of
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=70
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [PerfectField k] {X Z V W : Scheme.{u}}
  [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k))]
  [IsIntegral X] [IsIntegral Z] [QuasiCompact (Z ↘ Spec (.of k))]
  {m n : ℕ} {T : BlowupTower X m V} {U : BlowupTower Z n W}
  (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Z U) (e : V ≅ W)

local notation "sX" => (X ↘ Spec (CommRingCat.of k))
local notation "sZ" => (Z ↘ Spec (CommRingCat.of k))
local notation "π" => T.toBase
local notation "g" => (e.hom ≫ U.toBase)
local notation "RT" => hT.ramificationIdealSheafToBase k
local notation "RU" => comap (hU.ramificationIdealSheafToBase k) (Iso.hom e)

/-- If the two Jacobian-corrected total transforms agree, the target projection
descends uniquely over the complement of the source poles. The hypothesis is
the product identity obtained by clearing the two ramification terms from the
equality of logarithmic pullback divisors. -/
theorem existsUnique_comp_eq_compl_support_of_common_log_divisor
    (D : X.IdealSheafData) (B : Z.IdealSheafData)
    (h : D.comap π * RU = B.comap g * RT) :
    ∃! a : Scheme.Opens.toScheme (D.support.compl : X.Opens) ⟶ Z,
      (π ∣_ D.support.compl) ≫ a = (π ⁻¹ᵁ D.support.compl).ι ≫ g := by
  have : IsModification U.toBase := hU.isModification_of_smoothOfRelativeDimension_two sZ
  have : IsModification e.hom := IsModification.of_isIso _
  have : IsModification g := inferInstance
  have : Smooth sZ := SmoothOfRelativeDimension.smooth 2 sZ
  have : IsNoetherian Z := isNoetherian_of_finiteType sZ
  have : IsRegular Z := IsRegular.of_smooth sZ
  have : Smooth (U.toBase ≫ sZ) := (hU.smoothOfRelativeDimension sZ).smooth
  have : IsRegular W := IsRegular.of_smooth (U.toBase ≫ sZ)
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension sZ (n := 2)
  have hg : (g).centre = U.toBase.centre := by
    rw [Scheme.Hom.centre_comp, (e.hom.centre_eq_empty_iff.mpr inferInstance),
      Set.image_empty, Set.union_empty]
  have hs₀ := hT.support_ramificationIdealSheafToBase k
  have hs₁ : e.hom ⁻¹' ((hU.ramificationIdealSheafToBase k).support : Set W) =
      g ⁻¹' (g).centre := by
    rw [hU.support_ramificationIdealSheafToBase k, hg, Set.preimage_preimage]
    rfl
  have hs := congrArg (fun I : V.IdealSheafData ↦ (I.support : Set V)) h
  simp only [support_mul, Closeds.coe_sup, support_comap, Closeds.coe_preimage, hs₀, hs₁] at hs
  apply hT.existsUnique_comp_eq_morphismRestrict_of_preimage_centre_subset sX g hdim.le
  intro x hx hxc
  have hm : x ∈ π ⁻¹' (D.support : Set X) ∪ g ⁻¹' (g).centre := by
    rw [hs]
    exact Or.inr hxc
  have hx' : x ∉ π ⁻¹' (D.support : Set X) := by
    simpa only [Set.mem_preimage, ← SetLike.mem_coe, Closeds.coe_compl,
      Set.mem_compl_iff] using hx
  exact hm.resolve_left hx'

/-- A specified rational map on smooth surfaces that satisfies the common
logarithmic divisor identity on a point-blowup resolution is regular off the
source boundary. -/
theorem compl_support_le_domain_of_common_log_divisor
    (D : X.IdealSheafData) (B : Z.IdealSheafData)
    (h : D.comap π * RU = B.comap g * RT) (q : X ⤏ Z)
    (hq : letI := hT.isModification_of_smoothOfRelativeDimension_two sX
          letI := (IsModification.birational π).irreducibleSpace
          (g).toRationalMap = (π).toRationalMap.comp q) :
    D.support.compl ≤ q.domain := by
  have := hT.isModification_of_smoothOfRelativeDimension_two sX
  have := (IsModification.birational π).irreducibleSpace
  have := hT.smoothOfRelativeDimension sX
  have : Smooth (π ≫ sX) := SmoothOfRelativeDimension.smooth 2 _
  have : IsRegular V := IsRegular.of_smooth (π ≫ sX)
  have : IsIntegral V := isIntegral_of_irreducibleSpace_of_isReduced V
  obtain ⟨a, ha, _⟩ :=
    hT.existsUnique_comp_eq_compl_support_of_common_log_divisor (k := k) hU e D B h
  exact q.le_domain_of_morphismRestrict_comp_eq π g hq a ha

variable [V.Over (Spec (.of k))] [IsIntegral V] [SmoothOfRelativeDimension 2 (V ↘ Spec (.of k))]
  [T.toBase.IsOver (Spec (.of k))] [(e.hom ≫ U.toBase).IsOver (Spec (.of k))]

include hU in
/-- Equality of the actual divisors of the pulled-back logarithmic top forms on
the specified resolution implies regularity off the source poles, even if the
common divisor has a positive part. -/
theorem compl_support_le_domain_of_pullbackTopFormDivisor_eq
    {D : X.IdealSheafData} {B : Z.IdealSheafData}
    (hD : D.IsEffectiveCartier) (hB : B.IsEffectiveCartier)
    (ω : hD.toInvertibleSheaf ≅ canonicalBundle k X 2)
    (η : hB.toInvertibleSheaf ≅ canonicalBundle k Z 2)
    (hD' : (D.comap π).IsEffectiveCartier) (hB' : (B.comap g).IsEffectiveCartier)
    (q : X ⤏ Z)
    (hq : letI := hT.isModification_of_smoothOfRelativeDimension_two sX
          (g).toRationalMap = (π).toRationalMap.comp q) :
    letI := SmoothOfRelativeDimension.smooth 2 (V ↘ Spec (.of k))
    ∀ (hRamT : (ramificationIdealSheaf k π).IsEffectiveCartier)
      (hRamU : (ramificationIdealSheaf k g).IsEffectiveCartier),
      pullbackTopFormDivisor k π 2 hD ω hD' hRamT =
        pullbackTopFormDivisor k g 2 hB η hB' hRamU → D.support.compl ≤ q.domain := by
  let : Smooth (V ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  intro hRamT hRamU hlog
  have hT' : RT = ramificationIdealSheaf k π := by
    simpa only [Iso.refl_hom, comap_id] using
      hT.comap_ramificationIdealSheafToBase k (Iso.refl V) (Category.id_comp π)
  have hU' : RU = ramificationIdealSheaf k g :=
    hU.comap_ramificationIdealSheafToBase k e rfl
  refine hT.compl_support_le_domain_of_common_log_divisor (k := k) hU e D B ?_ q hq
  rw [hT', hU']
  apply ((TauCeti.isEffectiveCartier_mul hD' hRamU).toCartierDivisor_eq_iff
    (TauCeti.isEffectiveCartier_mul hB' hRamT)).mp
  rw [IsEffectiveCartier.toCartierDivisor_mul hD' hRamU,
    IsEffectiveCartier.toCartierDivisor_mul hB' hRamT]
  rw [pullbackTopFormDivisor_eq_ramification_sub, pullbackTopFormDivisor_eq_ramification_sub,
    sub_eq_sub_iff_add_eq_add] at hlog
  calc
    _ = hRamU.toCartierDivisor + hD'.toCartierDivisor := add_comm _ _
    _ = hRamT.toCartierDivisor + hB'.toCartierDivisor := hlog.symm
    _ = _ := add_comm _ _

end QPainleve.BlowupTower.IsClosedPointTower
