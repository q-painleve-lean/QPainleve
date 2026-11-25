/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Incidence
public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Subdivision.StrictTransform

import QPainleve.AlgebraicGeometry.Blowup.Tower.Multiplicity
import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.BaseMultiplicity
import QPainleve.Geometry.Toric.Fan.Smooth
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback

/-!
# The section centers of a toric Hirzebruch link

When the pivot is a corner on the chosen section, the reverse corner is off
that section. The incidence of every remaining center with the successive
strict transforms of the section follows its exceptional coordinate, including
at infinitely near points. The Picard coordinate change comes from the
elementary transformation in [Lutz, Lemma 8.9][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=71
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry TauCeti.Toric LineBundleClass
open Scheme.IdealSheafData.IsEffectiveCartier (toInvertibleSheaf)

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ Ω : Fan i} [Nonempty Φ.cones] [Nonempty Ψ.cones]

local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "π[" s "]" => FanHom.algebraicMap (Fan.IsSubdivision.toFanHom s)
local notation "f[" Δ "]" => Fan.algebraicRealizationStructureMap Δ
local notation "D[" h "," r "]" => Fan.rayBoundaryIdeal _ h (r 0)
local notation "H[" b "," a "," h "," r "," hr "]" =>
  Fan.hirzebruchPicardBasis b a h r hr

variable {Y Z : Scheme} {n : ℕ} {T : BlowupTower X[Φ] (n + 1) Y}
  {U : BlowupTower X[Ψ] (1 + n) Z}
  (hT : IsClosedPointTower X[Φ] T) (hU : IsClosedPointTower X[Ψ] U)
  (b d : Basis (Fin 2) ℤ N) (a : ℤ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
  (r : Fin 4 ≃ Φ.Ray) (r' : Fin 4 ≃ Ψ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, a • b 0 - b 1])
  (hr' : (fun j ↦ (r' j).primitiveGenerator) = ![d 0, d 1, -d 0, (a + 1) • d 0 - d 1])

local notation "C" => H[b,a,hΦ,r,hr]
local notation "C'" => H[d,a + 1,hΨ,r',hr']
local notation "classOf(" h ")" => Additive.ofMul (LineBundleClass.mk (toInvertibleSheaf h))⁻¹

private theorem strictTransformCoefficients_section_of_corner
    (σ : Φ.cones) (hσ : (r 0).toCone ≤ σ) (j : Fin (n + 1))
    (hj : hT.baseCenter j = Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (hfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
    [SmoothOfRelativeDimension 2 f[Φ]] [IsNoetherian X[Φ]] :
    hT.strictTransformCoefficients (D[hΦ,r]) j = -1 := by
  rw [hT.strictTransformCoefficients_eq_neg_baseMultiplicities f[Φ]
    (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ (r 0)),
    hT.baseMultiplicities_eq_stalkOrder_toNat_of_first (D[hΦ,r]) j hfirst, hj,
    Φ.stalkOrder_rayBoundaryIdeal_distinguishedPoint hΦ, ite_eq_left hσ]
  rfl

variable
    (hΩ : Ω.IsRegular) (s : Ω.IsSubdivision Φ) (t : Ω.IsSubdivision Ψ)
    (g : Y ⟶ X[Ω]) [Surjective g] (e : Y ≅ Z)
    (hg : g ≫ π[s] = T.toBase) (hg' : g ≫ π[t] = e.hom ≫ U.toBase)
    (hd : d 0 = b 0) (σ : Φ.cones) (hσ : (r 0).toCone ≤ σ) (j : Fin (n + 1))
    (hj : hT.baseCenter j = Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (hfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
    (hmark : ∀ x : Fin (n + 1) → ℤ,
      let source := Fan.hirzebruchPicardBasis b a hΦ r hr
      let target := Fan.hirzebruchPicardBasis d (a + 1) hΨ r' hr'
      pullback e.hom (U.picardHom ((1 + x j) • target 0 + target 1,
        Fin.append (fun _ : Fin 1 ↦ -1 - x j) (x ∘ j.succAbove))).toMul =
        (T.picardHom (source 1, x)).toMul)

include hr hr' hΩ hg hg' hd hσ hj hfirst hmark in
/-- The exceptional coefficients of the strict section after a resolved toric
corner link are obtained by removing the pivot coefficient and inserting zero
at the reverse corner. The Picard comparison is the section case of the
coordinate formula in `exists_sarkisov_decrease_of_toric_corner`. The formula
applies to every retained center, in its original relative order. -/
theorem strictTransformCoefficients_toric_corner :
    hU.strictTransformCoefficients (D[hΨ,r']) =
      Fin.append (0 : Fin 1 → ℤ) (hT.strictTransformCoefficients (D[hΦ,r]) ∘ j.succAbove) := by
  have hN : finrank ℤ N = 2 := (finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let : SmoothOfRelativeDimension 2 f[Φ] := hN ▸
    Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : SmoothOfRelativeDimension 2 f[Ψ] := hN ▸
    Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
  let : Smooth f[Φ] := SmoothOfRelativeDimension.smooth 2 f[Φ]
  let : Smooth f[Ψ] := SmoothOfRelativeDimension.smooth 2 f[Ψ]
  let : IsNoetherian X[Φ] := isNoetherian_of_finiteType f[Φ]
  let : IsNoetherian X[Ψ] := isNoetherian_of_finiteType f[Ψ]
  let x := hT.strictTransformCoefficients (D[hΦ,r])
  have hx : x j = -1 := strictTransformCoefficients_section_of_corner hT hΦ r σ hσ j hj hfirst
  have hgen : (r 0).primitiveGenerator = (r' 0).primitiveGenerator :=
    (congrFun hr 0).trans (hd.symm.trans (congrFun hr' 0).symm)
  have hstrict := s.comap_strictTransform_rayBoundaryIdeal t hΦ hΨ hΩ hN hT hU g e hg hg'
    (r 0) (r' 0) hgen
  let hD := Φ.isEffectiveCartier_rayBoundaryIdeal hΦ (r 0)
  let hD' := Ψ.isEffectiveCartier_rayBoundaryIdeal hΨ (r' 0)
  have hsrc : C 1 = classOf(hD) := by
    simp only [Fan.hirzebruchPicardBasis_apply_one, Fan.rayDivisorToPicard_single, one_smul,
      primeDivisorClass_def, ← Φ.rayBoundaryIdeal_def hΦ]
  have htgt : C' 1 = classOf(hD') := by
    simp only [Fan.hirzebruchPicardBasis_apply_one, Fan.rayDivisorToPicard_single, one_smul,
      primeDivisorClass_def, ← Ψ.rayBoundaryIdeal_def hΨ]
  have hclass := hmark x
  dsimp only at hclass
  rw [hx, add_neg_cancel, zero_smul, zero_add, sub_self, hsrc, htgt] at hclass
  have hY := hT.isEffectiveCartier_strictTransform f[Φ] hD
  have hZ := hU.isEffectiveCartier_strictTransform f[Ψ] hD'
  have hpb : pullback e.hom (classOf(hZ)).toMul = (classOf(hY)).toMul := by
    rw [toMul_ofMul, toMul_ofMul, pullback_inv, hZ.pullback_mk_toInvertibleSheaf (hZ.comap e.hom),
      mk_toInvertibleSheaf_congr _ _ hstrict]
  have hTclass := hT.picardMarking_strictTransform f[Φ] hD
  have hUclass := hU.picardMarking_strictTransform f[Ψ] hD'
  rw [T.picardMarking_apply hT f[Φ]] at hTclass
  rw [U.picardMarking_apply hU f[Ψ]] at hUclass
  rw [hTclass, ← hpb, ← hUclass] at hclass
  rw [← pullbackEquiv_apply e, ← pullbackEquiv_apply e] at hclass
  have heq := (hU.bijective_picardHom f[Ψ]).injective
    (Additive.toMul.injective ((pullbackEquiv e).injective hclass))
  exact (congrArg Prod.snd heq).symm

include hr hr' hΩ hg hg' hd hσ hj hfirst hmark in
/-- The section-center indices after a resolved toric corner link consist of
the original section-center indices other than the selected pivot, reindexed
in their retained order after the reverse corner. -/
theorem strictTransformCenterIndices_toric_corner :
    hU.strictTransformCenterIndices (D[hΨ,r']) =
      (Finset.univ.filter fun l : Fin n ↦
        j.succAbove l ∈ hT.strictTransformCenterIndices (D[hΦ,r])).map (Fin.natAddEmb 1) := by
  exact hT.strictTransformCenterIndices_eq_map_of_coefficients_eq_append_zero hU j.succAbove
    (hT.strictTransformCoefficients_toric_corner hU b d a hΦ hΨ r r' hr hr'
      hΩ s t g e hg hg' hd σ hσ j hj hfirst hmark)

end QPainleve.BlowupTower.IsClosedPointTower
