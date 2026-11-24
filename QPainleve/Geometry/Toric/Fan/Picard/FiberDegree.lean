/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Ruling.Basic
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch
public import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import QPainleve.Geometry.Toric.Fan.Picard.Ruling
import QPainleve.Geometry.Toric.Fan.Ruling.Subdivision
import TauCeti.AlgebraicGeometry.RationalPoint.IdealSheaf

/-!
# Fiber degree on Hirzebruch resolutions

The fiber degree read from the Picard marking of a resolution is the intersection
with the pullback of a point under the resolved ruling. Two Hirzebruch models with
a common resolved ruling therefore give the same fiber degree, even when their
closed-point towers have different exceptional coordinates. This is the numerical
comparison used in the preparation of a Hirzebruch surface for the quadric case in
[Lutz's appendix to Hacking and Keating][HKL], Proposition 8.11, Case C.

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.Toric

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "H" => Additive.toMul (AddEquiv.symm (projectiveLine.picardDegreeEquiv ℂ) 1)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "m" => LinearMap.toAddMonoidHom (b.coord 1)

/-- The first Hirzebruch Picard basis vector is the pullback of `𝒪(1)`
under the ruling defined by the second basis character. -/
theorem hirzebruchPicardBasis_zero_eq_pullback_characterRuling :
    (Φ.hirzebruchPicardBasis b e hΦ r hr 0).toMul =
      pullback (Φ.characterRuling m (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)) H := by
  classical
  let h := nonneg_or_nonpos_hirzebruch_ruling_character b e r hr
  let p := projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 0
  have hp : p ≫ (projectiveLine ℂ ↘ S) = 𝟙 S := by
    simp [p, projectiveLine.polynomialPoint_over]
  have hm : m ≠ 0 := by
    intro hz
    have ha := DFunLike.congr_fun hz (b 1)
    simp [Basis.coord_apply] at ha
  have hcoeff : (fun ρ : Φ.Ray ↦ max (m ρ.primitiveGenerator) 0) = Pi.single (r 1) 1 := by
    funext ρ
    obtain ⟨j, rfl⟩ := r.surjective ρ
    have hj := congrFun hr j
    simp only [Equiv.apply_eq_iff_eq, Pi.single_apply]
    rw [hj]
    fin_cases j <;> norm_num [Basis.coord_apply]
  have hI := Φ.isEffectiveCartier_characterRuling_fiber m h hm p hp
  have hclass := congrArg Additive.toMul
    (Φ.toLineBundleClass_characterRuling_fiber m h hm p hp hΦ)
  simp only [toMul_ofMul, hcoeff, ← hirzebruchPicardBasis_apply_zero b e hΦ r hr] at hclass
  let hP := (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension p hp)
    |>.isEffectiveCartier
  have hH : (LineBundleClass.mk hP.toInvertibleSheaf)⁻¹ = H := by
    apply Additive.ofMul.injective
    apply (projectiveLine.picardDegreeEquiv ℂ).injective
    rw [projectiveLine.picardDegreeEquiv_apply, toMul_ofMul, projectiveLine.eulerDegree_inv,
      LineBundleClass.eulerDegree_mk, p.eulerDegree_ker_of_smooth hp]
    simp only [ofMul_toMul, AddEquiv.apply_symm_apply, neg_neg]
  rw [← hH, ← hclass, hI.toLineBundleClass_toCartierDivisor, pullback_inv,
    hP.pullback_mk_toInvertibleSheaf hI]

end TauCeti.Toric.Fan

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] [(X[Φ]).IsProjectiveOver ℂ]
  (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "m" => LinearMap.toAddMonoidHom (b.coord 1)

local notation "f[" Δ "]" => (X[Δ] ↘ S)
local notation "ruling[" Δ "," j "," q "," hq "]" => Fan.characterRuling Δ m
  (Fan.nonneg_or_nonpos_hirzebruch_ruling_character b j q hq)
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "C[" Δ "," j "," hΔ "," q "," hq "]" => Fan.hirzebruchPicardBasis
  (Φ := Δ) b j hΔ q hq

variable {Y : Scheme} {n : ℕ} {T : BlowupTower X[Φ] n Y}

include hc in
/-- On a specified resolution of a Hirzebruch surface, intersecting a class with
a fiber of the resolved ruling reads its section coefficient in the base Picard
marking. The exceptional coefficients do not enter the intersection. -/
theorem hirzebruch_fiber_degree_eq_classIntersectionNumber
    (hT : IsClosedPointTower X[Φ] T) (L : LineBundleClass Y) :
    let : SmoothOfRelativeDimension 2 f[Φ] := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let v := (T.picardMarking hT f[Φ]).symm (Additive.ofMul L)
    (C[Φ,e,hΦ,r,hr]).repr v.1 1 =
      Chow.classIntersectionNumber ℂ Y L
        (pullback (T.toBase ≫ ruling[Φ,e,r,hr]) H) := by
  intro hDim hOver v
  let := hDim
  let := hOver
  let F := C[Φ,e,hΦ,r,hr] 0
  have hmark := classIntersectionNumber_picardMarking ℂ hT v (F, 0)
  have hv : (T.picardMarking hT f[Φ] v).toMul = L :=
    congrArg Additive.toMul ((T.picardMarking hT f[Φ]).apply_symm_apply (Additive.ofMul L))
  dsimp only at hmark
  rw [hv] at hmark
  simp only [picardMarking_apply, picardHom_apply_zero, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, sub_zero] at hmark
  have hdegree := (Fan.hirzebruchPicardBasis_intersection_repr b e hΦ r hr hc v.1).1
  rw [Chow.intersectionBilinForm_apply] at hdegree
  rw [← hdegree, ← pullback_comp,
    ← Fan.hirzebruchPicardBasis_zero_eq_pullback_characterRuling b e hΦ r hr]
  exact hmark.symm

omit [(X[Φ]).IsProjectiveOver ℂ] in
/-- Further closed-point blowups of a specified Hirzebruch resolution preserve
the fiber degree of a pulled-back class. -/
theorem hirzebruch_fiber_degree_eq_of_append
    (hT : IsClosedPointTower X[Φ] T) {a : ℕ} {W : Scheme} {A : BlowupTower Y a W}
    (hA : IsClosedPointTower Y A) (L : LineBundleClass Y) :
    let : SmoothOfRelativeDimension 2 f[Φ] := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let v := (T.picardMarking hT f[Φ]).symm (Additive.ofMul L)
    let w := ((T.append A).picardMarking (hT.append hA) f[Φ]).symm
      (Additive.ofMul (pullback A.toBase L))
    (C[Φ,e,hΦ,r,hr]).repr v.1 1 = (C[Φ,e,hΦ,r,hr]).repr w.1 1 := by
  intro hDim v w
  let := hDim
  have hv : (T.picardHom v).toMul = L := by
    rw [← picardMarking_apply T hT f[Φ], LinearEquiv.apply_symm_apply, toMul_ofMul]
  have hw : w = (v.1, Fin.append v.2 (0 : Fin a → ℤ)) := by
    apply (LinearEquiv.symm_apply_eq _).mpr
    apply Additive.toMul.injective
    simp only [toMul_ofMul, picardMarking_apply, picardHom_append, Fin.append_left,
      Fin.append_right, Prod.mk.eta, picardHom_apply_zero, hv]
  rw [hw]

variable {Ψ : Fan i} [Nonempty Ψ.cones] [(X[Ψ]).IsProjectiveOver ℂ]
  (d : ℤ) (hΨ : Ψ.IsRegular) (hcΨ : Ψ.IsComplete)
  (s : Fin 4 ≃ Ψ.Ray)
  (hs : (fun j ↦ (s j).primitiveGenerator) = ![b 0, b 1, -b 0, d • b 0 - b 1])
  {Z : Scheme} {l : ℕ} {U : BlowupTower X[Ψ] l Z}

include hc hcΨ in
/-- Two resolutions with the same ruling over their common surface give the
same fiber degree for the transported line class, including resolutions with
infinitely near centers. -/
theorem hirzebruch_fiber_degree_eq_of_common_ruling
    (hT : IsClosedPointTower X[Φ] T) (hU : IsClosedPointTower X[Ψ] U)
    (k : Y ≅ Z) (hk : k.hom ≫ U.toBase ≫ f[Ψ] = T.toBase ≫ f[Φ])
    (hruling : k.hom ≫ U.toBase ≫ ruling[Ψ,d,s,hs] = T.toBase ≫ ruling[Φ,e,r,hr])
    (L : LineBundleClass Z) :
    let : SmoothOfRelativeDimension 2 f[Φ] := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : SmoothOfRelativeDimension 2 f[Ψ] := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
    let v := (T.picardMarking hT f[Φ]).symm (Additive.ofMul (pullback k.hom L))
    let w := (U.picardMarking hU f[Ψ]).symm (Additive.ofMul L)
    (C[Φ,e,hΦ,r,hr]).repr v.1 1 = (C[Ψ,d,hΨ,s,hs]).repr w.1 1 := by
  intro hDim hDim' v w
  let := hDim
  let := hDim'
  let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
  let : Z.Over S := ⟨U.toBase ≫ f[Ψ]⟩
  let : k.hom.IsOver S := ⟨hk⟩
  dsimp only [v, w]
  rw [hT.hirzebruch_fiber_degree_eq_classIntersectionNumber b e hΦ hc r hr _,
    hU.hirzebruch_fiber_degree_eq_classIntersectionNumber b d hΨ hcΨ s hs _,
    ← hruling, ← pullback_comp, Chow.classIntersectionNumber_pullback_of_isIso ℂ k.hom]

include hc hcΨ in
/-- The fiber degree is unchanged by a toric change between Hirzebruch models
with the same ruling character. The original projection may first be refined
by any closed-point tower, such as the nodal blowups used to resolve the change.
Both specified projections are recovered from the common subdivision. -/
theorem hirzebruch_fiber_degree_eq_of_common_subdivision
    (hT : IsClosedPointTower X[Φ] T) {a : ℕ} {W : Scheme} {A : BlowupTower Y a W}
    (hA : IsClosedPointTower Y A) (hU : IsClosedPointTower X[Ψ] U)
    (k : W ≅ Z) {Ω : Fan i} (J : Ω.IsSubdivision Φ) (K : Ω.IsSubdivision Ψ)
    (q : W ⟶ X[Ω]) (hq : q ≫ J.toFanHom.algebraicMap = A.toBase ≫ T.toBase)
    (hq' : q ≫ K.toFanHom.algebraicMap = k.hom ≫ U.toBase) (L : LineBundleClass Y) :
    let : SmoothOfRelativeDimension 2 f[Φ] := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : SmoothOfRelativeDimension 2 f[Ψ] := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
    let v := (T.picardMarking hT f[Φ]).symm (Additive.ofMul L)
    let w := (U.picardMarking hU f[Ψ]).symm (Additive.ofMul (pullback (k.inv ≫ A.toBase) L))
    (C[Φ,e,hΦ,r,hr]).repr v.1 1 = (C[Ψ,d,hΨ,s,hs]).repr w.1 1 := by
  intro hDim hDim' v w
  let := hDim
  let := hDim'
  have hk : k.hom ≫ U.toBase ≫ f[Ψ] = (T.append A).toBase ≫ f[Φ] := by
    rw [toBase_append, ← Category.assoc k.hom, ← hq', ← hq]
    simp only [Category.assoc, Fan.algebraicRealization_over,
      FanHom.algebraicMap_comp_algebraicRealizationStructureMap]
  have hruling' : k.hom ≫ U.toBase ≫ ruling[Ψ,d,s,hs] =
      (T.append A).toBase ≫ ruling[Φ,e,r,hr] := by
    rw [toBase_append, ← Category.assoc k.hom, ← hq', ← hq]
    simpa only [Category.assoc] using congrArg (q ≫ ·) (J.comp_characterRuling_eq K m
      (Fan.nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)
      (Fan.nonneg_or_nonpos_hirzebruch_ruling_character b d s hs)).symm
  have heq := (hT.append hA).hirzebruch_fiber_degree_eq_of_common_ruling b e hΦ hc r hr
    d hΨ hcΨ s hs hU k hk hruling' (pullback (k.inv ≫ A.toBase) L)
  dsimp only at heq
  rw [pullback_comp k.hom, Iso.hom_inv_id_assoc] at heq
  exact (hT.hirzebruch_fiber_degree_eq_of_append b e hΦ r hr hA L).trans heq

end QPainleve.BlowupTower.IsClosedPointTower
