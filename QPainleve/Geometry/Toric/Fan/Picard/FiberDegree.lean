/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nef
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Picard
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Ruling.Basic
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch
public import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef.Pullback
import QPainleve.Geometry.Toric.Fan.Picard.Ruling
import QPainleve.Geometry.Toric.Fan.Ruling.Subdivision
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample
import TauCeti.AlgebraicGeometry.RationalPoint.IdealSheaf

/-!
# Fiber degree on Hirzebruch resolutions

The fiber degree read from the Picard marking of a resolution is the intersection
with the pullback of a point under the resolved ruling. Two Hirzebruch models with
a common resolved ruling therefore give the same fiber degree, even when their
closed-point towers have different exceptional coordinates. This is the numerical
comparison used in the preparation of a Hirzebruch surface for the quadric case in
[Lutz's appendix to Hacking and Keating][HKL], Proposition 8.11, Case C.
A ruling fiber through the projected center also bounds each base order of a nef class,
including at infinitely near centers.

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.Toric

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "rulingLineClass" =>
  Additive.toMul (AddEquiv.symm (projectiveLine.picardDegreeEquiv ℂ) 1)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "m" => LinearMap.toAddMonoidHom (b.coord 1)
local notation "C" => Φ.hirzebruchPicardBasis b e hΦ r hr

open scoped Classical in
include hr in
private theorem hirzebruch_ruling_fiber_coefficients :
    (fun ρ : Φ.Ray ↦ max (m ρ.primitiveGenerator) 0) = Pi.single (r 1) 1 :=
  hirzebruch_ruling_coordinateFiber_coefficients b e r hr 0

variable [Nonempty Φ.cones]

/-- The first Hirzebruch Picard basis vector is the pullback of `𝒪(1)`
under the ruling defined by the second basis character. -/
theorem hirzebruchPicardBasis_zero_eq_pullback_characterRuling :
    (Φ.hirzebruchPicardBasis b e hΦ r hr 0).toMul =
      pullback (Φ.characterRuling m (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr))
        rulingLineClass := by
  classical
  let h := nonneg_or_nonpos_hirzebruch_ruling_character b e r hr
  let p := projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 0
  have hp : p ≫ (projectiveLine ℂ ↘ S) = 𝟙 S := by
    simp [p, projectiveLine.polynomialPoint_over]
  have hm := hirzebruch_ruling_character_ne_zero b
  have hI := Φ.isEffectiveCartier_characterRuling_fiber m h hm p hp
  have hclass := congrArg Additive.toMul
    (Φ.toLineBundleClass_characterRuling_fiber m h hm p hp hΦ)
  simp only [toMul_ofMul, hirzebruch_ruling_fiber_coefficients b e r hr,
    ← hirzebruchPicardBasis_apply_zero b e hΦ r hr] at hclass
  let hP := (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension p hp)
    |>.isEffectiveCartier
  have hH : (LineBundleClass.mk hP.toInvertibleSheaf)⁻¹ = rulingLineClass := by
    apply Additive.ofMul.injective
    apply (projectiveLine.picardDegreeEquiv ℂ).injective
    rw [projectiveLine.picardDegreeEquiv_apply, toMul_ofMul, projectiveLine.eulerDegree_inv,
      LineBundleClass.eulerDegree_mk, p.eulerDegree_ker_of_smooth hp]
    simp only [ofMul_toMul, AddEquiv.apply_symm_apply, neg_neg]
  rw [← hH, ← hclass, hI.toLineBundleClass_toCartierDivisor, pullback_inv,
    hP.pullback_mk_toInvertibleSheaf hI]

/-- The fiber class of a Hirzebruch fan has an effective Cartier representative through
every closed point, obtained as the scheme-theoretic fiber of the ruling at the point's image. -/
theorem exists_isEffectiveCartier_mem_support_hirzebruchPicardBasis_zero
    (x : X[Φ]) (hx : IsClosed ({x} : Set X[Φ])) :
    ∃ (D : (X[Φ]).IdealSheafData) (hD : D.IsEffectiveCartier), x ∈ D.support ∧
      Additive.ofMul (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ = C 0 := by
  classical
  let h := nonneg_or_nonpos_hirzebruch_ruling_character b e r hr
  have hm := hirzebruch_ruling_character_ne_zero b
  let f := (X[Φ] ↘ S)
  have hdim : SmoothOfRelativeDimension 2 f :=
    (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)) ▸
      Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : Smooth f := hdim.smooth
  let q := Φ.characterRuling m h
  let p := pointOfClosedPoint f x hx ≫ q
  have hp : p ≫ (projectiveLine ℂ ↘ S) = 𝟙 S := by
    simpa only [p, Category.assoc, comp_over q S] using pointOfClosedPoint_comp f x hx
  have : IsClosedImmersion p := p.isClosedImmersion_of_comp_eq_id hp
  let hD := Φ.isEffectiveCartier_characterRuling_fiber m h hm p hp
  refine ⟨p.ker.comap q, hD, ?_, ?_⟩
  · rw [← SetLike.mem_coe, Scheme.IdealSheafData.support_comap,
      TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage, Scheme.Hom.support_ker,
      p.isClosedEmbedding.isClosed_range.closure_eq]
    refine ⟨IsLocalRing.closedPoint ℂ, (Scheme.Hom.comp_apply _ _ _).trans ?_⟩
    exact congrArg q (pointOfClosedPoint_apply f x hx (IsLocalRing.closedPoint ℂ))
  · have hclass := Φ.toLineBundleClass_characterRuling_fiber m h hm p hp hΦ
    simpa only [Scheme.IdealSheafData.IsEffectiveCartier.toLineBundleClass_toCartierDivisor,
      hirzebruch_ruling_fiber_coefficients b e r hr, hirzebruchPicardBasis_apply_zero] using hclass

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
        (pullback (T.toBase ≫ ruling[Φ,e,r,hr]) rulingLineClass) := by
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

namespace QPainleve.BlowupTower.IsClosedPointTower

open Chow

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "f" => (X[Φ] ↘ S)
local notation "C" => Φ.hirzebruchPicardBasis b e hΦ r hr
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)

variable [Φ.algebraicRealization.IsProjectiveOver ℂ] (hc : Φ.IsComplete)
  {Y : Scheme} {n : ℕ} {T : BlowupTower Φ.algebraicRealization n Y}
  (hT : IsClosedPointTower Φ.algebraicRealization T)

include hT in
/-- The fiber degree of the base class bounds each base order of a marked nef class
on a point blowup tower of a complete regular Hirzebruch fan. -/
theorem neg_exceptionalCoeff_le_hirzebruch_fiber_degree
    (v : Additive (LineBundleClass X[Φ]) × (Fin n → ℤ))
    (hv : (T.picardHom v).toMul.IsNef ℂ (T.toBase ≫ f)) (j : Fin n) :
    let := hc.nonempty_cones
    (-v.2 j) ≤ (C).repr v.1 1 := by
  intro hcones
  let := hcones
  let : SmoothOfRelativeDimension 2 f :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : IsNoetherian X[Φ] := isNoetherian_of_finiteType f
  obtain ⟨D, hD, hj, hClass⟩ := Φ.exists_isEffectiveCartier_mem_support_hirzebruchPicardBasis_zero
    b e hΦ r hr _ (hT.isClosed_baseCenter j)
  have hBound := hT.neg_exceptionalCoeff_le_classIntersectionNumber_of_mem_support hv j hD hj
  rw [← toMul_ofMul (mk hD.toInvertibleSheaf)⁻¹, ← intersectionBilinForm_apply, hClass,
    (Φ.hirzebruchPicardBasis_intersection_repr b e hΦ r hr hc v.1).1] at hBound
  exact hBound

open TauCeti.SymmetricAlgebra

local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)

/-- Every base order of a resolved plane line system on a Hirzebruch surface is at most
the fiber degree of the system. The bound holds at corners, at smooth points on
sections and fibers, and at infinitely near centers. -/
theorem base_order_le_hirzebruch_fiber_degree
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f) (j : Fin n) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X[Φ] := isNoetherian_of_finiteType f
    let v : Additive (LineBundleClass X[Φ]) × (Fin n → ℤ) :=
      (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    (-v.2 j) ≤ (C).repr v.1 1 := by
  intro hcones hdim hnoeth v
  let := hcones
  let := hdim
  let := hnoeth
  let : Y.Over S := ⟨T.toBase ≫ f⟩
  have : g.IsOver S := ⟨hg⟩
  have hH : (H).IsAmple := isAmple_twistingSheaf ℂ (Fin 3 → ℂ) Nat.one_pos
  have hClass : (T.picardHom v).toMul = pullback g H := by
    rw [← picardMarking_apply _ hT f, LinearEquiv.apply_symm_apply, toMul_ofMul]
  exact hT.neg_exceptionalCoeff_le_hirzebruch_fiber_degree b e hΦ r hr hc v
    (hClass.symm ▸ hH.isNef.pullback g) j

end QPainleve.BlowupTower.IsClosedPointTower
