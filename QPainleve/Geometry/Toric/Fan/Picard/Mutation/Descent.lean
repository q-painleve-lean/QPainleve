/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.ChargeKernel
public import QPainleve.Geometry.Toric.Fan.Picard.Orthogonal

import QPainleve.AlgebraicGeometry.Blowup.Tower.Numerical

/-!
# Picard pullback for a descended toric mutation

A toric mutation isomorphism on ordered internal blowups can descend through nodal
blowups on either side. The full Picard action of the descended isomorphism is
computed in the ordered toric markings. On the original boundary orthogonals this
pullback is the integral charge-kernel change of coordinates.

The charge comparison descends `mutationPicardEquiv_boundaryOrthogonalEquivChargeKernel_symm`,
the marked Picard calculation of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, Theorems 5.5 and 5.6](https://arxiv.org/html/1309.2573v2#S5).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} {n : ℕ}
  (b : Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray) (k : Fin n)
  (hop : hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones) (hΦ : Φ.IsRegular)

local notation "hv" => Ray.primitiveGenerator_ne_zero (s k)
local notation "hp" => Ray.hull_primitiveGenerator_mem (s k)
local notation "Ψ" => Φ.mutationFan b hv hp hop
local notation "r" => Φ.mutationFanRayEquiv b hv hp hop
local notation "s'" => Φ.mutationFanCenterRays b s k hop
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hop) hΦ
local notation "I" => mutationPicardEquiv k₀ b s k hop hΦ
local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "S" => Spec (CommRingCat.of k₀)

variable (c d : Fin n → k₀ˣ)

local notation "nΦ" => Nonempty.intro (Ray.toCone Φ (s k))
local notation "nΨ" => Nonempty.intro (Ray.toCone (Ψ) (r (s k)))

local notation "A" => internalBlowupTower k₀ (h₀ := nΦ) b s c
local notation "B" => internalBlowupTower k₀ (h₀ := nΨ) b s' d
local notation "U" => WithBoundary.toTower (Sigma.snd A)
local notation "W" => WithBoundary.toTower (Sigma.snd B)
local notation "μ₀" => internalBlowupPicardMarking k₀ (h₀ := nΦ) b s c hΦ
local notation "μ₁" => internalBlowupPicardMarking k₀ (h₀ := nΨ) b s' d hΨ

/-- For a commuting contraction square, the pullback on the original surfaces has the
same full toric marking formula as the isomorphism of the ordered blowup models. -/
theorem pullback_nodal_mutation_picard_marking
    {X Y : Scheme} {p : (A).1 ⟶ X} {q : (B).1 ⟶ Y}
    {e : (A).1 ≅ (B).1} {g : X ≅ Y}
    (hsquare : e.hom ≫ q = p ≫ g.hom)
    (hmark : ∀ z, pullback e.hom ((W).picardHom z).toMul =
      ((U).picardHom (I z)).toMul)
    (L : LineBundleClass Y) :
    (μ₀).symm (Additive.ofMul (pullback p (pullback g.hom L))) =
      I ((μ₁).symm (Additive.ofMul (pullback q L))) := by
  apply (μ₀).injective
  rw [LinearEquiv.apply_symm_apply, internalBlowupPicardMarking_apply k₀ (h₀ := nΦ)]
  apply Additive.toMul.injective
  rw [toMul_ofMul, ← hmark, ← internalBlowupPicardMarking_apply k₀ (h₀ := nΨ) b s' d hΨ,
    LinearEquiv.apply_symm_apply, toMul_ofMul, pullback_comp, pullback_comp, hsquare]

section Orthogonal

variable {X Y X' Y' : Scheme}
  [X.Over (Spec (.of k₀))] [X'.Over (Spec (.of k₀))]
  [X.IsProjectiveOver k₀] [X'.IsProjectiveOver k₀]
  [IsIntegral X] [IsIntegral X']
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k₀))]
  [SmoothOfRelativeDimension 2 (X' ↘ Spec (.of k₀))]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm k₀ X)]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm k₀ X')]
  {D : X.IdealSheafData} {D' : X'.IdealSheafData} {m l : ℕ}
  {P : BlowupTower X m Y} {Q : BlowupTower X' l Y'}
  (hP : IsNodalBoundaryTower D (X ↘ Spec (.of k₀)) (𝟙 X) P)
  (hQ : IsNodalBoundaryTower D' (X' ↘ Spec (.of k₀)) (𝟙 X') Q)

local notation "projection" a:arg T:arg => (Iso.inv a ≫ BlowupTower.toBase T)

local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "χ" t => (fun j ↦ LinearMap.toAddMonoidHom (b.detDualEquiv
  (Ray.primitiveGenerator (t j))))
local notation "χzero" t => (fun j ↦ b.detDualEquiv_self (Ray.primitiveGenerator (t j)))
local notation "χsurj" t => (fun j ↦ Ray.surjective_detCharacter (t j) b)
local notation "J(" hn "," t "," c₀ ")" =>
  (fun j ↦ Ray.internalCenter k₀ (h₀ := hn) b (t j) (c₀ j))
local notation "hJ(" hn "," t "," c₀ ")" =>
  (fun j ↦ Ray.internalCenter_val k₀ (h₀ := hn) b (t j) (c₀ j))
-- This is the model in the domain of the boundary-orthogonal charge comparison.
-- `internalBlowupTower_eq_alongBoundary` identifies it with the ordered internal blowups.
local notation "A₀" =>
  alongBoundary (Scheme.IdealSheafData.subschemeι (Φ.toricBoundaryIdeal k₀ nΦ)) J(nΦ, s, c)
local notation "A₁" =>
  alongBoundary (Scheme.IdealSheafData.subschemeι (Fan.toricBoundaryIdeal k₀ (Ψ) nΨ)) J(nΨ, s', d)
local notation "U₀" => WithBoundary.toTower (Sigma.snd A₀)
local notation "U₁" => WithBoundary.toTower (Sigma.snd A₁)
local notation "hU₀" => isClosedPointTower_alongBoundary_binomialCenters k₀
  rankTwo s (χ s) (χzero s) (χsurj s) c J(nΦ, s, c) hJ(nΦ, s, c)
local notation "hU₁" => isClosedPointTower_alongBoundary_binomialCenters k₀
  rankTwo s' (χ s') (χzero s') (χsurj s') d J(nΨ, s', d) hJ(nΨ, s', d)
local notation "K₀" a:arg ha:arg hD:arg =>
  picardBoundaryOrthogonalEquivChargeKernel k₀ hΦ rankTwo s (χ s) (χzero s)
    (χsurj s) c J(nΦ, s, c) hJ(nΦ, s, c) hP a ha hD
local notation "K₁" a:arg ha:arg hD:arg =>
  picardBoundaryOrthogonalEquivChargeKernel k₀ hΨ rankTwo s' (χ s') (χzero s')
    (χsurj s') d J(nΨ, s', d) hJ(nΨ, s', d) hQ a ha hD
local notation "transport" => mutationFanChargeKernelEquiv b s k hop

/-- In the original surfaces, mutation pulls the boundary-orthogonal class of a target
charge relation back to the class of its integral cluster exponent transport. -/
theorem pullback_nodal_mutation_chargeKernel
    [@Scheme.IsProjectiveOver k₀ _ (Φ.finiteFanScheme k₀) (Fan.finiteFanSchemeOver k₀ Φ)]
    [@Scheme.IsProjectiveOver k₀ _ (Fan.finiteFanScheme k₀ (Ψ)) (Fan.finiteFanSchemeOver k₀ (Ψ))]
    (a : Y ≅ (A₀).1) (a' : Y' ≅ (A₁).1)
    (ha : a.inv ≫ P.toBase ≫ (X ↘ S) = (U₀).toBase ≫ ((Φ.finiteFanScheme k₀) ↘ S))
    (ha' : a'.inv ≫ Q.toBase ≫ (X' ↘ S) = (U₁).toBase ≫ ((Fan.finiteFanScheme k₀ (Ψ)) ↘ S))
    (hD : ((D.comap P.toBase).comap a.inv).support = (A₀).2.boundaryι.ker.support)
    (hD' : ((D'.comap Q.toBase).comap a'.inv).support = (A₁).2.boundaryι.ker.support)
    {e : (A₀).1 ≅ (A₁).1} {g : X ≅ X'}
    (hsquare : e.hom ≫ projection a' Q = projection a P ≫ g.hom)
    (hmark : ∀ z, pullback e.hom ((U₁).picardHom z).toMul =
      ((U₀).picardHom (I z)).toMul)
    (hg : g.hom ≫ (X' ↘ S) = X ↘ S)
    (x : (rayChargeMap s').ker) :
    let : Nonempty Φ.cones := nΦ
    let : Nonempty (Ψ).cones := nΨ
    pullback g.hom ((K₁ a' ha' hD').symm x).val.toMul =
      ((K₀ a ha hD).symm (transport x)).val.toMul := by
  let : Nonempty Φ.cones := nΦ
  let : Nonempty (Ψ).cones := nΨ
  let smooth₀ : SmoothOfRelativeDimension 2 ((Φ.finiteFanScheme k₀) ↘ S) :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
  let smooth₁ : SmoothOfRelativeDimension 2 ((Fan.finiteFanScheme k₀ (Ψ)) ↘ S) :=
    rankTwo ▸ (Ψ).smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΨ
  let T₀ := @Chow.intersectionBilinForm k₀ _ _ (Φ.finiteFanScheme k₀) _ _ _ smooth₀
  let T₁ := @Chow.intersectionBilinForm k₀ _ _ (Fan.finiteFanScheme k₀ (Ψ)) _ _ _ smooth₁
  let negDot := -(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin n → ℤ))
  let C₀ := T₀.prod negDot
  let C₁ := T₁.prod negDot
  let : C₀.IsPerfPair :=
    isPerfPair_internal_markedForm k₀ hΦ rankTwo s (χ s) (χzero s) (χsurj s)
      c J(nΦ, s, c) hJ(nΦ, s, c) hP a ha
  let : C₁.IsPerfPair :=
    isPerfPair_internal_markedForm k₀ hΨ rankTwo s' (χ s') (χzero s') (χsurj s')
      d J(nΨ, s', d) hJ(nΨ, s', d) hQ a' ha'
  have hOver : e.hom ≫ (U₁).toBase ≫ ((Fan.finiteFanScheme k₀ (Ψ)) ↘ S) =
      (U₀).toBase ≫ ((Φ.finiteFanScheme k₀) ↘ S) := by
    rw [← ha', ← Category.assoc a'.inv Q.toBase, ← Category.assoc e.hom, hsquare,
      Category.assoc, hg, Category.assoc a.inv P.toBase, ha]
  have hI : ∀ y z, C₀ (I y) (I z) = C₁ y z := by
    let : SmoothOfRelativeDimension 2 ((Φ.finiteFanScheme k₀) ↘ S) := smooth₀
    let : SmoothOfRelativeDimension 2 ((Fan.finiteFanScheme k₀ (Ψ)) ↘ S) := smooth₁
    intro y z
    have h := classIntersectionNumber_picardEquivOfCommonResolution k₀ hU₁ hU₀ e hOver y z
    have hE (a₀ : Pic((Fan.finiteFanScheme k₀ (Ψ))) × (Fin n → ℤ)) :
        picardEquivOfCommonResolution k₀ hU₁ hU₀ e a₀ = I a₀ := by
      apply (hU₀).bijective_picardHom ((Φ.finiteFanScheme k₀) ↘ S) |>.injective
      exact (picardHom_picardEquivOfCommonResolution k₀ _ _ _ _).trans
        (congrArg Additive.ofMul (hmark a₀))
    simpa only [hE, C₀, C₁, T₀, T₁, negDot, LinearMap.BilinForm.prod_apply,
      Chow.intersectionBilinForm_apply, LinearMap.neg_apply, dotProductBilin_apply_apply,
      dotProduct, sub_eq_add_neg] using h
  have hK := mutationPicardEquiv_boundaryOrthogonalEquivChargeKernel_symm k₀
    b s k hop hΦ C₀ C₁ hI x
  have hsource := picardHom_boundaryOrthogonalEquivChargeKernel_symm k₀
    hΦ rankTwo s (χ s) (χzero s) (χsurj s) c J(nΦ, s, c) hJ(nΦ, s, c) hP a ha hD (transport x)
  have htarget := picardHom_boundaryOrthogonalEquivChargeKernel_symm k₀
    hΨ rankTwo s' (χ s') (χzero s') (χsurj s') d J(nΨ, s', d) hJ(nΨ, s', d) hQ a' ha' hD' x
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  apply hP.isClosedPointTower.injective_pullback_toBase (X ↘ S)
  apply (pullbackEquiv a.symm).injective
  simp only [pullbackEquiv_apply, Iso.symm_hom, pullback_comp]
  rw [← Category.assoc a.inv P.toBase, ← hsquare, ← pullback_comp, ← htarget, hmark,
    hK, hsource]

end Orthogonal

end TauCeti.Toric.Fan
