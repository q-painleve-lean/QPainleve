/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.ChargeKernel.Transport
public import QPainleve.SignedClusterModularGroup.Realization.Presentation

import QPainleve.Algebra.Cluster.Word.Monomial
import QPainleve.AlgebraicGeometry.Chow.Nef.Boundary
import QPainleve.Geometry.Toric.Fan.Presentation.Genus
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.Endpoint.ConnectingWord
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Orthogonal

/-!
# Transport of the total boundary exponent

The negatives of the exceptional coordinates of the total boundary class give
its Casimir exponent. In a contracted fiber the exponent entries are the Weil
multiplicities at the center rays. A connecting word pulls the target total
boundary monomial back to the source total boundary monomial raised to the
inversion sign. The two markings can use different toric fans and different
ordered centers.

The comparison uses `GeometricRealization.exponentEquiv_eq_signed_picard_pullback`.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Multiplicative Quiver
open Scheme Scheme.IdealSheafData
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "cartier(" M ")" => MarkedSurface.isEffectiveCartier_boundaryIdeal M
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "orth[" H "," d "]" =>
  LinearMap.BilinForm.orthogonal H (Submodule.span ℤ (Set.range d))
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "total[" d "]" => ∑ j, d j

namespace CompleteToricPresentation

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}
  (Q : CompleteToricPresentation i b r L γ)

/-- The exponent of the total boundary, in the ordered center coordinates of the
presentation. Its entries are the negatives of the exceptional coordinates of the
total boundary class. -/
def totalBoundaryExponent (d : ZMod n → L) : Fin r → ℤ :=
  -(Q.inclusion (total[d])).2

theorem totalBoundaryExponent_def (d : ZMod n → L) :
    Q.totalBoundaryExponent d = -(Q.inclusion (total[d])).2 :=
  (rfl)

attribute [local instance] CompleteToricPresentation.neZero CompleteToricPresentation.prestable

private local instance : Nonempty Q.fan.cones := Q.complete.nonempty_cones

/-- In a contracted fiber the exponent at a center is the multiplicity of its ray
in the actual total boundary transform. -/
theorem totalBoundaryExponent_eq_totalBoundaryRayMultiplicity
    {c : GeometricRealization.Point Centers[r]} {M : MarkedSurface ℂ n H XTor[r]}
    (p : ContractedToricFiber (h₀ := Q.complete.nonempty_cones)
      b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c] M)
    (d : ZMod n → L) (hd : M.boundaryClass (cartier(M)) = d) :
    Q.totalBoundaryExponent d = fun j ↦
      p.totalBoundaryRayMultiplicity (h₀ := Q.complete.nonempty_cones) (cartier(M)) (Q.rays j) := by
  rw [← hd, Q.totalBoundaryExponent_def, p.inclusion_sum_boundaryClass (cartier(M)),
    Fan.markedBoundaryMap_apply]
  funext j
  simp only [Pi.neg_apply, neg_neg]

private theorem smoothOfRelativeDimension_fan :
    SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S) := by
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  rw [← hN, Q.fan.algebraicRealization_over]
  exact Q.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Q.regular

local notation "Aux" => LinearMap.BilinForm.prod
  (Chow.intersectionBilinForm ℂ Q.fan.algebraicRealization)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))

private theorem totalBoundaryExponent_eq_of_chargeKernelEquiv
    [Q.fan.algebraicRealization.IsProjectiveOver ℂ]
    [SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S)] [LinearMap.IsPerfPair Aux]
    {d : ZMod n → L} (e : orth[H,d] ≃ₗ[ℤ] (Fan.rayChargeMap Q.rays).ker)
    (he : ∀ y, Q.inclusion (e.symm y).val =
      ((Fan.boundaryOrthogonalEquivChargeKernel Q.regular Q.rays Aux).symm y).val)
    (x : orth[H,d]) (hx : x.val = total[d]) :
    Q.totalBoundaryExponent d = (e x : Fin r → ℤ) := by
  simpa only [totalBoundaryExponent_def, LinearEquiv.symm_apply_apply, hx,
    Fan.boundaryOrthogonalEquivChargeKernel_symm_snd, neg_neg]
    using congrArg (fun p ↦ -p.2) (he (e x))

private theorem HasNodalModel.genus_eq_zero_at_boundary_normalization
    {c : GeometricRealization.Point Centers[r]} {M : MarkedSurface ℂ n H XTor[r]}
    (h : Q.HasNodalModel c M) :
    letI := M.prestable_boundaryImage
    ∀ v : irreducibleComponents (D[M].subscheme.singularLocus ℂ).blowup,
      (D[M].subscheme.blowupComponent (K := ℂ) v).toScheme.genus ℂ = 0 := by
  let : IsIntegral M.surface := M.integral
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : PrestableFamily (D[M].subscheme ↘ S) := M.prestable_boundaryImage
  exact h.hasToricPresentation.genus_blowupComponent_eq_zero (cartier(M))

/-- The total boundary exponent is a charge relation whenever the total class is
orthogonal to the boundary. -/
theorem HasNodalModel.totalBoundaryExponent_mem_chargeKernel
    {c : GeometricRealization.Point Centers[r]} {M : MarkedSurface ℂ n H XTor[r]}
    (h : Q.HasNodalModel c M) {d : ZMod n → L}
    (hd : M.boundaryClass (cartier(M)) = d) (hδ : total[d] ∈ orth[H,d]) :
    Q.totalBoundaryExponent d ∈ (Fan.rayChargeMap Q.rays).ker := by
  let : Q.fan.algebraicRealization.IsProjectiveOver ℂ :=
    Q.fan.isProjectiveOver_algebraicRealization_of_isComplete Q.regular Q.complete b
  let := Q.smoothOfRelativeDimension_fan
  obtain ⟨hAux, e, he, -⟩ := h.existsUnique_chargeKernelEquiv (cartier(M)) hd
  let := hAux
  rw [Q.totalBoundaryExponent_eq_of_chargeKernelEquiv e he ⟨total[d], hδ⟩ rfl]
  exact (e ⟨total[d], hδ⟩).property

end CompleteToricPresentation

private theorem mem_orthogonal_total_boundary
    {r n : ℕ} [NeZero n] {L : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L} {d : ZMod n → L}
    (M : MarkedSurface ℂ n H XTor[r]) (hd : M.boundaryClass (cartier(M)) = d)
    (hnef : classOf(cartier(M)).IsNef ℂ (M.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M.surface classOf(cartier(M)) classOf(cartier(M)) = 0) :
    total[d] ∈ orth[H,d] := by
  let : IsIntegral M.surface := M.integral
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  rw [← hd, ← M.picardMarking_mem_boundaryOrthogonal_iff (cartier(M)),
    M.picardMarking_sum_boundaryClass (cartier(M))]
  exact ((cartier(M)).effectiveCartierClass_mem_boundaryOrthogonal_iff_of_isNef hnef).mpr hsq

namespace GeometricRealization

private theorem picard_total_boundary
    {n r : ℕ} [NeZero n] {L₀ L₁ : Type} [AddCommGroup L₀] [AddCommGroup L₁]
    {H₀ : LinearMap.BilinForm ℤ L₀} {H₁ : LinearMap.BilinForm ℤ L₁}
    {M₀ : Point Centers[r] → MarkedSurface ℂ n H₀ XTor[r]}
    {M₁ : Point Centers[r] → MarkedSurface ℂ n H₁ XTor[r]}
    {d₀ : ZMod n → L₀} {d₁ : ZMod n → L₁}
    {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
    [C.IsOver Centers[r].hom Centers[r].hom] {F : XTor[r] ⤏ XTor[r]} [F.IsDominant]
    (R : GeometricRealization M₀ M₁ C F)
    (hmark₀ : ∀ c j, (M₀ c).boundaryClass (cartier(M₀ c)) j = d₀ j)
    (hmark₁ : ∀ c j, (M₁ c).boundaryClass (cartier(M₁ c)) j = d₁ j) :
    R.picard (total[d₁]) = total[d₀] := by
  obtain ⟨c⟩ := nonempty_centerPoint C
  rw [map_sum]
  have h (j : ZMod n) : R.picard (d₁ j) = d₀ (cycleVertexPerm R.boundaryAction⁻¹ j) := by
    simpa only [hmark₀, hmark₁] using R.picard_boundaryClass c (cartier(_)) (cartier(_)) j
  simp only [h]
  exact Equiv.sum_comp (cycleVertexPerm R.boundaryAction⁻¹) d₀

variable {r n : ℕ} [NeZero n]
  {N₀ V₀ N₁ V₁ : Type} [AddCommGroup N₀] [AddCommGroup V₀] [Module ℝ V₀]
  [AddCommGroup N₁] [AddCommGroup V₁] [Module ℝ V₁]
  {i₀ : N₀ →+ V₀} {i₁ : N₁ →+ V₁} {b₀ : Module.Basis (Fin 2) ℤ N₀}
  {b₁ : Module.Basis (Fin 2) ℤ N₁}
  {L₀ L₁ γ₀ γ₁ : Type} [AddCommGroup L₀] [AddCommGroup L₁]
  {H₀ : LinearMap.BilinForm ℤ L₀} {H₁ : LinearMap.BilinForm ℤ L₁}
  {M₀ : Point Centers[r] → MarkedSurface ℂ n H₀ XTor[r]}
  {M₁ : Point Centers[r] → MarkedSurface ℂ n H₁ XTor[r]}
  {d₀ : ZMod n → L₀} {d₁ : ZMod n → L₁}
  {Q₀ : CompleteToricPresentation i₀ b₀ r L₀ γ₀} {Q₁ : CompleteToricPresentation i₁ b₁ r L₁ γ₁}
  {E₀ E₁ : SkewExchangeMatrix (Fin r)} {w : Word E₀ E₁}

local notation "src[" C "," c "]" =>
  c ≫ Scheme.PartialMap.domainSource (X := Centers[r]) (Y := Centers[r]) C
local notation "dst[" C "," c "]" =>
  c ≫ Scheme.PartialMap.domainTarget (X := Centers[r]) (Y := Centers[r]) C

/-- The exponent pullback of a geometrically realized connecting word sends the target
total boundary exponent to the source total boundary exponent multiplied by its
ordered branch sign. The target total class is assumed to be orthogonal to the boundary. -/
theorem exponentEquiv_totalBoundaryExponent
    {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
    [C.IsOver Centers[r].hom Centers[r].hom]
    (R : GeometricRealization M₀ M₁ C (w.xRationalMap ℂ))
    (hC : C.hom = C.domain.ι ≫ (w.centerIso ℂ).hom)
    (hmark₀ : ∀ c j, (M₀ c).boundaryClass (cartier(M₀ c)) j = d₀ j)
    (hmark₁ : ∀ c j, (M₁ c).boundaryClass (cartier(M₁ c)) j = d₁ j)
    (models₀ : ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) C,
      Q₀.HasNodalModel (src[C,c]) (M₀ (src[C,c])))
    (models₁ : ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) C,
      Q₁.HasNodalModel (dst[C,c]) (M₁ (dst[C,c])))
    (hδ₁ : total[d₁] ∈ orth[H₁,d₁]) :
    w.exponentEquiv (Q₁.totalBoundaryExponent d₁) =
      R.orientation • Q₀.totalBoundaryExponent d₀ := by
  let := Q₀.complete.nonempty_cones
  let := Q₁.complete.nonempty_cones
  let := Q₀.prestable
  let := Q₁.prestable
  let := Q₀.neZero
  let := Q₁.neZero
  let := Q₀.fan.isProjectiveOver_algebraicRealization_of_isComplete Q₀.regular Q₀.complete b₀
  let := Q₁.fan.isProjectiveOver_algebraicRealization_of_isComplete Q₁.regular Q₁.complete b₁
  let := Q₀.smoothOfRelativeDimension_fan
  let := Q₁.smoothOfRelativeDimension_fan
  obtain ⟨c⟩ := nonempty_centerPoint C
  obtain ⟨hAux₀, e₀, he₀, -⟩ := (models₀ c).existsUnique_chargeKernelEquiv (cartier(_))
    (funext (hmark₀ (src[C,c])))
  obtain ⟨hAux₁, e₁, he₁, -⟩ := (models₁ c).existsUnique_chargeKernelEquiv (cartier(_))
    (funext (hmark₁ (dst[C,c])))
  let := hAux₀
  let := hAux₁
  let t₁ : orth[H₁,d₁] := ⟨_, hδ₁⟩
  let t₀ := R.boundaryOrthogonalEquiv hmark₀ hmark₁ t₁
  have ht : t₀.val = total[d₀] :=
    (R.coe_boundaryOrthogonalEquiv_apply hmark₀ hmark₁ t₁).trans
      (R.picard_total_boundary hmark₀ hmark₁)
  rw [Q₀.totalBoundaryExponent_eq_of_chargeKernelEquiv e₀ he₀ t₀ ht,
    Q₁.totalBoundaryExponent_eq_of_chargeKernelEquiv e₁ he₁ t₁ rfl]
  have h := R.exponentEquiv_eq_signed_picard_pullback hmark₀ hmark₁ e₀ e₁ he₀ he₁ hC
    Q₀.rayOrder (fun j ↦ (Q₀.cycle.component_apply j).symm.trans (Q₀.component_eq j))
    (fun j ↦ (Q₀.positive j).1) Q₀.exists_cone_of_numbered_node
    Q₁.rayOrder (fun j ↦ (Q₁.cycle.component_apply j).symm.trans (Q₁.component_eq j))
    (fun j ↦ (Q₁.positive j).1) Q₁.exists_cone_of_numbered_node
    (fun c ↦ ⟨(models₀ c).nonempty_contractedToricFiber,
      (models₀ c).genus_eq_zero_at_boundary_normalization Q₀⟩)
    (fun c ↦ ⟨(models₁ c).nonempty_contractedToricFiber,
      (models₁ c).genus_eq_zero_at_boundary_normalization Q₁⟩) t₁
  simpa only [t₀, Units.smul_def, map_smul, Submodule.coe_smul] using h

local notation "Cw[" w "," P "]" => Path.centerPartialMap ℂ w P
local notation "Cnil[" P "]" => Path.centerPartialMap ℂ Path.nil P
local notation "mon[" k "," v "]" =>
  CharacterTorus.monomial k (ofAdd (Finsupp.equivFunOnFinite.symm v))

/-- In two marked toric presentations of primitive nef square-zero anticanonical
cycles, a connecting word pulls back the target total boundary monomial to the
source total boundary monomial raised to the inversion sign. Both exponents are
read from the given presentations, and the formula holds in the independent
X coordinates over every coefficient field. -/
theorem xPullback_totalBoundaryExponent_of_presentations
    (k : Type*) [Field k]
    (w : Word E₀ E₁) (P₀ : ChargeSeed E₀ N₀) (P₁ : ChargeSeed E₁ N₁)
    (hform₀ : P₀.form = b₀.detDualEquiv.toLinearMap)
    (hcharge₀ : P₀.charge = Fan.rayChargeMap Q₀.rays)
    (hform₁ : P₁.form = b₁.detDualEquiv.toLinearMap)
    (hcharge₁ : P₁.charge = Fan.rayChargeMap Q₁.rays)
    (models₀ : ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P₀],
      Q₀.HasNodalModel (dst[Cnil[P₀],c]) (M₀ (dst[Cnil[P₀],c])))
    (models₁ : ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P₁],
      Q₁.HasNodalModel (dst[Cnil[P₁],c]) (M₁ (dst[Cnil[P₁],c])))
    {a₀ a₁ : Point Centers[r]} (ref₁ : Q₁.HasNodalModel a₁ (M₁ a₁))
    (hmark₀ : ∀ c j, (M₀ c).boundaryClass (cartier(M₀ c)) j = d₀ j)
    (hmark₁ : ∀ c j, (M₁ c).boundaryClass (cartier(M₁ c)) j = d₁ j)
    (hprim₀ : IsPrimitive (Additive.ofMul classOf(cartier(M₀ a₀))))
    (hprim₁ : IsPrimitive (Additive.ofMul classOf(cartier(M₁ a₁))))
    (hnef₀ : classOf(cartier(M₀ a₀)).IsNef ℂ ((M₀ a₀).surface ↘ S))
    (hnef₁ : classOf(cartier(M₁ a₁)).IsNef ℂ ((M₁ a₁).surface ↘ S))
    (hsq₀ : Chow.classIntersectionNumber ℂ (M₀ a₀).surface
      classOf(cartier(M₀ a₀)) classOf(cartier(M₀ a₀)) = 0)
    (hsq₁ : Chow.classIntersectionNumber ℂ (M₁ a₁).surface
      classOf(cartier(M₁ a₁)) classOf(cartier(M₁ a₁)) = 0) :
    w.xPullback k (mon[k,Q₁.totalBoundaryExponent d₁]) =
      (mon[k,Q₀.totalBoundaryExponent d₀]) ^ ((-1 : ℤˣ) ^ w.inversionCount : ℤ) := by
  obtain ⟨R, hsign, -, hmodels₁⟩ := exists_realize_signed_word_to_presentation
    w P₀ P₁ Q₀ Q₁ hform₀ hcharge₀ hform₁ hcharge₁ M₀ M₁ models₀ models₁ ref₁
    (fun c ↦ cartier(M₀ c)) (fun c ↦ cartier(M₁ c)) hnef₀ hnef₁ hsq₀ hsq₁ hprim₀ hprim₁
    d₀ d₁ hmark₀ hmark₁
  have hmodels₀ (c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cw[w,P₀]) :
      Q₀.HasNodalModel (src[Cw[w,P₀],c]) (M₀ (src[Cw[w,P₀],c])) := by
    have hU : (Cw[w,P₀]).domain ≤ (Cnil[P₀]).domain := by
      simpa only [Path.centerPartialMap_domain] using w.centerOpen_le_centerOpen_nil ℂ P₀
    have hc := ((Cw[w,P₀]).exists_section_comp_domainSource_eq_iff
      (Y := Centers[r]) (src[Cw[w,P₀],c]) (default : S)).mp ⟨c, rfl⟩
    obtain ⟨v, hv⟩ := ((Cnil[P₀]).exists_section_comp_domainSource_eq_iff
      (Y := Centers[r]) (src[Cw[w,P₀],c]) (default : S)).mpr (hU hc)
    have hn : (Cnil[P₀]).domainTarget (X := Centers[r]) (Y := Centers[r]) =
        (Cnil[P₀]).domainSource (X := Centers[r]) (Y := Centers[r]) := by
      apply Over.OverMorphism.ext
      simp only [Scheme.PartialMap.domainTarget_left, Scheme.PartialMap.domainSource_left,
        Path.centerPartialMap_hom, Path.centerIso_nil, Iso.refl_hom, Category.comp_id]
    simpa only [hn, hv] using models₀ v
  have hδ₁ := mem_orthogonal_total_boundary (M₁ a₁) (funext (hmark₁ a₁)) hnef₁ hsq₁
  have h := R.exponentEquiv_totalBoundaryExponent (w.centerPartialMap_hom (K := ℂ) P₀)
    hmark₀ hmark₁ hmodels₀ hmodels₁ hδ₁
  have hx := ref₁.totalBoundaryExponent_mem_chargeKernel Q₁ (funext (hmark₁ a₁)) hδ₁
  have hE := P₁.matrix_eq.symm.trans (congrArg₂ chargeExchangeMatrix hform₁ hcharge₁)
  have hmem : Q₁.totalBoundaryExponent d₁ ∈ E₁.matrix.mulVecLin.ker :=
    hE.symm ▸ ker_le_ker_chargeExchangeMatrix _ _ hx
  rw [w.xPullback_apply_monomial k ⟨_, hmem⟩, Path.coe_exchangeKernelEquiv_apply, h, hsign]
  have hpow (m : ℤ) (v : Fin r → ℤ) : mon[k,m • v] = (mon[k,v]) ^ m := by
    have hsmul : Finsupp.equivFunOnFinite.symm (m • v) = m • Finsupp.equivFunOnFinite.symm v :=
      (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin r)).symm.map_smul m v
    rw [hsmul, ofAdd_zsmul, map_zpow]
  simpa only [Units.smul_def, Units.val_pow_eq_pow_val] using
    hpow ((-1 : ℤˣ) ^ w.inversionCount : ℤ) (Q₀.totalBoundaryExponent d₀)

end GeometricRealization

end QPainleve.SignedClusterModularGroup
