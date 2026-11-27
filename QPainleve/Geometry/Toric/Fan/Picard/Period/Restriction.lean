/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Picard
public import QPainleve.Geometry.Toric.Fan.Picard.Orthogonal

/-!
# Boundary restriction of toric charge classes

The inverse charge comparison represents a line bundle on the original surface.
Pulling its restriction back to the fixed toric boundary gives the restriction of
the toric part tensored with the center ideals to the powers given by the charge relation.
The toric part is determined by the charge relation and the fan, so it cancels when
comparing two choices of center parameters.

This gives the restriction calculation behind the period formula in Gross, Hacking
and Keel, *Moduli of surfaces with an anti-canonical cycle*, Proposition 2.9.
The coordinates come from `exists_picardBoundaryOrthogonalEquivChargeKernel_symm_marking`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable (K : Type) [Field K] [IsAlgClosed K]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}

local notation "Dtor" => Φ.toricBoundaryIdeal K inferInstance
local notation "Pic(" S ")" => Additive (LineBundleClass S)

section Presentation

variable {X Y : Scheme} {D : X.IdealSheafData} {d : ℕ} {T : QPainleve.BlowupTower X d Y}
  (J : Fin n →
    {I : (Φ.toricBoundaryIdeal K inferInstance).subscheme.IdealSheafData // I.IsEffectiveCartier})
  (e : Y ≅ (alongBoundary (Φ.toricBoundaryIdeal K inferInstance).subschemeι J).1)

local notation "model" => alongBoundary (subschemeι Dtor) J
local notation "boundaryι" => WithBoundary.boundaryι (Sigma.snd model)

variable (hD : ((D.comap T.toBase).comap e.inv).support =
  (alongBoundary (Φ.toricBoundaryIdeal K inferInstance).subschemeι J).2.boundaryι.ker.support)

omit [IsAlgClosed K] in
/-- In a toric presentation, the projection from the internal blowup model to the
original surface maps the fixed reduced toric boundary into the original boundary. -/
def toricBoundaryToBase : (Dtor).subscheme ⟶ D.subscheme :=
  IsClosedImmersion.lift D.subschemeι (boundaryι ≫ e.inv ≫ T.toBase) (by
    have : IsReduced (Dtor).subscheme := by
      rw [Φ.toricBoundaryIdeal_def K]
      infer_instance
    rw [ker_subschemeι]
    refine (le_support_iff_le_vanishingIdeal.mp le_rfl).trans
      (vanishingIdeal_le_ker_of_range_subset _ ?_)
    rintro _ ⟨y, rfl⟩
    have hy : boundaryι y ∈ ((boundaryι).ker.support : Set (model).1) := by
      rw [(boundaryι).support_ker]
      exact subset_closure (Set.mem_range_self y)
    simpa only [← hD, support_comap, Closeds.coe_preimage, Set.mem_preimage,
      Scheme.Hom.comp_apply] using hy)

omit [IsAlgClosed K] in
/-- The map on boundaries commutes with their embeddings in the two surfaces. -/
@[reassoc (attr := simp)]
theorem toricBoundaryToBase_comp_subschemeι :
    toricBoundaryToBase K J e hD ≫ D.subschemeι = boundaryι ≫ e.inv ≫ T.toBase :=
  IsClosedImmersion.lift_fac _ _ _

omit [IsAlgClosed K] in
/-- The toric boundary projection is over any base for which the presentation
identification commutes with the two projections to that base. -/
theorem isOver_toricBoundaryToBase {X Y Z : Scheme} [X.Over Z]
    [(Φ.finiteFanScheme K).Over Z]
    {D : X.IdealSheafData} {d : ℕ} {T : QPainleve.BlowupTower X d Y}
    (J : Fin n → {I : (Dtor).subscheme.IdealSheafData // I.IsEffectiveCartier})
    (e : Y ≅ (alongBoundary (subschemeι Dtor) J).1)
    (he : e.inv ≫ T.toBase ≫ (X ↘ Z) =
      (alongBoundary (subschemeι Dtor) J).2.toTower.toBase ≫ ((Φ.finiteFanScheme K) ↘ Z))
    (hD : ((D.comap T.toBase).comap e.inv).support =
      (alongBoundary (subschemeι Dtor) J).2.boundaryι.ker.support) :
    (toricBoundaryToBase K J e hD).IsOver Z := by
  constructor
  rw [D.over_eq_subschemeι_comp, toricBoundaryToBase_comp_subschemeι_assoc, he,
    WithBoundary.boundaryι_toBase_assoc, ← (Dtor).over_eq_subschemeι_comp]

local notation "Z" => (Φ.finiteFanScheme K)

variable [(Φ.finiteFanScheme K).IsProjectiveOver K]
  (hΦ : Φ.IsRegular) (hdim : Module.finrank ℤ N = 2)
  (s : Fin n → Φ.Ray) (m : Fin n → N →+ ℤ)
  (hm : ∀ j, m j (s j).primitiveGenerator = 0) (hprim : ∀ j, Function.Surjective (m j))
  (c : Fin n → Kˣ)
  (hJ : ∀ j, (J j).val = ((s j).binomialCenterOnBoundary K hdim (hm j) (hprim j) (c j)).ker)
  [X.Over (Spec (.of K))] [X.IsProjectiveOver K] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of K))]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm K X)]
  (hT : IsNodalBoundaryTower D (X ↘ Spec (.of K)) (𝟙 X) T)
  (he : e.inv ≫ T.toBase ≫ (X ↘ Spec (.of K)) =
    (alongBoundary (Φ.toricBoundaryIdeal K inferInstance).subschemeι J).2.toTower.toBase ≫
      ((Φ.finiteFanScheme K) ↘ Spec (.of K)))

local notation "chargeEquiv" =>
  picardBoundaryOrthogonalEquivChargeKernel K hΦ hdim s m hm hprim c J hJ hT e he hD

include hJ hT he hD in
/-- A charge relation `x` gives a boundary restriction on the original surface.
After pullback to the fixed toric boundary, it is the toric part of the marking
restricted to that boundary, tensored with each center ideal line bundle to the
power `x j`. The toric part `H` is specified by its degrees on the ray divisors. -/
theorem pullback_toricBoundaryToBase_picardBoundaryOrthogonalEquivChargeKernel_symm
    (x : (rayChargeMap s).ker) (H : Pic(Z))
    (hH : ∀ v : Φ.Ray → ℤ, Chow.classIntersectionNumber K Z
        (Φ.rayChartDivisorToPicard K hΦ v).toMul H.toMul = ∑ j, v (s j) * (x : Fin n → ℤ) j) :
    pullback (toricBoundaryToBase K J e hD)
      (pullback D.subschemeι ((chargeEquiv).symm x).val.toMul) =
      pullback (subschemeι Dtor) H.toMul *
        ∏ j, (LineBundleClass.mk (J j).property.toInvertibleSheaf) ^ ((x : Fin n → ℤ) j) := by
  obtain ⟨G, hMarking, hDegree⟩ :=
    exists_picardBoundaryOrthogonalEquivChargeKernel_symm_marking K
      hΦ hdim s m hm hprim c J hJ hT e he hD x
  have hEq := (hDegree H).mp hH
  subst G
  rw [pullback_comp, toricBoundaryToBase_comp_subschemeι, ← pullback_comp, ← hMarking,
    pullback_picardHom_alongBoundary]
  simp only [Pi.neg_apply, neg_neg]

end Presentation

section CenterRatio

variable (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "ChargeKernel" => LinearMap.ker (rayChargeMap s)
local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "m" =>
  (fun j ↦ LinearMap.toAddMonoidHom (Module.Basis.detDualEquiv b (Ray.primitiveGenerator (s j))))
local notation "hm" => (fun j ↦ Module.Basis.detDualEquiv_self b (Ray.primitiveGenerator (s j)))
local notation "hprim" => (fun j ↦ Ray.surjective_detCharacter (s j) b)
local notation "J[" c "]" => (fun j ↦ Ray.internalCenter K b (s j) (c j))
local notation "hJ[" c "]" => (fun j ↦ Ray.internalCenter_val K b (s j) (c j))

variable [(Φ.finiteFanScheme K).IsProjectiveOver K]
  {c₀ c₁ : Fin n → Kˣ}
  {X₀ X₁ Y₀ Y₁ : Scheme}
  [X₀.Over (Spec (.of K))] [X₀.IsProjectiveOver K] [IsIntegral X₀]
  [SmoothOfRelativeDimension 2 (X₀ ↘ Spec (.of K))]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm K X₀)]
  [X₁.Over (Spec (.of K))] [X₁.IsProjectiveOver K] [IsIntegral X₁]
  [SmoothOfRelativeDimension 2 (X₁ ↘ Spec (.of K))]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm K X₁)]
  {D₀ : X₀.IdealSheafData} {D₁ : X₁.IdealSheafData}
  {d₀ d₁ : ℕ} {T₀ : QPainleve.BlowupTower X₀ d₀ Y₀} {T₁ : QPainleve.BlowupTower X₁ d₁ Y₁}
  (hT₀ : IsNodalBoundaryTower D₀ (X₀ ↘ Spec (.of K)) (𝟙 X₀) T₀)
  (hT₁ : IsNodalBoundaryTower D₁ (X₁ ↘ Spec (.of K)) (𝟙 X₁) T₁)
  (e₀ : Y₀ ≅ (alongBoundary (Φ.toricBoundaryIdeal K inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter K b (c₀ j))).1)
  (e₁ : Y₁ ≅ (alongBoundary (Φ.toricBoundaryIdeal K inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter K b (c₁ j))).1)
  (he₀ : e₀.inv ≫ T₀.toBase ≫ (X₀ ↘ Spec (.of K)) =
    (alongBoundary (Φ.toricBoundaryIdeal K inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter K b (c₀ j))).2.toTower.toBase ≫
      ((Φ.finiteFanScheme K) ↘ Spec (.of K)))
  (he₁ : e₁.inv ≫ T₁.toBase ≫ (X₁ ↘ Spec (.of K)) =
    (alongBoundary (Φ.toricBoundaryIdeal K inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter K b (c₁ j))).2.toTower.toBase ≫
      ((Φ.finiteFanScheme K) ↘ Spec (.of K)))
  (hD₀ : ((D₀.comap T₀.toBase).comap e₀.inv).support =
    (alongBoundary (Φ.toricBoundaryIdeal K inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter K b (c₀ j))).2.boundaryι.ker.support)
  (hD₁ : ((D₁.comap T₁.toBase).comap e₁.inv).support =
    (alongBoundary (Φ.toricBoundaryIdeal K inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter K b (c₁ j))).2.boundaryι.ker.support)

local notation "g₀" => toricBoundaryToBase K (J[c₀]) e₀ hD₀
local notation "g₁" => toricBoundaryToBase K (J[c₁]) e₁ hD₁
local notation "charge₀" =>
  picardBoundaryOrthogonalEquivChargeKernel K hΦ rankTwo s m hm hprim c₀ (J[c₀]) (hJ[c₀])
    hT₀ e₀ he₀ hD₀
local notation "charge₁" =>
  picardBoundaryOrthogonalEquivChargeKernel K hΦ rankTwo s m hm hprim c₁ (J[c₁]) (hJ[c₁])
    hT₁ e₁ he₁ hD₁

include hT₀ he₀ hD₀ hT₁ he₁ hD₁ in
/-- The quotient of two marked restrictions, pulled back to the same toric boundary,
is the product of the center ideal quotients with exponents given by the charge relation. -/
theorem pullback_toricBoundaryToBase_markedCharge_div (x : ChargeKernel) :
    let I (u : Fin n → Kˣ) (j : Fin n) :=
      LineBundleClass.mk ((s j).internalCenter K b (u j)).property.toInvertibleSheaf
    pullback g₀ (pullback D₀.subschemeι ((charge₀).symm x).val.toMul) /
      pullback g₁ (pullback D₁.subschemeι ((charge₁).symm x).val.toMul) =
        (∏ j, I c₀ j ^ (x : Fin n → ℤ) j) / (∏ j, I c₁ j ^ (x : Fin n → ℤ) j) := by
  dsimp only
  obtain ⟨H, -, hH⟩ := exists_picardBoundaryOrthogonalEquivChargeKernel_symm_marking K
    hΦ rankTwo s m hm hprim c₀ (J[c₀]) (hJ[c₀]) hT₀ e₀ he₀ hD₀ x
  have hdegree := (hH H).mpr rfl
  rw [pullback_toricBoundaryToBase_picardBoundaryOrthogonalEquivChargeKernel_symm K
    (J[c₀]) e₀ hD₀ hΦ rankTwo s m hm hprim c₀ (hJ[c₀]) hT₀ he₀ x H hdegree,
    pullback_toricBoundaryToBase_picardBoundaryOrthogonalEquivChargeKernel_symm K
      (J[c₁]) e₁ hD₁ hΦ rankTwo s m hm hprim c₁ (hJ[c₁]) hT₁ he₁ x H hdegree,
    mul_div_mul_left_eq_div]

end CenterRatio

end TauCeti.Toric.Fan
