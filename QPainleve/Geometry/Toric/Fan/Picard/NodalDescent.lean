/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Quotient
public import QPainleve.Geometry.Toric.Fan.Boundary.StrictTransform
public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import QPainleve.Geometry.Toric.Fan.Picard.StrictTransform

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
import QPainleve.Geometry.Toric.Fan.Smooth
import QPainleve.LinearAlgebra.Dual.Cokernel

/-!
# The Picard boundary quotient of a toric presentation

The boundary quotient of the original surface identifies with the cokernel of the
dual charge map. Pullback first compares the Picard groups modulo the prime divisors
supported in the boundary, using the isomorphism over the boundary complement.
On the ordered toric model those prime divisor classes are the strict ray classes.
The marked quotient then gives the charge presentation, as in Gross, Hacking and
Keel, *Birational geometry of cluster algebras*, proof of Theorem 5.5.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TopologicalSpace
open TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  (hΦ : Φ.IsRegular) (hdim : Module.finrank ℤ N = 2)
  (s : Fin n → Φ.Ray) (m : Fin n → N →+ ℤ)
  (hm : ∀ j, m j (s j).primitiveGenerator = 0) (hprim : ∀ j, Function.Surjective (m j))
  (c : Fin n → ℂˣ)

local notation "toricBoundary" => Φ.boundaryIdeal inferInstance

variable (J : Fin n →
  {K : (Φ.boundaryIdeal inferInstance).subscheme.IdealSheafData // K.IsEffectiveCartier})
  (hJ : ∀ j, (J j).val = ((s j).binomialCenterOnBoundary hdim (hm j) (hprim j) (c j)).ker)

local notation "model" => alongBoundary (subschemeι toricBoundary) J
local notation "internalTower" => WithBoundary.toTower (Sigma.snd model)
local notation "internalBoundary" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd model))
local notation "toricMap" => Φ.algebraicRealizationStructureMap
local notation "strictIdeal" ρ:arg => strictTransform (Φ.rayBoundaryIdeal hΦ ρ) internalTower

local notation "internalPoints" =>
  isClosedPointTower_alongBoundary_binomialCenters hdim s m hm hprim c J hJ

local notation "strictClass" => strictRayBoundaryClass hΦ hdim internalTower internalPoints

include hJ in
private theorem isEffectiveCartier_comap_center (j : Fin n) (ρ : Φ.Ray) :
    ((J j).val.comap (ρ.boundaryComponentι hΦ)).IsEffectiveCartier := by
  rw [hJ j]
  exact (s j).isEffectiveCartier_comap_ker_binomialCenterOnBoundary hΦ
    hdim (hm j) (hprim j) (c j) ρ

include hJ in
private theorem primeDivisorSpanCompl_internalBlowup
    [IsIntegral (model).1] [IsNoetherian (model).1]
    [∀ x : (model).1, UniqueFactorizationMonoid ((model).1.presheaf.stalk x)] :
    Scheme.Opens.primeDivisorSpanCompl (X := (model).1) (Closeds.compl (internalBoundary).support) =
      Submodule.span ℤ (Set.range strictClass) := by
  let : SmoothOfRelativeDimension 2 toricMap :=
    hdim ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  have hcenters := isEffectiveCartier_comap_center hΦ hdim s m hm hprim c J hJ
  let (ρ : Φ.Ray) : IsIntegral (strictIdeal ρ).subscheme :=
    isIntegral_strictTransform_rayBoundaryIdeal hΦ J ρ (fun j ↦ hcenters j ρ)
  let hCartier (ρ : Φ.Ray) : (strictIdeal ρ).IsEffectiveCartier :=
    (internalPoints).isEffectiveCartier_strictTransform toricMap
      (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ)
  let η (ρ : Φ.Ray) : CodimensionOnePoint (model).1 :=
    ⟨(strictIdeal ρ).subschemeι (genericPoint (strictIdeal ρ).subscheme),
      (hCartier ρ).coheight_subschemeι_genericPoint⟩
  have hcover : (↑(Closeds.compl (internalBoundary).support) : Set (model).1)ᶜ =
      ⋃ ρ, closure {(η ρ : (model).1)} := by
    rw [Closeds.coe_compl, compl_compl, support_ker_alongBoundary_boundaryι hΦ J hcenters]
    exact congrArg (fun S : Φ.Ray → Set (model).1 ↦ ⋃ ρ, S ρ)
      (funext fun ρ ↦ (strictIdeal ρ).support_eq_closure_subschemeι_genericPoint)
  rw [Scheme.Opens.primeDivisorSpanCompl_eq_span_of_iUnion_closure _ η hcover]
  congr 2
  funext ρ
  rw [strictRayBoundaryClass_eq hΦ hdim internalTower internalPoints ρ (hCartier ρ),
    LineBundleClass.primeDivisorClass_def, LineBundleClass.mk_toInvertibleSheaf_congr _ _
      (strictIdeal ρ).vanishingIdeal_closure_subschemeι_genericPoint]

variable {X Y : Scheme} [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
  {D : X.IdealSheafData} {f : X ⟶ Spec (.of ℂ)} {d : ℕ} {T : QPainleve.BlowupTower X d Y}
  (hT : IsNodalBoundaryTower D f (𝟙 X) T)
  (e : Y ≅ (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι J).1)
  (hD : ((D.comap T.toBase).comap e.inv).support =
    (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι J).2.boundaryι.ker.support)

local notation "boundaryCompl" => (Closeds.compl (Scheme.IdealSheafData.support D) : Scheme.Opens X)
local notation "modelToBase" => (Iso.inv e ≫ QPainleve.BlowupTower.toBase T)
local notation "binomialEquiv" =>
  binomialBoundaryQuotientEquivDualChargeCokernel hΦ hdim s m hm hprim c J hJ internalPoints

include hJ hT hD in
/-- In a toric presentation the Picard group of the original surface modulo its boundary
classes is the cokernel of the dual charge map. The two towers can be empty, and there
is no rank condition on the charge map. -/
def picardBoundaryQuotientEquivDualChargeCokernel :
    (Additive (LineBundleClass X) ⧸ Scheme.Opens.primeDivisorSpanCompl (X := X) boundaryCompl) ≃ₗ[ℤ]
      (Module.Dual ℤ (Fin n → ℤ) ⧸ (rayChargeMap s).dualMap.range) := by
  letI : SmoothOfRelativeDimension 2 toricMap :=
    hdim ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  letI : IsIntegral (model).1 := (internalPoints).isIntegral toricMap
  letI : IsNoetherian (model).1 := (internalTower).isNoetherian
  let fModel := (internalTower).toBase ≫ toricMap
  letI : SmoothOfRelativeDimension 2 fModel := (internalPoints).smoothOfRelativeDimension toricMap
  letI : ∀ x : (model).1, UniqueFactorizationMonoid ((model).1.presheaf.stalk x) :=
    fModel.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hTowerIso := hT.isIso_morphismRestrict_boundaryCompl
  rw [Scheme.IdealSheafData.comap_id] at hTowerIso
  haveI : IsIso (modelToBase ∣_ boundaryCompl) := by
    rw [morphismRestrict_comp]
    exact IsIso.comp_isIso' (inferInstance : IsIso (e.inv ∣_ T.toBase ⁻¹ᵁ boundaryCompl)) hTowerIso
  have hU : modelToBase ⁻¹ᵁ boundaryCompl = Closeds.compl (internalBoundary).support := by
    rw [← compl_support_comap, Scheme.IdealSheafData.comap_comp, hD]
  have hspan : (modelToBase ⁻¹ᵁ boundaryCompl).primeDivisorSpanCompl =
      Submodule.span ℤ (Set.range strictClass) := by
    rw [hU, primeDivisorSpanCompl_internalBlowup hΦ hdim s m hm hprim c J hJ]
  exact (Scheme.Hom.quotientPrimeDivisorSpanComplEquiv modelToBase boundaryCompl).trans
    ((Submodule.quotEquivOfEq _ _ hspan).trans binomialEquiv)

/-- The comparison evaluates a representative by pulling it back to the toric blowup
model and applying the comparison in the ordered marking. -/
@[simp] theorem picardBoundaryQuotientEquivDualChargeCokernel_apply_mk (a : LineBundleClass X) :
    picardBoundaryQuotientEquivDualChargeCokernel hΦ hdim s m hm hprim c J hJ hT e hD
      (Submodule.Quotient.mk (Additive.ofMul a)) =
    binomialEquiv
      (Submodule.Quotient.mk (Additive.ofMul (LineBundleClass.pullback modelToBase a))) := by
  simp only [picardBoundaryQuotientEquivDualChargeCokernel, LinearEquiv.trans_apply,
    Scheme.Hom.quotientPrimeDivisorSpanComplEquiv_mk, Submodule.quotEquivOfEq_mk]

include hΦ hJ hT hD in
/-- When the charges span the ambient lattice rationally, the charge index is the
order of the torsion subgroup of the original surface's Picard boundary quotient. -/
theorem natCard_torsion_picardBoundaryQuotient_eq_chargeIndex
    (h : Module.finrank ℤ (rayChargeMap s).range = Module.finrank ℤ N) :
    Nat.card (AddCommGroup.torsion (Additive (LineBundleClass X) ⧸
      Scheme.Opens.primeDivisorSpanCompl (X := X) boundaryCompl)) =
        (rayChargeMap s).range.toAddSubgroup.index := by
  have := Φ.lattice.free
  have := Φ.lattice.finite
  let q := picardBoundaryQuotientEquivDualChargeCokernel hΦ hdim s m hm hprim c J hJ hT e hD
  let eqv := q.toAddEquiv
  let torsionEquiv := (eqv.addSubgroupMap (AddCommGroup.torsion _)).trans
    (AddEquiv.addSubgroupCongr eqv.map_torsion)
  exact (Nat.card_congr torsionEquiv.toEquiv).trans
    ((rayChargeMap s).natCard_torsion_coker_dualMap_of_finrank_range_eq h)

end TauCeti.Toric.Fan
