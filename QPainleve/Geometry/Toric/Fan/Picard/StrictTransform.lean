/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
public import QPainleve.Geometry.Toric.Fan.Boundary.Component
public import QPainleve.Geometry.Toric.Fan.Boundary.NumberedPrime
public import QPainleve.Geometry.Toric.Fan.Boundary.Prime
public import QPainleve.Geometry.Toric.Fan.Picard.BoundaryQuotient
public import QPainleve.Geometry.Toric.BaseChange.Fan

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Boundary.StrictTransform
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Picard classes of the strict boundary in an internal toric blowup tower

The strict transform of a ray component has its original toric divisor class and an
exceptional coefficient of `-1` for each center on that ray. This identifies the
Picard quotient by the actual strict-transform boundary classes with the cokernel of
the dual charge map. The centers are ordered and may repeat, in which case the
associated blowups use the successive strict transforms of the boundary. Along a boundary
identification, the strict ray classes are the pullbacks of the corresponding boundary prime
classes, including those given by a nodal cycle numbering.

The boundary marking is the calculation used in the proof of Gross, Hacking and Keel,
*Birational geometry of cluster algebras*, Theorem 5.5. The comparison uses
`boundaryQuotientEquivDualChargeCokernel` for charges of arbitrary rank.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

universe u

variable (k : Type u) [Field k] [PerfectField k] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]

section Marking

variable {n : ℕ} (hΦ : Φ.IsRegular) (hdim : Module.finrank ℤ N = 2)
  (s : Fin n → Φ.Ray) (m : Fin n → N →+ ℤ)
  (hm : ∀ j, m j (s j).primitiveGenerator = 0) (hprim : ∀ j, Function.Surjective (m j))
  (c : Fin n → kˣ)

local notation "b" => subschemeι (Φ.toricBoundaryIdeal k inferInstance)
local notation "f" => Φ.finiteFanSchemeToSpec k
local notation "Pic" Y => Additive (LineBundleClass Y)
local notation "C" j:arg => Ray.binomialCenterOnBoundary (s j) k hdim (hm j) (hprim j) (c j)
local notation "p" j:arg => (C j) (IsLocalRing.closedPoint k : Spec (CommRingCat.of k))

omit [Nonempty Φ.cones] [PerfectField k] in
include hΦ hdim in
private theorem smoothOfRelativeDimension_two : SmoothOfRelativeDimension 2 f :=
  hdim ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ

/-- The Picard class of the actual scheme-theoretic strict transform of a ray boundary divisor
in a closed-point tower over the regular toric surface. -/
def strictRayBoundaryClass {Y : Scheme.{u}} (T : BlowupTower (Φ.finiteFanScheme k) n Y)
    (hT : IsClosedPointTower (Φ.finiteFanScheme k) T) (ρ : Φ.Ray) : Pic Y :=
  let := smoothOfRelativeDimension_two k hΦ hdim
  Additive.ofMul (LineBundleClass.mk (hT.isEffectiveCartier_strictTransform f
    (Φ.isEffectiveCartier_rayDivisorIdeal k hΦ ρ)).toInvertibleSheaf)⁻¹

/-- The strict boundary class is the inverse of the class of its Cartier ideal. -/
theorem strictRayBoundaryClass_eq {Y : Scheme.{u}} (T : BlowupTower (Φ.finiteFanScheme k) n Y)
    (hT : IsClosedPointTower (Φ.finiteFanScheme k) T) (ρ : Φ.Ray)
    (hD : (T.strictTransform (Φ.rayDivisorIdeal k hΦ ρ)).IsEffectiveCartier) :
    strictRayBoundaryClass k hΦ hdim T hT ρ =
      Additive.ofMul (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ := (rfl)

variable (J : Fin n → {I : (Φ.toricBoundaryIdeal k inferInstance).subscheme.IdealSheafData //
  I.IsEffectiveCartier})
  (hJ : ∀ j, (J j).val = ((s j).binomialCenterOnBoundary k hdim (hm j) (hprim j) (c j)).ker)

local notation "tower" => alongBoundary b J
local notation "T" => WithBoundary.toTower (Sigma.snd tower)

variable (hT : IsClosedPointTower (Φ.finiteFanScheme k)
  (alongBoundary (Φ.toricBoundaryIdeal k inferInstance).subschemeι J).2.toTower)

include hJ in
private theorem strictTransformCoefficients_rayBoundaryIdeal [DecidableEq Φ.Ray] (ρ : Φ.Ray) :
    (hT).strictTransformCoefficients (Φ.rayDivisorIdeal k hΦ ρ) =
      fun j ↦ if s j = ρ then -1 else 0 := by
  let : ∀ j : Fin n, Decidable (p j ∈ Set.range (ρ.boundaryComponentι k hΦ)) :=
    fun _ ↦ Classical.propDecidable _
  let := smoothOfRelativeDimension_two k hΦ hdim
  obtain h := strictTransformCoefficients_alongBoundary b (ρ.boundaryComponentι k hΦ) f
    J (fun j ↦ p j)
    (fun j ↦ by
      have hsingle : Set.range (C j) = {p j} :=
        Set.range_eq_singleton fun q ↦ congrArg (C j) (Subsingleton.elim q _)
      rw [← hsingle]
      exact (C j).isClosedEmbedding.isClosed_range)
    (fun j ↦ (hJ j).trans (C j).ker_eq_ker_fromSpecResidueField)
    (fun j ↦ by
      rw [hJ j]
      exact (s j).isEffectiveCartier_comap_ker_binomialCenterOnBoundary k hΦ hdim
        (hm j) (hprim j) (c j) ρ)
    (fun j ↦ (s j).isRegularLocalRing_stalk_of_boundaryComponentι_eq_binomialCenter k hΦ hdim
      (hm j) (hprim j) (c j) ρ)
    (by simpa only [Ray.boundaryComponentι_subschemeι, ker_subschemeι] using
      Φ.isEffectiveCartier_rayDivisorIdeal k hΦ ρ)
    (hT)
  simp only [Ray.boundaryComponentι_subschemeι, ker_subschemeι] at h
  refine h.trans ?_
  funext j
  have hmem := (s j).binomialCenterOnBoundary_mem_range_boundaryComponentι_iff k hΦ hdim
    (hm j) (hprim j) (c j) ρ
  by_cases hs : s j = ρ
  · simp only [ite_eq_left hs,
      ite_eq_left (hmem.mpr hs)]
  · simp only [ite_eq_right hs,
      ite_eq_right (hmem.not.mpr hs)]

include hJ in
/-- The coordinate vector of a marked boundary generator maps to the strict transform of its
ray component, even if several centers on that ray coincide on the initial toric surface. -/
theorem picardHom_markedBoundaryMap_single [DecidableEq Φ.Ray] (ρ : Φ.Ray) :
    (T).picardHom (markedBoundaryMap k hΦ s (Pi.single ρ 1)) =
      strictRayBoundaryClass k hΦ hdim (T) (hT) ρ := by
  let := smoothOfRelativeDimension_two k hΦ hdim
  have := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := k) hΦ
  have h := (hT).picardMarking_strictTransform f (Φ.isEffectiveCartier_rayDivisorIdeal k hΦ ρ)
  rw [strictTransformCoefficients_rayBoundaryIdeal k hΦ hdim s m hm hprim c J hJ hT ρ] at h
  have hbase : LineBundleClass.primeDivisorClass (Φ.rayBoundaryChartPoint (R := k) hΦ ρ) =
      (LineBundleClass.mk (Φ.isEffectiveCartier_rayDivisorIdeal k hΦ ρ).toInvertibleSheaf)⁻¹ := by
    rw [LineBundleClass.primeDivisorClass_def, LineBundleClass.mk_toInvertibleSheaf_congr _ _
      (Φ.rayDivisorIdeal_def k hΦ ρ).symm]
  rw [strictRayBoundaryClass_eq k hΦ hdim (T) (hT) ρ
    ((hT).isEffectiveCartier_strictTransform f (Φ.isEffectiveCartier_rayDivisorIdeal k hΦ ρ))]
  simpa only [picardMarking_apply, markedBoundaryMap_apply,
    rayChartDivisorToPicard_single, one_zsmul, Pi.single_apply, apply_ite, neg_zero, hbase]
    using h

include hJ in
/-- The ordered Picard marking sends the marked boundary span to the span of the actual
strict-transform ray classes. -/
theorem map_range_markedBoundaryMap_picardHom :
    (markedBoundaryMap k hΦ s).range.map (T).picardHom =
      Submodule.span ℤ (Set.range (strictRayBoundaryClass k hΦ hdim (T) (hT))) := by
  classical
  rw [range_markedBoundaryMap_eq_span, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext ρ
  simpa only [Function.comp_apply, markedBoundaryMap_apply, Pi.single_apply, apply_ite,
    neg_zero] using picardHom_markedBoundaryMap_single k hΦ hdim s m hm hprim c J hJ hT ρ

include hJ in
/-- In the surface obtained by blowing up the ordered binomial centers, the Picard group
modulo the strict-transform ray classes is the cokernel of the dual of the charge map.
The charges may have any rank. -/
def binomialBoundaryQuotientEquivDualChargeCokernel :
    ((Pic (Sigma.fst tower)) ⧸ Submodule.span ℤ
      (Set.range (strictRayBoundaryClass k hΦ hdim (T) (hT)))) ≃ₗ[ℤ]
      (Module.Dual ℤ (Fin n → ℤ) ⧸ (rayChargeMap s).dualMap.range) := by
  letI := smoothOfRelativeDimension_two k hΦ hdim
  let e := (T).picardMarking (hT) f
  have he : e.toLinearMap = (T).picardHom :=
    LinearMap.ext fun a ↦ picardMarking_apply (T) (hT) f a
  have hspan := map_range_markedBoundaryMap_picardHom k hΦ hdim s m hm hprim c J hJ hT
  exact (Submodule.Quotient.equiv _ _ e (he.symm ▸ hspan)).symm.trans
    (boundaryQuotientEquivDualChargeCokernel k hΦ s)

/-- The inverse cokernel comparison sends a dual functional to the corresponding class
supported in the total exceptional coordinates. -/
@[simp]
theorem binomialBoundaryQuotientEquivDualChargeCokernel_symm_apply_mk
    (φ : Module.Dual ℤ (Fin n → ℤ)) :
    (binomialBoundaryQuotientEquivDualChargeCokernel k hΦ hdim s m hm hprim c J hJ hT).symm
      (Submodule.Quotient.mk φ) =
      Submodule.Quotient.mk ((T).picardHom (0, fun j ↦ φ (Pi.single j 1))) := by
  simp only [binomialBoundaryQuotientEquivDualChargeCokernel, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, boundaryQuotientEquivDualChargeCokernel_symm_apply_mk,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe, picardMarking_apply]

end Marking

section OrderedModel

variable {n : ℕ} (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

open TopologicalSpace LineBundleClass

local notation "S" => Spec (CommRingCat.of k)
local notation "Z" => (Φ.finiteFanScheme k)
local notation "d₂" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "m" => (fun j ↦ LinearMap.toAddMonoidHom
  (b.detDualEquiv (Ray.primitiveGenerator (s j))))
local notation "hm" => (fun j ↦ b.detDualEquiv_self (Ray.primitiveGenerator (s j)))
local notation "hprim" => (fun j ↦ Ray.surjective_detCharacter (s j) b)
local notation "Model" =>
  (Σ Y, WithBoundary (subschemeι (Φ.toricBoundaryIdeal k inferInstance)) n Y)
local notation "model" c => internalBlowupTower k b s c
local notation "U" c => WithBoundary.toTower (Sigma.snd (model c))
local notation "hU" c => isClosedPointTower_internalBlowupTower k b s c
local notation "fZ" => ((Φ.finiteFanScheme k) ↘ S)
local notation "prime(" x ")" => (Subtype.mk (Subtype.val x)
  (And.right (mem_boundaryPrimes.mp (Subtype.property x))) : CodimensionOnePoint _)
local notation "cl" ρ:arg => markedBoundaryMap k hΦ s (Pi.single ρ 1)

/-- The strict ray class has exceptional coefficient `-1` at every center on the ray
and zero at the other centers, including in an ordered tower with repeated centers. -/
theorem picardHom_markedBoundaryMap_single_internalBlowupTower [DecidableEq Φ.Ray]
    (c : Fin n → kˣ) (ρ : Φ.Ray) :
    (U c).picardHom (cl ρ) = strictRayBoundaryClass k hΦ d₂ (U c) (hU c) ρ := by
  let Marked (M : Model) := ∀ hM : IsClosedPointTower Z M.2.toTower,
    M.2.toTower.picardHom (cl ρ) = strictRayBoundaryClass k hΦ d₂ _ hM ρ
  have hmark : Marked (model c) := by
    rw [internalBlowupTower_eq_alongBoundary]
    intro hM
    exact picardHom_markedBoundaryMap_single k hΦ d₂ s m hm hprim c _
      (fun j ↦ (s j).internalCenter_val k b (c j)) hM ρ
  exact hmark (hU c)

/-- In the ordered Picard marking the actual boundary prime over a ray has the
fixed strict ray class. -/
theorem picardHom_markedBoundaryMap_single_eq_primeDivisorClass [DecidableEq Φ.Ray]
    (c : Fin n → kˣ) (ρ : Φ.Ray) :
    let : IsIntegral (model c).1 := isIntegral_internalBlowupTower k b s c hΦ
    let : IsNoetherian (model c).1 := (U c).isNoetherian
    let : SmoothOfRelativeDimension 2 fZ :=
      d₂ ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ
    let : SmoothOfRelativeDimension 2 ((U c).toBase ≫ fZ) :=
      (hU c).smoothOfRelativeDimension fZ
    let := ((U c).toBase ≫ fZ).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (U c).picardHom (cl ρ) = Additive.ofMul
      (primeDivisorClass (prime(internalBlowupBoundaryPrimeEquiv k hΦ b s c ρ))) := by
  intro _ _ _ _ _
  let j := ρ.boundaryComponentι k hΦ ≫ (model c).2.boundaryι
  have hI := ker_boundaryComponentι_internalBlowupTower k b s c hΦ ρ
  have hs := range_rayComponent_internalBlowupBoundaryPrimeEquiv k hΦ b s c ρ
  let x := (internalBlowupBoundaryPrimeEquiv k hΦ b s c ρ).val
  have hker : j.ker = vanishingIdeal ⟨closure {x}, isClosed_closure⟩ := by
    rw [j.ker_eq_vanishingIdeal_support]
    congr 1
    exact SetLike.coe_injective ((j.support_ker.trans
      j.isClosedEmbedding.isClosed_range.closure_eq).trans hs)
  have heff := (hU c).isEffectiveCartier_strictTransform fZ
    (Φ.isEffectiveCartier_rayDivisorIdeal k hΦ ρ)
  rw [picardHom_markedBoundaryMap_single_internalBlowupTower k hΦ b s c ρ,
    strictRayBoundaryClass_eq k _ _ _ _ _ heff, primeDivisorClass_def,
    mk_toInvertibleSheaf_congr _ _ (hI.symm.trans hker)]

end OrderedModel

section BoundaryClasses

variable {Y : Scheme.{u}} {n : ℕ} (b : Module.Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular)
  (s : Fin n → Φ.Ray) (c : Fin n → kˣ)

local notation "S" => Spec (CommRingCat.of k)
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "M" => internalBlowupTower k b s c
local notation "J" => WithBoundary.toTower (Sigma.snd M)
local notation "hJ" => isClosedPointTower_internalBlowupTower k b s c
local notation "ι" => WithBoundary.boundaryι (Sigma.snd M)
local notation "f" => (Φ.finiteFanScheme k) ↘ S

open LineBundleClass

/-- Pullback of a transported boundary prime class along the model isomorphism gives
the strict class of the same ray. -/
theorem pullback_primeDivisorClass_internalBlowupBoundaryPrimeEquivOfIso
    [IsLocallyNoetherian Y] [∀ y : Y, IsDomain (Y.presheaf.stalk y)]
    [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]
    {D : Y.IdealSheafData} (e : M.1 ≅ Y) (hs : (D.comap e.hom).support = (ι).ker.support)
    (ρ : Φ.Ray) :
    Additive.ofMul (pullback e.hom (primeDivisorClass (D.boundaryPrimeEmbedding
      (internalBlowupBoundaryPrimeEquivOfIso k hΦ b s c e hs ρ)))) =
      strictRayBoundaryClass k hΦ rankTwo J hJ ρ := by
  classical
  let : IsIntegral M.1 := isIntegral_internalBlowupTower k b s c hΦ
  let : IsNoetherian M.1 := (J).isNoetherian
  let : SmoothOfRelativeDimension 2 f :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ
  let : SmoothOfRelativeDimension 2 ((J).toBase ≫ f) := (hJ).smoothOfRelativeDimension f
  let := ((J).toBase ≫ f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let α := internalBlowupBoundaryPrimeEquiv k hΦ b s c
  have hp : CodimensionOnePoint.mapOfIsOpenImmersion e.hom
      ((ι).ker.boundaryPrimeEmbedding (α ρ)) =
        D.boundaryPrimeEmbedding (internalBlowupBoundaryPrimeEquivOfIso k hΦ b s c e hs ρ) := by
    apply Subtype.ext
    simp [α]
  rw [← hp, pullback_primeDivisorClass_mapOfIsOpenImmersion,
    ← picardHom_markedBoundaryMap_single_internalBlowupTower k hΦ b s c ρ]
  have hα : (ι).ker.boundaryPrimeEmbedding (α ρ) =
      ⟨(α ρ).val, (mem_boundaryPrimes.mp (α ρ).property).2⟩ :=
    Subtype.ext (coe_boundaryPrimeEmbedding _ _)
  rw [hα]
  exact (picardHom_markedBoundaryMap_single_eq_primeDivisorClass k hΦ b s c ρ).symm

local notation "Dtor" => Φ.toricBoundaryIdeal k inferInstance

variable [IsSepClosed k] in
/-- If the boundary identification sends the component of a ray to a numbered
component, the numbered Picard class pulls back to that ray's strict class.
The component matching uses the actual boundary isomorphism. -/
theorem pullback_numbered_boundaryPrime_eq_strictRayBoundaryClass
    [IsLocallyNoetherian Y] [∀ y : Y, IsDomain (Y.presheaf.stalk y)]
    [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]
    {D : Y.IdealSheafData} [Scheme.Over D.subscheme S] [PrestableFamily (D.subscheme ↘ S)]
    [PrestableFamily ((Dtor).subscheme ↘ S)]
    {m l : ℕ} [NeZero m] [NeZero l] {γ δ : Type*}
    {p : γ → ((Dtor).subscheme ↘ S).smoothLocus} {q : δ → (D.subscheme ↘ S).smoothLocus}
    (C : Scheme.NodalCycleNumbering (k := k) (X := (Dtor).subscheme) p m)
    (A : Scheme.NodalCycleNumbering (k := k) (X := D.subscheme) q l)
    (hD : D.IsEffectiveCartier) (e : M.1 ≅ Y)
    (eB : (Dtor).subscheme ≅ D.subscheme) (heB : eB.hom ≫ D.subschemeι = (ι) ≫ e.hom)
    (ρ : Φ.Ray) (j : ZMod m) (j' : ZMod l)
    (hρ : C.component j = Φ.boundaryNormalizationComponentEquiv k hΦ ρ)
    (hj : eB.hom (C.componentGenericPoint j) = A.componentGenericPoint j') :
    Additive.ofMul (pullback e.hom (primeDivisorClass (D.boundaryPrimeEmbedding
      (A.boundaryPrimeEquiv hD j')))) = strictRayBoundaryClass k hΦ rankTwo J hJ ρ := by
  have he : D.comap e.hom = (ι).ker := by
    have hk : ((ι) ≫ e.hom).ker = D := by
      rw [← heB, Scheme.Hom.ker_comp_of_isIso, D.ker_subschemeι]
    rw [← hk, Scheme.Hom.comap_ker_comp_of_isClosedImmersion]
  have hpoint : (internalBlowupBoundaryPrimeEquiv k hΦ b s c ρ).val =
      (ι) (C.componentGenericPoint j) := by
    rw [internalBlowupBoundaryPrime_val, Scheme.NodalCycleNumbering.componentGenericPoint_def, hρ]
  have hs := congrArg Scheme.IdealSheafData.support he
  have hPrime : internalBlowupBoundaryPrimeEquivOfIso k hΦ b s c e hs ρ =
      A.boundaryPrimeEquiv hD j' := by
    apply Subtype.ext
    rw [internalBlowupBoundaryPrimeEquivOfIso_apply_val, hpoint, ← Scheme.Hom.comp_apply,
      ← heB, Scheme.Hom.comp_apply, hj, A.boundaryPrimeEquiv_apply_val]
  rw [← hPrime]
  exact pullback_primeDivisorClass_internalBlowupBoundaryPrimeEquivOfIso k b hΦ s c e hs ρ

end BoundaryClasses

end TauCeti.Toric.Fan
