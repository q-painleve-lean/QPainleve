/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import QPainleve.LinearAlgebra.IntegralLattice.IsotropicQuotient
public import QPainleve.SignedClusterModularGroup.BoundaryCycle
public import QPainleve.SignedClusterModularGroup.RadicalQuotient
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Index
import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Naturality

/-!
# Saturation of a boundary cycle

The inclusion of the boundary span into the orthogonal complement of its total class induces
a rational isometric embedding on the radical quotients. The inverse image of the larger
integral carrier is the saturation of the boundary quotient. This realizes the saturation
as a type-A integral overlattice after reversing the sign of the form. Its quotient by
the boundary lattice is the torsion of the original ambient quotient.

The construction uses Tau Ceti's `radicalQuotient` and `IntermediateCarrier` and the
isometry that identifies the boundary radical quotient with the negative type-A lattice.
-/

public noncomputable section

open LinearMap Submodule TauCeti.IntegralLattice
open scoped TensorProduct

namespace QPainleve.BoundaryCycle

variable {n : ℕ} {L : Type*} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
  {B : LinearMap.BilinForm ℤ L} {D : ZMod (n + 1) → L}
  (hGram : ∀ i j, B (D i) (D j) =
    (-2 : ℤ) * (if i = j then 1 else 0) +
      (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))
  (hB : B.IsSymm)

local notation "M" => span ℤ (Set.range D)
local notation "δ₀" => ∑ i, D i
local notation "W" => B.orthogonal (ℤ ∙ δ₀)
local notation "A" => ofIntegralForm (B.restrict M) (hB.restrict M)
local notation "N" => ofIntegralForm (B.restrict W) (hB.restrict W)

include hGram hB in
private theorem baseChange_inclusion_mem_radical {x : ℚ ⊗[ℤ] M} (hx : x ∈ (A).radical) :
    (inclusion (span_le_orthogonal_total hGram)).baseChange ℚ x ∈ (N).radical := by
  rw [radical_ofIntegralForm_restrict_span hGram hB, mem_span_singleton] at hx
  obtain ⟨r, rfl⟩ := hx
  rw [map_smul]
  apply (N).radical.smul_mem
  rw [LinearMap.baseChange_tmul]
  rw [← ofIntegralForm.coe_carrierEquiv_apply (B.restrict W) (hB.restrict W),
    ← radicalQuotientMap_eq_zero_iff,
    ofIntegralForm.radicalQuotientMap_carrierEquiv_eq_zero_iff (hB.restrict W), mem_ker]
  ext y
  simpa only [BilinForm.restrict_apply, domRestrict_apply, coe_inclusion, Submodule.coe_sum,
    coe_component, LinearMap.zero_apply] using
    B.mem_orthogonal_iff.mp y.property δ₀ (mem_span_singleton_self δ₀)

/-- The boundary span inclusion descends to the rational radical quotients. -/
def boundaryRadicalQuotientMap :
    (ℚ ⊗[ℤ] M) ⧸ (A).radical →ₗ[ℚ] (ℚ ⊗[ℤ] W) ⧸ (N).radical :=
  (A).radical.mapQ (N).radical ((inclusion (span_le_orthogonal_total hGram)).baseChange ℚ)
    (fun _ hx ↦ baseChange_inclusion_mem_radical hGram hB hx)

@[simp]
theorem boundaryRadicalQuotientMap_mk (x : ℚ ⊗[ℤ] M) :
    boundaryRadicalQuotientMap hGram hB (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((inclusion (span_le_orthogonal_total hGram)).baseChange ℚ x) :=
  mapQ_apply _ _ _ _

/-- The map on the rational radical quotients preserves intersection pairings. -/
theorem form_boundaryRadicalQuotientMap (x y : (ℚ ⊗[ℤ] M) ⧸ (A).radical) :
    (N).radicalQuotient.form (boundaryRadicalQuotientMap hGram hB x)
      (boundaryRadicalQuotientMap hGram hB y) = (A).radicalQuotient.form x y := by
  obtain ⟨x, rfl⟩ := (A).radical.mkQ_surjective x
  obtain ⟨y, rfl⟩ := (A).radical.mkQ_surjective y
  simp only [mkQ_apply, boundaryRadicalQuotientMap_mk, radicalQuotient_form,
    radicalQuotientForm_mk, ofIntegralForm_form]
  let f := (inclusion (span_le_orthogonal_total hGram)).baseChange ℚ
  suffices h : ((B.restrict W).baseChange ℚ).compl₁₂ f f = (B.restrict M).baseChange ℚ from
    LinearMap.congr_fun (LinearMap.congr_fun h x) y
  ext a b
  simp [f, BilinForm.baseChange_tmul]

/-- The boundary radical quotient embeds into the ambient isotropic quotient. -/
theorem boundaryRadicalQuotientMap_injective :
    Function.Injective (boundaryRadicalQuotientMap hGram hB) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  exact (A).nondegenerate_radicalQuotient.1 x fun y ↦ by
    rw [← form_boundaryRadicalQuotientMap hGram hB x y, hx]
    exact (LinearMap.congr_fun ((N).radicalQuotient.form.map_zero) _)

/-- The rational map agrees with inclusion on the integral quotient representatives. -/
theorem boundaryRadicalQuotientMap_radicalQuotientMap (x : M) :
    boundaryRadicalQuotientMap hGram hB
      ((A).radicalQuotientMap (ofIntegralForm.carrierEquiv (B.restrict M) (hB.restrict M) x)) =
    ((N).radicalQuotientMap (ofIntegralForm.carrierEquiv (B.restrict W) (hB.restrict W)
      (inclusion (span_le_orthogonal_total hGram) x)) :
      (ℚ ⊗[ℤ] W) ⧸ (N).radical) := by
  simp

/-- The embedding sends the integral boundary carrier into the integral ambient carrier. -/
theorem boundaryRadicalQuotientMap_mem_carrier {x : (ℚ ⊗[ℤ] M) ⧸ (A).radical}
    (hx : x ∈ (A).radicalQuotient.carrier) :
    boundaryRadicalQuotientMap hGram hB x ∈ (N).radicalQuotient.carrier := by
  obtain ⟨y, hy⟩ := (A).radicalQuotientMap_surjective ⟨x, hx⟩
  obtain ⟨z, rfl⟩ := (ofIntegralForm.carrierEquiv (B.restrict M) (hB.restrict M)).surjective y
  have hy' : ((A).radicalQuotientMap
      (ofIntegralForm.carrierEquiv (B.restrict M) (hB.restrict M) z) : (ℚ ⊗[ℤ] M) ⧸ (A).radical) =
      x := congrArg Subtype.val hy
  rw [← hy', boundaryRadicalQuotientMap_radicalQuotientMap]
  exact Subtype.property _

/-- The saturation of the boundary quotient in the ambient radical quotient, in the rational
space of the boundary quotient. -/
def boundarySaturationCarrier : (A).radicalQuotient.IntermediateCarrier := by
  let f := boundaryRadicalQuotientMap hGram hB
  let S := (N).radicalQuotient.carrier.comap (f.restrictScalars ℤ)
  refine ⟨S, fun _ hx ↦ boundaryRadicalQuotientMap_mem_carrier hGram hB hx, ?_⟩
  intro x hx
  apply (A).radicalQuotient.form.mem_dualSubmodule.mpr
  intro y hy
  rw [← form_boundaryRadicalQuotientMap hGram hB]
  exact (N).radicalQuotient.form_mem_one ⟨f x, hx⟩
    ⟨f y, boundaryRadicalQuotientMap_mem_carrier hGram hB hy⟩

@[simp]
theorem mem_boundarySaturationCarrier_iff (x : (ℚ ⊗[ℤ] M) ⧸ (A).radical) :
    x ∈ (boundarySaturationCarrier hGram hB).val ↔
      boundaryRadicalQuotientMap hGram hB x ∈ (N).radicalQuotient.carrier :=
  (Iff.rfl)

/-- The saturation inherits its integral form from the ambient radical quotient. -/
theorem isIntegral_boundarySaturationCarrier :
    IntermediateCarrier.IsIntegral (boundarySaturationCarrier hGram hB) := by
  refine IntermediateCarrier.isIntegral_def.mpr fun x hx y hy ↦ ?_
  rw [← form_boundaryRadicalQuotientMap hGram hB]
  exact (N).radicalQuotient.form_mem_one ⟨_, (mem_boundarySaturationCarrier_iff hGram hB x).mp hx⟩
    ⟨_, (mem_boundarySaturationCarrier_iff hGram hB y).mp hy⟩

/-- The saturated boundary carrier in the standard type-A coordinates for the cut at `k`.
The sign of the form is reversed to use the positive type-A lattice. -/
def typeASaturationCarrier (k : ZMod (n + 1)) :
    (typeARootLattice n).IntermediateCarrier := by
  let Q := (radicalQuotientIsometryNegTypeA hGram hB k).intermediateCarrierEquiv
    (boundarySaturationCarrier hGram hB)
  refine ⟨Q.val, ?_, ?_⟩
  · simpa only [neg_carrier] using Q.property.1
  · intro x hx
    apply (typeARootLattice n).form.mem_dualSubmodule.mpr
    intro y hy
    have h := (-(typeARootLattice n)).form.mem_dualSubmodule.mp (Q.property.2 hx) y
      (by simpa only [neg_carrier] using hy)
    simpa only [neg_form, LinearMap.neg_apply, neg_mem_iff] using h

/-- The type-A carrier is the image of the actual saturation under the boundary isometry. -/
theorem typeASaturationCarrier_val (k : ZMod (n + 1)) :
    (typeASaturationCarrier hGram hB k).val =
      (boundarySaturationCarrier hGram hB).val.map
        (radicalQuotientIsometryNegTypeA hGram hB k).ambientEquiv.toLinearMap := by
  unfold typeASaturationCarrier
  exact Isometry.intermediateCarrierEquiv_apply_coe
    (radicalQuotientIsometryNegTypeA hGram hB k) (boundarySaturationCarrier hGram hB)

/-- The type-A saturation inherits integrality from the ambient quotient. -/
theorem isIntegral_typeASaturationCarrier (k : ZMod (n + 1)) :
    IntermediateCarrier.IsIntegral (typeASaturationCarrier hGram hB k) := by
  let e := radicalQuotientIsometryNegTypeA hGram hB k
  have h := (e.isIntegral_intermediateCarrierEquiv_iff _).mpr
    (isIntegral_boundarySaturationCarrier hGram hB)
  refine IntermediateCarrier.isIntegral_def.mpr fun x hx y hy ↦ ?_
  have hxy := IntermediateCarrier.isIntegral_def.mp h x hx y hy
  simpa only [neg_form, LinearMap.neg_apply, neg_mem_iff] using hxy

private def boundarySaturationToAmbient :
    (boundarySaturationCarrier hGram hB).val →ₗ[ℤ] (N).radicalQuotient :=
  ((boundaryRadicalQuotientMap hGram hB).restrictScalars ℤ).restrict
    (fun x hx ↦ (mem_boundarySaturationCarrier_iff hGram hB x).mp hx)

variable [B.IsPerfPair] (hprim : TauCeti.IsPrimitive (∑ i : ZMod (n + 1), D i))

local notation "P" => Submodule.comap (Submodule.subtype W) (ℤ ∙ δ₀)

private def ambientQuotientMap : (N).radicalQuotient →ₗ[ℤ] L ⧸ M :=
  let h : ℤ ∙ δ₀ ≤ M :=
    (span_singleton_le_iff_mem _ _).mpr (sum_mem fun i _ ↦ subset_span (Set.mem_range_self i))
  let e : B.OrthogonalQuotient (ℤ ∙ δ₀) ≃ₗ[ℤ] (N).radicalQuotient :=
    (BilinForm.IsSymm.orthogonalQuotientIsometryRadicalQuotient (δ := δ₀) hB hprim).toLinearEquiv
  ((P).mapQ M (W).subtype (comap_mono h)).comp e.symm.toLinearMap

@[simp]
private theorem ambientQuotientMap_mk (x : W) :
    ambientQuotientMap (D := D) hB hprim
      ((N).radicalQuotientMap (ofIntegralForm.carrierEquiv (B.restrict W) (hB.restrict W) x)) =
      (M).mkQ x := by
  simp only [ambientQuotientMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← BilinForm.IsSymm.orthogonalQuotientIsometryRadicalQuotient_mk hB hprim,
    ← BilinForm.IsometryEquiv.coe_toLinearEquiv, LinearEquiv.symm_apply_apply,
    Submodule.mapQ_apply, Submodule.subtype_apply, mkQ_apply]

private def saturationToBoundaryCokernel :
    (boundarySaturationCarrier hGram hB).val →ₗ[ℤ] L ⧸ M :=
  (ambientQuotientMap (D := D) hB hprim).comp (boundarySaturationToAmbient hGram hB)

private theorem saturationToBoundaryCokernel_eq_mk
    (x : (boundarySaturationCarrier hGram hB).val) (y : W)
    (hxy : boundaryRadicalQuotientMap hGram hB x =
      ((N).radicalQuotientMap (ofIntegralForm.carrierEquiv (B.restrict W) (hB.restrict W) y) :
        (ℚ ⊗[ℤ] W) ⧸ (N).radical)) :
    saturationToBoundaryCokernel hGram hB hprim x = (M).mkQ y := by
  have hj : boundarySaturationToAmbient hGram hB x =
      (N).radicalQuotientMap (ofIntegralForm.carrierEquiv (B.restrict W) (hB.restrict W) y) :=
    Subtype.ext hxy
  simp only [saturationToBoundaryCokernel, LinearMap.comp_apply, hj, ambientQuotientMap_mk]

private theorem ker_saturationToBoundaryCokernel :
    (saturationToBoundaryCokernel hGram hB hprim).ker =
      (A).radicalQuotient.carrier.submoduleOf (boundarySaturationCarrier hGram hB).val := by
  ext x
  let f := boundaryRadicalQuotientMap hGram hB
  obtain ⟨v, hv⟩ := (N).radicalQuotientMap_surjective (boundarySaturationToAmbient hGram hB x)
  obtain ⟨y, rfl⟩ := (ofIntegralForm.carrierEquiv (B.restrict W) (hB.restrict W)).surjective v
  have hxy : f x = (N).radicalQuotientMap
      (ofIntegralForm.carrierEquiv (B.restrict W) (hB.restrict W) y) :=
    (congrArg Subtype.val hv).symm
  simp only [mem_ker, Submodule.submoduleOf, mem_comap, subtype_apply]
  constructor
  · intro hx
    rw [saturationToBoundaryCokernel_eq_mk hGram hB hprim x y hxy, mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hx
    let z : M := ⟨y, hx⟩
    let w := (A).radicalQuotientMap (ofIntegralForm.carrierEquiv (B.restrict M) (hB.restrict M) z)
    have hw : f w = f x := (boundaryRadicalQuotientMap_radicalQuotientMap hGram hB z).trans hxy.symm
    exact (boundaryRadicalQuotientMap_injective hGram hB hw) ▸ w.property
  · intro hx
    obtain ⟨v, hv'⟩ := (A).radicalQuotientMap_surjective ⟨x, hx⟩
    obtain ⟨z, rfl⟩ := (ofIntegralForm.carrierEquiv (B.restrict M) (hB.restrict M)).surjective v
    have hz : f x = (N).radicalQuotientMap (ofIntegralForm.carrierEquiv (B.restrict W)
        (hB.restrict W) (inclusion (span_le_orthogonal_total hGram) z)) :=
      (congrArg f (congrArg Subtype.val hv')).symm.trans
        (boundaryRadicalQuotientMap_radicalQuotientMap hGram hB z)
    rw [saturationToBoundaryCokernel_eq_mk hGram hB hprim x _ hz, mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact z.property

private theorem range_saturationToBoundaryCokernel :
    (saturationToBoundaryCokernel hGram hB hprim).range = Submodule.torsion ℤ (L ⧸ M) := by
  let C := boundarySaturationCarrier hGram hB
  let f := boundaryRadicalQuotientMap hGram hB
  ext q
  rw [Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨k, hk, hkm⟩ := Submodule.IsLattice.exists_ne_zero_smul_mem ℚ
      (A).radicalQuotient.carrier Submodule.IsFullLattice.span_eq_top (x : _)
    refine ⟨⟨k, mem_nonZeroDivisors_of_ne_zero hk⟩, ?_⟩
    rw [Submonoid.smul_def, ← map_smul, ← LinearMap.mem_ker, ker_saturationToBoundaryCokernel]
    exact hkm
  · rintro ⟨k, hk⟩
    obtain ⟨y, rfl⟩ := (M).mkQ_surjective q
    have hm : (k : ℤ) • y ∈ M := by
      apply (Submodule.Quotient.mk_eq_zero M).mp
      simpa only [← mkQ_apply, map_smul, Submonoid.smul_def] using hk
    have hy : y ∈ W := by
      have hky := span_le_orthogonal_total hGram hm
      rw [BilinForm.orthogonal, orthogonalBilin_span_singleton, mem_ker, map_smul] at hky
      rw [BilinForm.orthogonal, orthogonalBilin_span_singleton, mem_ker]
      exact (smul_eq_zero.mp hky).resolve_left (nonZeroDivisors.coe_ne_zero k)
    let w : W := ⟨y, hy⟩
    let z := (N).radicalQuotientMap (ofIntegralForm.carrierEquiv (B.restrict W) (hB.restrict W) w)
    let a := (A).radicalQuotientMap
      (ofIntegralForm.carrierEquiv (B.restrict M) (hB.restrict M) ⟨(k : ℤ) • y, hm⟩)
    have hfa : f a = (k : ℤ) • (z : (ℚ ⊗[ℤ] W) ⧸ (N).radical) := by
      rw [boundaryRadicalQuotientMap_radicalQuotientMap]
      -- The included representative is the same integer multiple in the orthogonal complement.
      have hw : inclusion (span_le_orthogonal_total hGram) ⟨(k : ℤ) • y, hm⟩ = (k : ℤ) • w :=
        Subtype.ext rfl
      simp only [hw, map_smul, SetLike.val_smul, z]
    let x := ((k : ℤ) : ℚ)⁻¹ • (a : (ℚ ⊗[ℤ] M) ⧸ (A).radical)
    have hx : f x = z := by
      have hk' : ((k : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (nonZeroDivisors.coe_ne_zero k)
      simp only [x, map_smul, hfa, ← Int.cast_smul_eq_zsmul ℚ, inv_smul_smul₀ hk']
    let xC : C.val := ⟨x, (mem_boundarySaturationCarrier_iff hGram hB x).mpr (hx ▸ z.property)⟩
    exact ⟨xC, saturationToBoundaryCokernel_eq_mk hGram hB hprim xC w hx⟩

/-- The quotient of the saturation by the boundary lattice is the torsion of the
original ambient quotient. -/
def boundarySaturationQuotientEquivTorsion :
    ((boundarySaturationCarrier hGram hB).val ⧸
      (A).radicalQuotient.carrier.submoduleOf (boundarySaturationCarrier hGram hB).val) ≃ₗ[ℤ]
        Submodule.torsion ℤ (L ⧸ M) :=
  (quotEquivOfEq _ _ (ker_saturationToBoundaryCokernel hGram hB hprim).symm).trans
    ((saturationToBoundaryCokernel hGram hB hprim).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (range_saturationToBoundaryCokernel hGram hB hprim)))

/-- The torsion comparison sends an integral ambient representative to its class modulo
the original boundary span. -/
theorem coe_boundarySaturationQuotientEquivTorsion_mk
    (x : (boundarySaturationCarrier hGram hB).val) (y : W)
    (hxy : boundaryRadicalQuotientMap hGram hB x =
      ((N).radicalQuotientMap (ofIntegralForm.carrierEquiv (B.restrict W) (hB.restrict W) y) :
        (ℚ ⊗[ℤ] W) ⧸ (N).radical)) :
    (boundarySaturationQuotientEquivTorsion hGram hB hprim (Submodule.Quotient.mk x) :
      L ⧸ M) = (M).mkQ y := by
  rw [boundarySaturationQuotientEquivTorsion, LinearEquiv.trans_apply, quotEquivOfEq_mk,
    LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply, LinearMap.quotKerEquivRange_apply_mk]
  exact saturationToBoundaryCokernel_eq_mk hGram hB hprim x y hxy

include hprim in
/-- The index of the saturated boundary quotient is the original boundary saturation index. -/
theorem index_boundarySaturationCarrier :
    IntermediateCarrier.index (boundarySaturationCarrier hGram hB) =
      Nat.card (AddCommGroup.torsion (L ⧸ M)) := by
  rw [IntermediateCarrier.index_eq_natCard_quotient, ← Submodule.torsion_int]
  exact Nat.card_congr (boundarySaturationQuotientEquivTorsion hGram hB hprim).toEquiv

include hprim in
/-- In type-A coordinates the index is still the order of the original saturation quotient. -/
theorem index_typeASaturationCarrier (k : ZMod (n + 1)) :
    IntermediateCarrier.index (typeASaturationCarrier hGram hB k) =
      Nat.card (AddCommGroup.torsion (L ⧸ M)) := by
  let e := radicalQuotientIsometryNegTypeA hGram hB k
  rw [← index_boundarySaturationCarrier hGram hB hprim, IntermediateCarrier.index_def,
    IntermediateCarrier.index_def, typeASaturationCarrier_val, ← neg_carrier (typeARootLattice n),
    ← e.map_carrier_ambientEquiv]
  exact AddSubgroup.relIndex_map_map_of_injective
    (f := e.ambientEquiv.toLinearMap.toAddMonoidHom) (A).radicalQuotient.carrier.toAddSubgroup
    (boundarySaturationCarrier hGram hB).val.toAddSubgroup e.ambientEquiv.injective

include hprim in
/-- In type-A coordinates the saturated carrier is the overlattice cut out by the degree
moments of torsion classes. The description is independent of the choice of cut. -/
theorem typeASaturationCarrier_eq_intermediateCarrierOfDiscriminantSubgroup (k : ZMod (n + 1)) :
    typeASaturationCarrier hGram hB k =
      (typeARootLattice n).intermediateCarrierOfDiscriminantSubgroup
        (((typeADiscriminantGroupEquiv n).toAddMonoidHom.comp
          (degreeMoment hGram).toAddMonoidHom).comp
          (AddCommGroup.torsion (L ⧸ M)).subtype).range := by
  let A₀ := typeARootLattice n
  let e := typeADiscriminantGroupEquiv n
  let f := (e.toAddMonoidHom.comp (degreeMoment hGram).toAddMonoidHom).comp
    (AddCommGroup.torsion (L ⧸ M)).subtype
  let : HasUniqueDiv L := .of_isTorsionFree ℤ L
  have hf : Function.Injective f :=
    e.injective.comp (degreeMoment_injective_on_torsion hGram hprim)
  let : IsAddCyclic A₀.DiscriminantGroup := e.isAddCyclic.mp inferInstance
  apply A₀.intermediateCarrierOrderIsoDiscriminantSubgroup.injective
  rw [intermediateCarrierOrderIsoDiscriminantSubgroup_apply,
    intermediateCarrierOrderIsoDiscriminantSubgroup_apply,
    discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup,
    IsAddCyclic.addSubgroup_eq_iff_card_eq,
    ← IntermediateCarrier.index_eq_natCard_discriminantSubgroup,
    index_typeASaturationCarrier hGram hB hprim]
  exact Nat.card_congr (Equiv.ofInjective f hf)

include hprim in
/-- The boundary length is the discriminant of the saturated lattice times the square of the
original saturation index. -/
theorem discriminant_typeASaturationCarrier_mul_index_sq (k : ZMod (n + 1)) :
    (isIntegral_typeASaturationCarrier hGram hB k).toIntegralLattice.discriminant *
      Nat.card (AddCommGroup.torsion (L ⧸ M)) ^ 2 = n + 1 := by
  rw [← index_typeASaturationCarrier hGram hB hprim k,
    (isIntegral_typeASaturationCarrier hGram hB k).discriminant_mul_index_sq,
    discriminant_typeARootLattice]

end QPainleve.BoundaryCycle
