/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Basic
public import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Global

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import QPainleve.Geometry.Toric.Fan.Boundary.Intersection
import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision
import QPainleve.Geometry.Toric.Fan.Smooth
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Boundary divisors under a toric point blowup

The new ray of a star subdivision at a two-dimensional cone cuts out the
exceptional Cartier divisor of the blowup at the cone's distinguished point.
The comparison also identifies the reduced toric boundary with the sum of the
scheme-theoretic strict transform and the exceptional divisor. These identifications
extend `exists_iso_blowup_starSubdivisionAlong` to the boundary ideal sheaves.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry Multiplicative

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (hΦ : Φ.IsRegular) (σ : Φ.cones) (h₀ : σ.val ≠ ⊥)

local notation "Ψ" => Φ.starSubdivisionAlong hΦ σ.property
local notation "hΨ" => Φ.isRegular_starSubdivisionAlong hΦ σ.property
local notation "ρ" => Φ.starSubdivisionAlongRay hΦ σ.property h₀
local notation "F" => Φ.starSubdivisionAlong_isSubdivision hΦ σ.property h₀
local notation "π" => FanHom.algebraicMap (IsSubdivision.toFanHom F)
local notation "s" => Φ.distinguishedPointHom σ
local notation "I" => Scheme.Hom.ker s

private theorem newRay_le_centerCone : (ρ).toCone.val ≤ σ.val := by
  rw [coe_toCone_starSubdivisionAlongRay, Submodule.span_singleton_le_iff_mem]
  simpa only [starSubdivisionGenerator_none] using
    starSubdivisionGenerator_mem Φ.lattice
      (ToricRay.faceFinset (PointedCone.IsFaceOf.refl σ.val) (Φ.isToricCone σ.property).fg)
      (Φ.isToricCone σ.property) none

private theorem pos_on_newRay_of_pos_on_ray (m : dualSemigroup Φ.lattice σ.val)
    (r : ToricRay σ.val) (hm : 0 < (m : N →+ ℤ) (primitiveGenerator Φ.lattice
      (Φ.isToricCone σ.property) r)) :
    0 < (m : N →+ ℤ) (ρ).primitiveGenerator := by
  have hnonneg := (mem_dualSemigroup Φ.lattice m).1 m.property
    (newRay_le_centerCone hΦ σ h₀ (ρ).primitiveGenerator_mem)
  rw [Φ.lattice.realCharacter_apply] at hnonneg
  have hnonneg' : 0 ≤ (m : N →+ ℤ) (ρ).primitiveGenerator := by exact_mod_cast hnonneg
  apply lt_of_le_of_ne hnonneg'
  intro hz
  let K := PointedCone.ofSubmodule (LinearMap.ker (Φ.lattice.realCharacter m))
  have hface : (σ.val ⊓ K).IsFaceOf σ.val :=
    PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup Φ.lattice m).1 m.property)
  have hle : (ρ).toCone.val ≤ σ.val ⊓ K := by
    rw [(ρ).toCone_eq_hull_primitiveGenerator, Submodule.span_singleton_le_iff_mem]
    refine ⟨newRay_le_centerCone hΦ σ h₀ (ρ).primitiveGenerator_mem, ?_⟩
    exact LinearMap.mem_ker.mpr (by rw [Φ.lattice.realCharacter_apply, ← hz, Int.cast_zero])
  have hleast : (F).toFanHom.leastCone (ρ).toCone.property ≤ σ.val ⊓ K := by
    apply (F).toFanHom.leastCone_le _ (Φ.mem_of_isFaceOf σ.property hface)
    rwa [IsSubdivision.toFanHom_realMap, PointedCone.map_id]
  have hc := (Φ.starSubdivisionAlongRay_le_iff_le_leastCone hΦ σ.property h₀ (ρ).toCone).mp le_rfl
  have hz' : Φ.lattice.realCharacter m (i (primitiveGenerator Φ.lattice
      (Φ.isToricCone σ.property) r)) = 0 :=
    LinearMap.mem_ker.mp ((hc.trans hleast (r.val.isFaceOf.le
      (primitiveGenerator_mem Φ.lattice (Φ.isToricCone σ.property) r))).2)
  rw [Φ.lattice.realCharacter_apply] at hz'
  exact hm.ne' (Int.cast_eq_zero.mp hz')

private theorem algebraicMap_rayBoundaryPoint_starSubdivisionAlong
    (hfull : Nat.card (ToricRay σ.val) = Module.finrank ℤ N) :
    π ((Ψ).rayBoundaryPoint hΨ ρ).val = s (IsLocalRing.closedPoint ℂ) := by
  let C := (ρ).toCone
  let hC := (Ψ).isToricCone C.property
  let r := (ρ).toToricRay Ψ C le_rfl
  let hreg := isRegular_iff.1 hΨ _ C.property
  let x : PrimeSpectrum (affineCoordinateRing (Ψ).lattice C.val) :=
    (hreg.rayPoint (Ψ).lattice hC r).val
  let hmaps : Set.MapsTo (F).toFanHom.realMap (C.val : Set V) (σ.val : Set V) := by
    rw [IsSubdivision.toFanHom_realMap]
    exact newRay_le_centerCone hΦ σ h₀
  rw [(Ψ).coe_rayBoundaryPoint, ← Scheme.Hom.comp_apply,
    (F).toFanHom.affineToricChartι_comp_algebraicMap_of_mapsTo C σ hmaps,
    Φ.distinguishedPointHom_def, Scheme.Hom.comp_apply,
    Scheme.Hom.comp_apply _ _ (show Spec (.of ℂ) from IsLocalRing.closedPoint ℂ)]
  refine congrArg (fun z : Φ.affineToricChart σ ↦ Φ.affineToricChartι σ z) ?_
  rw [affineToricSchemeMap_def, Spec.map_apply, Spec.map_apply]
  let f := affineCoordinateRingMap (Ψ).lattice Φ.lattice (F).toFanHom.latticeMap
    (F).toFanHom.realMap (F).toFanHom.map_lattice hmaps
  let d := distinguishedPoint Φ.lattice (⊤ : σ.val.Face)
  -- In the affine coordinate rings the two point maps contract prime ideals.
  change PrimeSpectrum.comap f.toRingHom x = PrimeSpectrum.comap d.toRingHom
    (IsLocalRing.closedPoint ℂ)
  rw [PrimeSpectrum.ext_iff, PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
  simp only [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  have hd : Function.Surjective d.toRingHom := fun c ↦ ⟨algebraMap ℂ _ c, d.commutes c⟩
  have hmax := RingHom.ker_isMaximal_of_surjective d.toRingHom hd
  refine (hmax.eq_of_le (PrimeSpectrum.comap f.toRingHom x).isPrime.ne_top ?_).symm
  dsimp only [d]
  let hσ := Φ.isToricCone σ.property
  rw [← iSup_rayIdeal_eq_ker_distinguishedPoint Φ.lattice hσ
    (isRegular_iff.1 hΦ _ σ.property) hfull]
  refine iSup_le fun t ↦ (rayIdeal_le_iff Φ.lattice hσ t _).mpr fun m hm ↦ ?_
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, MonoidAlgebra.of_apply]
  let m' := dualSemigroupMap (Ψ).lattice Φ.lattice (F).toFanHom.latticeMap
    (F).toFanHom.realMap (F).toFanHom.map_lattice hmaps m
  have hsingle : f.toRingHom (MonoidAlgebra.single (ofAdd m) 1) =
      MonoidAlgebra.single (ofAdd m') 1 :=
    affineCoordinateRingMap_single _ _ _ _ _ hmaps m 1
  -- The subdivision leaves the lattice unchanged, so the pulled back character
  -- has the same value at the new primitive generator.
  have hchar := pos_on_newRay_of_pos_on_ray hΦ σ h₀ m t hm
  rw [hsingle, show x.asIdeal = _ from hreg.rayPoint_asIdeal (Ψ).lattice hC r,
    monomial_mem_rayIdeal_iff _ _ hreg]
  have hprim : primitiveGenerator (Ψ).lattice hC r = (ρ).primitiveGenerator :=
    (ρ).primitiveGenerator_def.symm
  simpa only [m', coe_dualSemigroupMap, IsSubdivision.toFanHom_latticeMap,
    AddMonoidHom.comp_id, hprim] using hchar

include hΦ in
private theorem isIntegral_exceptional_distinguishedPointHom
    (hN : Module.finrank ℤ N = 2) : IsIntegral ((I).comap (I).blowupToBase).subscheme := by
  let p := s (IsLocalRing.closedPoint ℂ)
  have hs := Φ.isClosedImmersion_distinguishedPointHom σ
  have hr : Set.range s = {p} := Set.range_eq_singleton fun x ↦
    congrArg s (Subsingleton.elim x (IsLocalRing.closedPoint ℂ))
  have hp : IsClosed ({p} : Set Φ.algebraicRealization) :=
    hr ▸ (s).isClosedEmbedding.isClosed_range
  let f := Φ.algebraicRealizationStructureMap
  have hsmooth : SmoothOfRelativeDimension 2 f :=
    hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have := isRegularLocalRing_stalk_of_smooth f p
  have hd := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp hsmooth).2 p hp
  rw [(s).ker_eq_ker_fromSpecResidueField]
  have hE := isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hd
  exact hE.isIntegral_subscheme

/-- In a regular rank-two fan, the new ray divisor of a star subdivision at a
two-dimensional cone is the schematic inverse image of the reduced distinguished point. -/
theorem comap_ker_distinguishedPointHom_eq_rayBoundaryIdeal
    (hN : Module.finrank ℤ N = 2) (hc : Nat.card (ToricRay σ.val) = 2) :
    (I).comap π = (Ψ).rayBoundaryIdeal hΨ ρ := by
  obtain ⟨_, e, _, he, _⟩ := exists_iso_blowup_starSubdivisionAlong hΦ σ hN hc
  let E := (I).comap (I).blowupToBase
  let q := (Ψ).rayBoundaryPoint hΨ ρ
  let q' := CodimensionOnePoint.mapOfIsOpenImmersion e.hom q
  have : IsIntegral E.subscheme := isIntegral_exceptional_distinguishedPointHom hΦ σ hN
  have : Nonempty Φ.cones := ⟨σ⟩
  have : IsLocallyNoetherian (I).blowup :=
    LocallyOfFiniteType.isLocallyNoetherian (I).blowupToBase
  have hq' : (q' : (I).blowup) ∈ E.support := by
    rw [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage]
    have hpoint := algebraicMap_rayBoundaryPoint_starSubdivisionAlong hΦ σ h₀ (hc.trans hN.symm)
    rw [CodimensionOnePoint.coe_mapOfIsOpenImmersion, ← Scheme.Hom.comp_apply, he, hpoint]
    exact (s).range_subset_ker_support ⟨_, rfl⟩
  have hEcart := (I).isEffectiveCartier_comap_blowupToBase
  have hη := (hEcart.mem_support_iff_eq_subschemeι_genericPoint q'.property).mp hq'
  have hE : vanishingIdeal ⟨closure {(q' : (I).blowup)}, isClosed_closure⟩ = E := by
    rw [hη, E.vanishingIdeal_closure_subschemeι_genericPoint]
  rw [← he, comap_comp]
  change E.comap e.hom = _
  rw [← hE, CodimensionOnePoint.coe_mapOfIsOpenImmersion,
    comap_vanishingIdeal_closure_singleton_apply, (Ψ).rayBoundaryIdeal_def]

/-- The exceptional class of a single point blowup corresponds to the positive class
of the new ray divisor under the comparison over the toric projection. -/
theorem pullback_blowupExceptionalClass_starSubdivisionAlong
    (hN : Module.finrank ℤ N = 2) (hc : Nat.card (ToricRay σ.val) = 2)
    (e : (Ψ).algebraicRealization ≅ (I).blowup) (he : e.hom ≫ (I).blowupToBase = π) :
    LineBundleClass.pullback e.hom (I).blowupExceptionalClass =
      (LineBundleClass.mk ((Ψ).isEffectiveCartier_rayBoundaryIdeal hΨ ρ).toInvertibleSheaf)⁻¹ := by
  let hE := (I).isEffectiveCartier_comap_blowupToBase
  have hcompare :
      ((I).comap (I).blowupToBase).comap e.hom = (Ψ).rayBoundaryIdeal hΨ ρ := by
    rw [← comap_comp, he]
    exact comap_ker_distinguishedPointHom_eq_rayBoundaryIdeal hΦ σ h₀ hN hc
  rw [blowupExceptionalClass_def, LineBundleClass.pullback_inv,
    hE.pullback_mk_toInvertibleSheaf (hE.comap e.hom),
    LineBundleClass.mk_toInvertibleSheaf_congr _ _ hcompare]

include h₀ in
private theorem boundaryIdeal_le_ker_distinguishedPointHom :
    Φ.boundaryIdeal ⟨σ⟩ ≤ I := by
  have hs := Φ.isClosedImmersion_distinguishedPointHom σ
  rw [Φ.ker_distinguishedPointHom_eq_vanishingIdeal, ← le_support_iff_le_vanishingIdeal,
    SetLike.coe_subset_coe.symm, Φ.support_boundaryIdeal]
  rintro _ ⟨x, rfl⟩ hx
  rw [Φ.denseTorusι_eq_affineToricChartι ⟨σ⟩ (Φ.bot_mem σ.property)] at hx
  have hle := (Φ.distinguishedPointHom_mem_range_affineToricChartι_iff σ
    ⟨⊥, Φ.bot_mem σ.property⟩ x).mp hx
  exact h₀ (le_bot_iff.mp hle)

/-- The reduced boundary on the star subdivision at a two-dimensional cone is the
strict transform of the old boundary plus the exceptional divisor. The equality
uses the scheme-theoretic strict transform on the native point blowup. -/
theorem comap_strictTransform_mul_exceptional_eq_boundaryIdeal
    (hN : Module.finrank ℤ N = 2) (hn : Nonempty (Ψ).cones)
    (e : (Ψ).algebraicRealization ≅ (I).blowup) (he : e.hom ≫ (I).blowupToBase = π) :
    let D := Φ.boundaryIdeal ⟨σ⟩
    (((I).blowupMap D.subschemeι).ker * (I).comap (I).blowupToBase).comap e.hom =
      (Ψ).boundaryIdeal hn := by
  let D := Φ.boundaryIdeal ⟨σ⟩
  have : IsReduced D.subscheme := by
    dsimp only [D]
    rw [Φ.boundaryIdeal_def]
    infer_instance
  have : IsIntegral ((I).comap (I).blowupToBase).subscheme :=
    isIntegral_exceptional_distinguishedPointHom hΦ σ hN
  have hrad := radical_comap_blowupToBase_eq_ker_blowupMap_subschemeι_mul I D
    (boundaryIdeal_le_ker_distinguishedPointHom σ h₀)
  have hcomp : (D.comap (I).blowupToBase).comap e.hom = D.comap π := by
    rw [← comap_comp, he]
  have hvan : ((D.comap (I).blowupToBase).radical).comap e.hom = (D.comap π).radical := by
    rw [← radical_comap_of_isOpenImmersion, hcomp]
  exact (congrArg (fun J ↦ J.comap e.hom) hrad).symm.trans
    (hvan.trans ((F).radical_comap_boundaryIdeal hn ⟨σ⟩))

end TauCeti.Toric.Fan
