/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Basic
public import QPainleve.Geometry.Toric.BaseChange.Boundary
public import QPainleve.Geometry.Toric.Fan.Boundary.Node
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Global

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import QPainleve.Geometry.Toric.BaseChange.FiniteType
import QPainleve.Geometry.Toric.RegularChart
import QPainleve.Geometry.Toric.Fan.Subdivision
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Boundary divisors under a toric point blowup

The new ray of a star subdivision at a two-dimensional cone cuts out the
exceptional Cartier divisor of the blowup at the cone's distinguished point.
The comparison also identifies the reduced toric boundary with the sum of the
scheme-theoretic strict transform and the exceptional divisor. These identifications
extend `exists_iso_blowup_starSubdivisionAlong` to the boundary ideal sheaves.
Conversely, a node on a model of a subdivision determines the cone whose star
subdivision realizes the blowup at that node.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry
open _root_.AddMonoidAlgebra

namespace TauCeti.Toric.Fan

universe u

variable (k : Type u) [Field k] {N V : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

section

variable (hΦ : Φ.IsRegular) (σ : Φ.cones) (h₀ : σ.val ≠ ⊥)

local notation "Ψ" => Φ.starSubdivisionAlong hΦ σ.property
local notation "hΨ" => Φ.isRegular_starSubdivisionAlong hΦ σ.property
local notation "ρ" => Φ.starSubdivisionAlongRay hΦ σ.property h₀
local notation "F" => Φ.starSubdivisionAlong_isSubdivision hΦ σ.property h₀
local notation "π" => FanHom.finiteFanSchemeHom k (IsSubdivision.toFanHom F)
local notation "s" => Φ.distinguishedSection (R := k) σ
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

private theorem finiteFanSchemeHom_rayBoundaryChartPoint_starSubdivisionAlong
    (hfull : Nat.card (ToricRay σ.val) = Module.finrank ℤ N) :
    π ((Ψ).rayBoundaryChartPoint (R := k) hΨ ρ).val = s (IsLocalRing.closedPoint k) := by
  let C := (ρ).toCone
  let hC := (Ψ).isToricCone C.property
  let r := (ρ).toToricRay Ψ C le_rfl
  let hreg := isRegular_iff.1 hΨ _ C.property
  let x : PrimeSpectrum (affineChartRing k (Ψ).lattice C.val) :=
    (hreg.rayChartPoint (Ψ).lattice hC r k).val
  let hmaps : Set.MapsTo (F).toFanHom.realMap (C.val : Set V) (σ.val : Set V) := by
    rw [IsSubdivision.toFanHom_realMap]
    exact newRay_le_centerCone hΦ σ h₀
  rw [(Ψ).coe_rayBoundaryChartPoint, ← Scheme.Hom.comp_apply,
    (F).toFanHom.affineChartι_comp_finiteFanSchemeHom k C σ hmaps,
    Φ.distinguishedSection_def (R := k), Scheme.Hom.comp_apply,
    Scheme.Hom.comp_apply _ _ (show Spec (.of k) from IsLocalRing.closedPoint k)]
  refine congrArg (fun z : affineChart k Φ.lattice σ.val ↦ Φ.affineChartι k σ z) ?_
  rw [affineChartMap_def, Spec.map_apply, Spec.map_apply]
  let f := AddMonoidAlgebra.mapDomainAlgHom k k
    (dualSemigroupMap (Ψ).lattice Φ.lattice (F).toFanHom.latticeMap
      (F).toFanHom.realMap (F).toFanHom.map_lattice hmaps)
  let d := facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) k
  -- In the affine coordinate rings the two point maps contract prime ideals.
  change PrimeSpectrum.comap f.toRingHom x = PrimeSpectrum.comap d.toRingHom
    (IsLocalRing.closedPoint k)
  rw [PrimeSpectrum.ext_iff, PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
  simp only [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  have hd : Function.Surjective d.toRingHom := fun c ↦ ⟨algebraMap k _ c, d.commutes c⟩
  have hmax := RingHom.ker_isMaximal_of_surjective d.toRingHom hd
  refine (hmax.eq_of_le (PrimeSpectrum.comap f.toRingHom x).isPrime.ne_top ?_).symm
  dsimp only [d]
  let hσ := Φ.isToricCone σ.property
  rw [← iSup_rayChartIdeal_eq_ker_facePointAlgebraHom k Φ.lattice hσ
    (isRegular_iff.1 hΦ _ σ.property) hfull]
  refine iSup_le fun t ↦ (rayChartIdeal_le_iff Φ.lattice hσ t k _).mpr fun m hm ↦ ?_
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  let m' := dualSemigroupMap (Ψ).lattice Φ.lattice (F).toFanHom.latticeMap
    (F).toFanHom.realMap (F).toFanHom.map_lattice hmaps m
  have hsingle : f (single m 1) = single m' 1 :=
    AddMonoidAlgebra.mapDomain_single
  -- The subdivision leaves the lattice unchanged.
  have hchar := pos_on_newRay_of_pos_on_ray hΦ σ h₀ m t hm
  rw [show f.toRingHom (single m 1) = single m' 1 from hsingle, hreg.rayChartPoint_asIdeal,
    single_mem_rayChartIdeal_iff]
  right
  have hprim : primitiveGenerator (Ψ).lattice hC r = (ρ).primitiveGenerator :=
    (ρ).primitiveGenerator_def.symm
  simpa only [m', coe_dualSemigroupMap, IsSubdivision.toFanHom_latticeMap,
    AddMonoidHom.comp_id, hprim] using hchar

include hΦ in
private theorem isIntegral_exceptional_distinguishedSection
    (hN : Module.finrank ℤ N = 2) : IsIntegral ((I).comap (I).blowupToBase).subscheme := by
  let p := s (IsLocalRing.closedPoint k)
  have hr : Set.range s = {p} := Set.range_eq_singleton fun x ↦
    congrArg s (Subsingleton.elim x (IsLocalRing.closedPoint k))
  have hp : IsClosed ({p} : Set (Φ.finiteFanScheme k)) :=
    hr ▸ (s).isClosedEmbedding.isClosed_range
  let f := Φ.finiteFanSchemeToSpec k
  have hsmooth : SmoothOfRelativeDimension 2 f :=
    hN ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec (R := k) hΦ
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have := isRegularLocalRing_stalk_of_smooth f p
  have hd := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp hsmooth).2 p hp
  rw [(s).ker_eq_ker_fromSpecResidueField]
  have hE := isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hd
  exact hE.isIntegral_subscheme

/-- In a regular rank-two fan, the new ray divisor of a star subdivision at a
two-dimensional cone is the schematic inverse image of the reduced distinguished point. -/
theorem comap_ker_distinguishedSection_eq_rayDivisorIdeal
    (hN : Module.finrank ℤ N = 2) (hc : Nat.card (ToricRay σ.val) = 2) :
    (I).comap π = (Ψ).rayDivisorIdeal k hΨ ρ := by
  obtain ⟨_, e, _, he, _⟩ := exists_iso_blowup_starSubdivisionAlong k hΦ σ hN hc
  let E := (I).comap (I).blowupToBase
  let q := (Ψ).rayBoundaryChartPoint (R := k) hΨ ρ
  let q' := CodimensionOnePoint.mapOfIsOpenImmersion e.hom q
  have : IsIntegral E.subscheme := isIntegral_exceptional_distinguishedSection k hΦ σ hN
  have : Nonempty Φ.cones := ⟨σ⟩
  have : IsLocallyNoetherian (I).blowup :=
    LocallyOfFiniteType.isLocallyNoetherian (I).blowupToBase
  have hq' : (q' : (I).blowup) ∈ E.support := by
    rw [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage]
    have hpoint := finiteFanSchemeHom_rayBoundaryChartPoint_starSubdivisionAlong k hΦ σ h₀
      (hc.trans hN.symm)
    rw [CodimensionOnePoint.coe_mapOfIsOpenImmersion, ← Scheme.Hom.comp_apply, he, hpoint]
    exact (s).range_subset_ker_support ⟨_, rfl⟩
  have hEcart := (I).isEffectiveCartier_comap_blowupToBase
  have hη := (hEcart.mem_support_iff_eq_subschemeι_genericPoint q'.property).mp hq'
  have hE : vanishingIdeal ⟨closure {(q' : (I).blowup)}, isClosed_closure⟩ = E := by
    rw [hη, E.vanishingIdeal_closure_subschemeι_genericPoint]
  rw [← he, comap_comp]
  change E.comap e.hom = _
  rw [← hE, CodimensionOnePoint.coe_mapOfIsOpenImmersion,
    comap_vanishingIdeal_closure_singleton_apply, (Ψ).rayDivisorIdeal_def k]

/-- The exceptional class of a single point blowup corresponds to the positive class
of the new ray divisor under the comparison over the toric projection. -/
theorem pullback_blowupExceptionalClass_starSubdivisionAlong
    (hN : Module.finrank ℤ N = 2) (hc : Nat.card (ToricRay σ.val) = 2)
    (e : (Ψ).finiteFanScheme k ≅ (I).blowup) (he : e.hom ≫ (I).blowupToBase = π) :
    LineBundleClass.pullback e.hom (I).blowupExceptionalClass =
      (LineBundleClass.mk ((Ψ).isEffectiveCartier_rayDivisorIdeal k hΨ ρ).toInvertibleSheaf)⁻¹ := by
  let hE := (I).isEffectiveCartier_comap_blowupToBase
  have hcompare :
      ((I).comap (I).blowupToBase).comap e.hom = (Ψ).rayDivisorIdeal k hΨ ρ := by
    rw [← comap_comp, he]
    exact comap_ker_distinguishedSection_eq_rayDivisorIdeal k hΦ σ h₀ hN hc
  rw [blowupExceptionalClass_def, LineBundleClass.pullback_inv,
    hE.pullback_mk_toInvertibleSheaf (hE.comap e.hom),
    LineBundleClass.mk_toInvertibleSheaf_congr _ _ hcompare]

include h₀ in
private theorem toricBoundaryIdeal_le_ker_distinguishedSection :
    Φ.toricBoundaryIdeal k ⟨σ⟩ ≤ I := by
  rw [(s).ker_eq_vanishingIdeal_support, ← le_support_iff_le_vanishingIdeal,
    SetLike.coe_subset_coe.symm, Φ.support_toricBoundaryIdeal k,
    (s).support_ker, (s).isClosedEmbedding.isClosed_range.closure_eq]
  rintro _ ⟨x, rfl⟩ hx
  have hle := (Φ.distinguishedSection_mem_range_affineChartι_iff (R := k) σ
    ⟨⊥, Φ.bot_mem σ.property⟩ x).mp hx
  exact h₀ (le_bot_iff.mp hle)

/-- The reduced boundary on the star subdivision at a two-dimensional cone is the
strict transform of the old boundary plus the exceptional divisor. The equality
uses the scheme-theoretic strict transform on the native point blowup. -/
theorem comap_strictTransform_mul_exceptional_eq_toricBoundaryIdeal
    (hN : Module.finrank ℤ N = 2) (hn : Nonempty (Ψ).cones)
    (e : (Ψ).finiteFanScheme k ≅ (I).blowup) (he : e.hom ≫ (I).blowupToBase = π) :
    let D := Φ.toricBoundaryIdeal k ⟨σ⟩
    (((I).blowupMap D.subschemeι).ker * (I).comap (I).blowupToBase).comap e.hom =
      (Ψ).toricBoundaryIdeal k hn := by
  let D := Φ.toricBoundaryIdeal k ⟨σ⟩
  have : IsReduced D.subscheme := Φ.isReduced_toricBoundary k ⟨σ⟩
  have : IsIntegral ((I).comap (I).blowupToBase).subscheme :=
    isIntegral_exceptional_distinguishedSection k hΦ σ hN
  have hrad := radical_comap_blowupToBase_eq_ker_blowupMap_subschemeι_mul I D
    (toricBoundaryIdeal_le_ker_distinguishedSection k σ h₀)
  have hcomp : (D.comap (I).blowupToBase).comap e.hom = D.comap π := by
    rw [← comap_comp, he]
  have hvan : ((D.comap (I).blowupToBase).radical).comap e.hom = (D.comap π).radical := by
    rw [← radical_comap_of_isOpenImmersion, hcomp]
  exact (congrArg (fun J ↦ J.comap e.hom) hrad).symm.trans
    (hvan.trans ((F).radical_comap_toricBoundaryIdeal k hn ⟨σ⟩))

end

variable {Ψ : Fan i}

local notation "X[" Δ "]" => (finiteFanScheme k Δ)
local notation "s[" Δ "]" => (finiteFanSchemeToSpec k Δ)
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

/-- A closed node of the reduced boundary on a model of a subdivision determines a
two-ray cone on that subdivision. Blowing up the actual center ideal is the star
subdivision at this cone, with the new ray class equal to the exceptional class. -/
theorem IsSubdivision.exists_iso_starSubdivision_of_isNodeOfReducedBoundary
    (h : Ψ.IsSubdivision Φ) (hc : Φ.IsComplete)
    (hΨ : Ψ.IsRegular) (hN : Module.finrank ℤ N = 2) {Y : Scheme}
    (f : Y ⟶ X[Φ]) (e : X[Ψ] ≅ Y) (he : e.hom ≫ f = h.toFanHom.finiteFanSchemeHom k)
    {p : Y} {I : Y.IdealSheafData} (hI : I = (Y.fromSpecResidueField p).ker)
    (hp : ((Φ.toricBoundaryIdeal k hc.nonempty_cones).comap f).IsNodeOfReducedBoundary
      (f ≫ s[Φ]) p) :
    ∃ (σ : Ψ.cones) (hσ : Nat.card (ToricRay σ.val) = 2),
      let Ω := Ψ.starSubdivisionAlong hΨ σ.property
      let hΩ := Ψ.isRegular_starSubdivisionAlong hΨ σ.property
      let h₀ := ne_bot_of_card_toricRay_eq_two hσ
      let F := Ψ.starSubdivisionAlong_isSubdivision hΨ σ.property h₀
      let ρ := Ψ.starSubdivisionAlongRay hΨ σ.property h₀
      I.comap e.hom = (Ψ.distinguishedSection (R := k) σ).ker ∧
      ∃ g : X[Ω] ≅ I.blowup,
        g.hom ≫ I.blowupToBase = F.toFanHom.finiteFanSchemeHom k ≫ e.hom ∧
        LineBundleClass.pullback g.hom I.blowupExceptionalClass =
          classOf(Ω.isEffectiveCartier_rayDivisorIdeal k hΩ ρ) := by
  let D := (Φ.toricBoundaryIdeal k hc.nonempty_cones).comap f
  let x := e.inv p
  have hx : e.hom x = p := by simp [x]
  have hs : e.hom ≫ f ≫ s[Φ] = s[Ψ] := by
    rw [← Category.assoc, he, h.toFanHom.finiteFanSchemeHom_comp_finiteFanSchemeToSpec k]
  let : Nonempty Ψ.cones := h.nonempty_cones_of_nonempty hc.nonempty_cones
  have hrad : (D.comap e.hom).radical = Ψ.toricBoundaryIdeal k inferInstance := by
    change ((Φ.toricBoundaryIdeal k hc.nonempty_cones).comap f |>.comap e.hom).radical =
      Ψ.toricBoundaryIdeal k inferInstance
    rw [← comap_comp, he]
    exact h.radical_comap_toricBoundaryIdeal k inferInstance hc.nonempty_cones
  have hnode : (Ψ.toricBoundaryIdeal k inferInstance).IsNodeOfReducedBoundary s[Ψ] x := by
    have hp' : D.IsNodeOfReducedBoundary (f ≫ s[Φ]) (e.hom x) := by simpa only [hx] using hp
    have hn := (D.isNodeOfReducedBoundary_comap_iff_of_isOpenImmersion (f ≫ s[Φ]) e.hom x).mpr
      hp'
    rwa [← isNodeOfReducedBoundary_radical (D.comap e.hom), hrad, hs] at hn
  obtain ⟨σ, ⟨hσ, hpoint⟩, -⟩ :=
    (Ψ.isNodeOfReducedBoundary_iff_existsUnique_twoRayCone k hΨ
      (h.isComplete_iff.mpr hc) hN).mp hnode
  let q := Ψ.distinguishedSection (R := k) σ
  have hcenter : I.comap e.hom = q.ker := by
    rw [hI, ← hx, e.hom.comap_ker_fromSpecResidueField_apply,
      q.ker_eq_ker_fromSpecResidueField, hpoint]
  obtain ⟨_, d, _, hd, _⟩ := exists_iso_blowup_starSubdivisionAlong k hΨ σ hN hσ
  let g := d ≪≫ blowupIso e hcenter.symm
  refine ⟨σ, hσ, hcenter, g, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, blowupIso_hom_blowupToBase, ← Category.assoc, hd]
  · rw [Iso.trans_hom, ← LineBundleClass.pullback_comp,
      I.pullback_blowupExceptionalClass e hcenter]
    exact pullback_blowupExceptionalClass_starSubdivisionAlong k hΨ σ _ hN hσ d hd

end TauCeti.Toric.Fan
