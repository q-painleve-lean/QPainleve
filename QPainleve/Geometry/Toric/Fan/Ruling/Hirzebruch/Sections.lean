/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.Trivialization

import QPainleve.Geometry.Toric.Fan.Hirzebruch.CoordinateBoundary
import QPainleve.Geometry.Toric.Fan.Separated
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Invariant sections in the affine charts of a Hirzebruch ruling

The product trivializations carry the two horizontal ray divisors to the
constant coordinate sections of the projective line. The comparison is an
equality of ideal sheaves, so it can be used to compare the full boundary
with the summand sections of a split projective bundle.

The affine calculation uses `Fan.comap_ker_characterRuling_polynomialPoint`
and `rayIdeal_eq_span_of_apply_eq_one` on the chart of a single ray.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Module
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (e : ℤ)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])
  (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (k j : Fin 2)

local notation "P" => projectiveLine ℂ
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "p" => (P ↘ S)
local notation "A" => projectiveLineAffineFan k
local notation "baseMap" => Fan.algebraicRealizationStructureMap A
local notation "c" => projectiveLineAffineFanι k
local notation "m" => LinearMap.toAddMonoidHom (Basis.coord b 1)
local notation "g" => Φ.characterRuling m (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)
local notation "U" => hirzebruchRulingAffineFan b e r hr k
local notation "H" => isPullback_hirzebruchRulingAffineFan b e r hr k
local notation "u" => Iso.hom (hirzebruchRulingAffineIso b e r hr hΦ hc k) ≫ pullback.fst p baseMap
local notation "Rₛ" => r ((![0, 2] : Fin 2 → Fin 4) j)
local notation "q" => projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) j 0
local notation "I" => Φ.rayBoundaryIdeal hΦ Rₛ

include hr in
private theorem horizontalRay_mem_affineFan :
    (Rₛ).toCone.val ∈ (U).cones := by
  refine (mem_hirzebruchRulingAffineFan_cones_iff b e r hr k).2 ⟨(Rₛ).toCone.property, ?_⟩
  have hzero : m (Rₛ).primitiveGenerator = 0 := by
    have he := congrFun hr
    fin_cases j <;> simp [he, Basis.coord_apply]
  rw [Ray.toCone_eq_hull_primitiveGenerator, PointedCone.map, Submodule.map_span,
    Set.image_singleton, Submodule.span_singleton_le_iff_mem]
  have he : (Φ.characterFanHom m (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)).realMap
      (i (Rₛ).primitiveGenerator) = 0 := by
    ext l
    simp [characterFanHom_realMap, IsIntegralLattice.realCharacter_apply, hzero]
  -- Cone maps use the restriction of the real linear map to nonnegative scalars.
  exact he.symm ▸ zero_mem _

local notation "σ" =>
  (Subtype.mk (Subtype.val (Ray.toCone Φ Rₛ)) (horizontalRay_mem_affineFan b e r hr k j) :
    Fan.cones U)
local notation "v" => Fan.affineToricChartι U σ ≫ Iso.hom (IsPullback.isoPullback H)

include hr in
private theorem rayChart_comp_affineIso_comap :
    (q).ker.comap ((v) ≫ (u)) = (I).comap (Φ.affineToricChartι (Rₛ).toCone) := by
  let F := hirzebruchRulingAffineFanEquiv b e r hr hΦ hc k
  let n := (b.coord 0 + (if k = 0 then 0 else e) • b.coord 1).toAddMonoidHom
  let f := (FanHom.fst (Fan.projectiveSpace (Pi.basisFun ℤ (Fin 1))
    (isIntegralLattice_intCast 1)) (A)).comp F.toFanHom
  obtain ⟨hn, hf⟩ := f.exists_eq_characterFanHom n fun x l ↦ by
    simp [f, F, FanHom.comp_latticeMap, FanHom.fst_latticeMap,
      hirzebruchRulingAffineFanEquiv_latticeEquiv_apply, n]
    split_ifs <;> simp [*]
  have hu : (v) ≫ (u) = (U).affineToricChartι (σ) ≫ (U).characterRuling n hn := by
    rw [Category.assoc, hirzebruchRulingAffineIso_hom_fst, ← reassoc_of% FanHom.algebraicMap_comp]
    rw [characterRuling_def, ← hf]
  let n' := if j = 0 then n else -n
  have hval : n' (Rₛ).primitiveGenerator = 1 := by
    have he := congrFun hr
    fin_cases j <;> simp [n', n, he, Basis.coord_apply] <;> split_ifs <;> simp [Basis.coord_apply]
  have hcone : (σ).val = (Rₛ).toCone.val := rfl
  have hmem : n' ∈ dualSemigroup (U).lattice (σ).val := by
    rw [hcone, Ray.toCone_eq_hull_primitiveGenerator,
      ← Set.image_singleton, mem_dualSemigroup_hull_image, Set.forall_mem_singleton, hval]
    omega
  let τ := (Rₛ).toToricRay Φ (Rₛ).toCone le_rfl
  have hgen := (Rₛ).primitiveGenerator_toToricRay (Rₛ).toCone le_rfl
  rw [hu, (U).comap_ker_characterRuling_polynomialPoint n hn (σ) j hmem 0,
    Φ.comap_rayBoundaryIdeal_eq_ofIdealTop hΦ Rₛ (Rₛ).toCone le_rfl,
    rayIdeal_eq_span_of_apply_eq_one (ρ := τ) (a := ⟨n', hmem⟩)]
  · simp [n']
  · rw [hgen, ← (Rₛ).toCone_eq_hull_primitiveGenerator]
  · exact (congrArg n' hgen).trans hval

include hr in
private theorem comap_coordinateIdeal_le_horizontalRay :
    (q).ker.comap (u) ≤ (I).comap (pullback.fst g c) := by
  let π := pullback.fst g c
  have hv : (v) ≫ π = Φ.affineToricChartι (Rₛ).toCone := by
    rw [Category.assoc, (H).isoPullback_hom_fst,
      affineToricChartι_comp_hirzebruchRulingAffineFanInclusion]
  obtain ⟨x, hx⟩ := (Φ.rayBoundaryPoint_mem_range_affineToricChartι_iff hΦ Rₛ (Rₛ).toCone).2 le_rfl
  have hxη : π ((v) x) = (Φ.rayBoundaryPoint hΦ Rₛ).val := by
    rw [← Scheme.Hom.comp_apply, hv, hx]
  have hq : (u) ((v) x) ∈ (q).ker.support := by
    have hx' : x ∈ ((q).ker.comap ((v) ≫ (u))).support := by
      rw [rayChart_comp_affineIso_comap b e r hr hΦ hc k j, support_comap]
      rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage,
        Φ.coe_support_rayBoundaryIdeal, hx]
      exact subset_closure (Set.mem_singleton _)
    simpa only [← SetLike.mem_coe, support_comap, TopologicalSpace.Closeds.coe_preimage,
      Set.mem_preimage, Scheme.Hom.comp_apply] using hx'
  -- The ray ideal is the vanishing ideal of the closure of this point in the open chart.
  have hπ : IsOpenImmersion π := inferInstanceAs (IsOpenImmersion (pullback.fst g c))
  rw [Φ.rayBoundaryIdeal_def, ← hxη, comap_vanishingIdeal_closure_singleton_apply,
    ← le_map_iff_comap_le, map_vanishingIdeal, ← le_support_iff_le_vanishingIdeal]
  exact TopologicalSpace.Closeds.closure_le.mpr <|
    (image_closure_subset_closure_image (u).continuous).trans (by
      simpa only [Set.image_singleton] using closure_minimal
        (Set.singleton_subset_iff.mpr hq) (q).ker.support.isClosed)

/-- The affine product chart of a complete regular Hirzebruch ruling carries the
horizontal ray `b 0` to `[1 : 0]` and the opposite ray to `[0 : 1]`, as closed
subschemes. This holds on both affine charts of the base. -/
theorem comap_coordinate_section_hirzebruch_ruling_affine_iso :
    (q).ker.comap (u) = (I).comap (pullback.fst g c) := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  obtain ⟨s, hs, hker, -, -⟩ := exists_hirzebruch_toric_boundary_sections_and_fibers
    b e hΦ r hr hc
  let s' : (A).algebraicRealization ⟶ pullback g c :=
    pullback.lift (c ≫ s j) (𝟙 _) (by simp [hs])
  have hq : q ≫ p = 𝟙 _ := by simp [projectiveLine.polynomialPoint_over]
  have hclosed : IsClosedImmersion q := (q).isClosedImmersion_of_comp_eq_id hq
  have : IsSeparated (g ≫ p) := by
    rw [CategoryTheory.comp_over, Fan.algebraicRealization_over]
    infer_instance
  have : IsSeparated g := IsSeparated.of_comp g p
  have hsclosed : IsClosedImmersion (s j) :=
    (s j).isClosedImmersion_of_comp_eq_id (hs j)
  have hs' : (s').ker = (I).comap (pullback.fst g c) := by
    rw [← hker j]
    exact (IsPullback.of_hasPullback g c).ker_eq_comap_of_comp_eq_id (hs j)
      (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
  have hle : (q).ker ≤ (s' ≫ (u)).ker := by
    rw [Scheme.Hom.ker_comp, le_map_iff_comap_le, hs']
    exact comap_coordinateIdeal_le_horizontalRay b e r hr hΦ hc k j
  -- The factorization through the coordinate point is forced by the base projection.
  let t := IsClosedImmersion.lift q (s' ≫ (u)) hle
  have ht : t ≫ q = s' ≫ (u) := IsClosedImmersion.lift_fac _ _ _
  have htp : t = baseMap := by
    simpa only [Category.assoc, hq, Category.comp_id, pullback.condition,
      hirzebruchRulingAffineIso_hom_snd_assoc, s', pullback.lift_snd_assoc, Category.id_comp]
      using congrArg (· ≫ p) ht
  have Hprod : IsPullback (u) (pullback.snd g c) p baseMap :=
    (IsPullback.of_hasPullback p baseMap).of_iso'
      (hirzebruchRulingAffineIso b e r hr hΦ hc k) (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  rw [htp] at ht
  exact (Hprod.ker_eq_comap_of_comp_eq_id hq (pullback.lift_snd _ _ _) ht.symm).symm.trans hs'

end TauCeti.Toric.Fan
