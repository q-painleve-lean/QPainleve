/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
public import QPainleve.AlgebraicGeometry.IdealSheaf.BoundaryComplexity

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryPrimes
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.Blowup.Restriction

/-!
# Boundary complexity under nodal blowups

For a surface with a boundary divisor, the complexity is its Picard rank plus two
minus the number of boundary prime divisors. Blowing up a node adds one exceptional
coordinate to the Picard group and one prime to the reduced total boundary. This is
the corner blowup invariance of the charge in Friedman's
*On the geometry of anticanonical pairs*, Lemmas 1.2 and 2.2.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

-- Off a center of codimension two, the isomorphism locus matches the old boundary primes.
private theorem bijOn_boundaryPrimes_comap_off_point (D : X.IdealSheafData) (π : Y ⟶ X)
    {p : X} (hp : Order.coheight p ≠ 1) (hIso : ∀ x : X, x ≠ p → x ∈ π.isoLocus) :
    Set.BijOn π ((D.comap π).boundaryPrimes ∩ {y | π y ≠ p}) D.boundaryPrimes := by
  refine ⟨?_, π.injOn_preimage_isoLocus.mono (fun y hy ↦ hIso (π y) hy.2), ?_⟩
  · intro y hy
    obtain ⟨h, hc⟩ := mem_boundaryPrimes.mp hy.1
    rw [support_comap] at h
    exact mem_boundaryPrimes.mpr
      ⟨h, (π.coheight_eq_of_apply_mem_isoLocus (hIso (π y) hy.2)).trans hc⟩
  · intro x hx
    obtain ⟨hxD, hxc⟩ := mem_boundaryPrimes.mp hx
    have hne : x ≠ p := fun he ↦ hp (he ▸ hxc)
    let U := π.isoLocus
    obtain ⟨y, hy⟩ := (π ∣_ U).surjective ⟨x, hIso x hne⟩
    have hxy : π ((π ⁻¹ᵁ U).ι y) = x := by
      rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hy]
      rfl
    exact ⟨_, ⟨mem_boundaryPrimes.mpr
      ⟨by
        rw [support_comap]
        exact (show π ((π ⁻¹ᵁ U).ι y) ∈ D.support from hxy.symm ▸ hxD),
        (π.coheight_eq_of_apply_mem_isoLocus (hxy.symm ▸ hIso x hne)).symm.trans
          (hxy.symm ▸ hxc)⟩,
      (show π ((π ⁻¹ᵁ U).ι y) ≠ p from hxy.symm ▸ hne)⟩, hxy⟩

-- The blowup is an isomorphism away from the center, so the nonexceptional primes
-- correspond bijectively to the original primes. The exceptional fiber has one prime.
private theorem encard_boundaryPrimes_comap_pointBlowup
    {k : Type u} [Field k] [IsNoetherian X]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]
    (D : X.IdealSheafData) {p : X} (hp : IsClosed ({p} : Set X)) (hD : p ∈ D.support) :
    let I := (X.fromSpecResidueField p).ker
    (D.comap I.blowupToBase).boundaryPrimes.encard = D.boundaryPrimes.encard + 1 := by
  dsimp only
  let I := (X.fromSpecResidueField p).ker
  let π := I.blowupToBase
  let E := I.comap π
  have := SmoothOfRelativeDimension.smooth 2 f
  have : IsRegular X := IsRegular.of_smooth f
  have hd := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp inferInstance).2 p hp
  have hp₂ := coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) f hp
  have hE := isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hd
  have : IsIntegral E.subscheme := hE.isIntegral_subscheme
  have : IsNoetherian I.blowup := (QPainleve.BlowupTower.nil.snoc I).isNoetherian
  let η := E.subschemeι (genericPoint E.subscheme)
  have hI : (I.support : Set X) = {p} := by
    rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hp.closure_eq]
  have hE' (y : I.blowup) (hy : Order.coheight y = 1) : π y = p ↔ y = η := by
    rw [← hE.isEffectiveCartier.mem_support_iff_eq_subschemeι_genericPoint hy, support_comap]
    -- The support of the extended center ideal is the inverse image of the point.
    change π y = p ↔ π y ∈ (I.support : Set X)
    rw [hI, Set.mem_singleton_iff]
  let S := (D.comap π).boundaryPrimes ∩ {y | π y ≠ p}
  have hIso (x : X) (hx : x ≠ p) : x ∈ π.isoLocus :=
    (π.le_isoLocus_iff.mpr I.isIso_blowupToBase_restrict_compl_support)
      (show x ∉ (I.support : Set X) from by rwa [hI, Set.mem_singleton_iff])
  have hη : π η = p := (hE' η hE.isEffectiveCartier.coheight_subschemeι_genericPoint).mpr rfl
  have hηD : η ∈ (D.comap π).boundaryPrimes :=
    mem_boundaryPrimes.mpr ⟨by
      rw [support_comap]
      exact (show π η ∈ D.support from hη.symm ▸ hD),
      hE.isEffectiveCartier.coheight_subschemeι_genericPoint⟩
  have hb : Set.BijOn π S D.boundaryPrimes :=
    bijOn_boundaryPrimes_comap_off_point D π (by rw [hp₂]; norm_num) hIso
  have hdecomp : (D.comap π).boundaryPrimes = insert η S := by
    ext y
    refine ⟨fun hy ↦ ?_, fun hy ↦ (Set.mem_insert_iff.mp hy).elim
      (fun he ↦ he.symm ▸ hηD) (fun hs ↦ hs.1)⟩
    by_cases he : π y = p
    · exact Set.mem_insert_iff.mpr (Or.inl ((hE' y (mem_boundaryPrimes.mp hy).2).mp he))
    · exact Set.mem_insert_of_mem _ ⟨hy, he⟩
  have hηS : η ∉ S := fun h ↦ h.2 hη
  rw [hdecomp, Set.encard_insert_of_notMem hηS, Set.encard_congr hb.equiv]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsNodalBoundaryTower

open Scheme.IdealSheafData

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} [IsNoetherian X]
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]
  {D : X.IdealSheafData} {n : ℕ} {T : BlowupTower X n Y}

/-- A nodal boundary tower adds one prime to the total boundary at each blowup. -/
theorem encard_boundaryPrimes_comap (hT : IsNodalBoundaryTower D f (𝟙 X) T) :
    (D.comap T.toBase).boundaryPrimes.encard = D.boundaryPrimes.encard + n := by
  induction hT with
  | nil => simp
  | @snoc m W R I hR p hp hI hnode ih =>
    subst I
    have := R.isNoetherian
    have := hR.isClosedPointTower.smoothOfRelativeDimension f
    have hDp : p ∈ (D.comap R.toBase).support := by
      simpa only [Category.comp_id] using mem_support_of_isNodeOfReducedBoundary hnode
    rw [toBase_snoc, comap_comp,
      encard_boundaryPrimes_comap_pointBlowup (R.toBase ≫ f) _ hp hDp, ih]
    push_cast
    rw [add_assoc]

/-- The complexity is unchanged by a tower of nodal blowups. The reduced total boundary
has the same support as the ideal pulled back along the tower. -/
theorem boundaryComplexity_comap [IsIntegral X] [X.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    [Module.Finite ℤ (Additive (LineBundleClass X))] (hD : D.IsEffectiveCartier)
    (hT : IsNodalBoundaryTower D (X ↘ Spec (.of k)) (𝟙 X) T) :
    (D.comap T.toBase).boundaryComplexity = D.boundaryComplexity := by
  have hcount := hT.encard_boundaryPrimes_comap _
  have hfinite := hD.finite_boundaryPrimes
  have hncard := congrArg ENat.toNat hcount
  have hcard : (D.comap T.toBase).boundaryPrimes.ncard = D.boundaryPrimes.ncard + n := by
    simpa only [Set.ncard_def, ENat.toNat_add hfinite.encard_lt_top.ne
      (ENat.natCast_ne_top n), ENat.toNat_natCast] using hncard
  rw [boundaryComplexity_def, boundaryComplexity_def,
    finrank_picard k hT.isClosedPointTower, hcard]
  push_cast
  ring

end QPainleve.BlowupTower.IsNodalBoundaryTower
