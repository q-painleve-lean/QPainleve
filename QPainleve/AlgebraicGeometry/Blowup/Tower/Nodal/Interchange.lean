/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Locus
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Locus
public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

import QPainleve.AlgebraicGeometry.Blowup.Smooth
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Disjoint
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Node
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Moving a nodal blowup before an internal blowup

A node of the strict boundary away from the exceptional divisor can be blown up
before the internal center. The moved centers have the correct reduced closed
subscheme structure. The two orders have the same final boundary over the base,
and the comparison identifies the two labeled total exceptional classes.

The interchange organizes the two types of blowup in the factorization of logarithmic
morphisms. See *Homological mirror symmetry for log Calabi–Yau surfaces* by Hacking
and Keating, Appendix by Wendelin Lutz, [Theorem 8.4][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}}

local notation "P[" p "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ p)
local notation "St[" I "," D "]" =>
  Scheme.Hom.ker (IdealSheafData.blowupMap I (IdealSheafData.subschemeι D))

section Point

variable {k : Type u} [Field k] (s : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 s]

/-- Move a closed node of the strict boundary before a disjoint internal blowup at
a smooth boundary point. Both orders use the actual residue-field center ideals. The
comparison preserves the projections to the one-step blowups, identifies the final
boundary ideals, and reindexes the two total exceptional classes. -/
theorem exists_iso_internal_nodal_blowup_interchange
    (D : X.IdealSheafData) [IsReduced D.subscheme]
    {p : X} {q' : (P[p]).blowup} (hp : IsClosed ({p} : Set X)) (hq' : IsClosed ({q'} : Set _))
    (haway : (P[p]).blowupToBase q' ≠ p) (hpD : p ∈ D.smoothBoundaryPoints s)
    (hqD : (St[P[p],D]).IsNodeOfReducedBoundary ((P[p]).blowupToBase ≫ s) q') :
    let I := P[p]
    let q := I.blowupToBase q'
    let J := P[q]
    let I' := I.comap J.blowupToBase
    let J' := J.comap I.blowupToBase
    let D' := (D.comap J.blowupToBase).radical
    ∃ (p' : J.blowup) (e : J'.blowup ≅ I'.blowup),
      IsClosed ({q} : Set X) ∧ D.IsNodeOfReducedBoundary s q ∧
      J' = P[q'] ∧ IsClosed ({p'} : Set J.blowup) ∧ J.blowupToBase p' = p ∧ I' = P[p'] ∧
      p' ∈ D'.smoothBoundaryPoints (J.blowupToBase ≫ s) ∧
      e.hom ≫ I.blowupMap J.blowupToBase = J'.blowupToBase ∧
      e.hom ≫ I'.blowupToBase = J.blowupMap I.blowupToBase ∧
      (St[I',D']).comap e.hom = ((St[I,D]).comap J'.blowupToBase).radical ∧
      LineBundleClass.pullback e.hom I'.blowupExceptionalClass =
        LineBundleClass.pullback J'.blowupToBase I.blowupExceptionalClass ∧
      LineBundleClass.pullback e.hom
        (LineBundleClass.pullback I'.blowupToBase J.blowupExceptionalClass) =
          J'.blowupExceptionalClass := by
  dsimp only
  let I := P[p]
  let q := I.blowupToBase q'
  let J := P[q]
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 s
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have hq : IsClosed ({q} : Set X) := by
    simpa only [q, Set.image_singleton] using I.blowupToBase.isClosedMap _ hq'
  have hIp : (I.support : Set X) = {p} := by
    rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hp.closure_eq]
  have hJq : (J.support : Set X) = {q} := by
    rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hq.closure_eq]
  have hqU : q ∉ I.support := by
    simpa only [← SetLike.mem_coe, hIp, Set.mem_singleton_iff] using haway
  have hpU : p ∈ J.support.compl := by
    simpa only [← SetLike.mem_coe, Closeds.coe_compl, hJq, Set.mem_compl_iff,
      Set.mem_singleton_iff] using haway.symm
  have hqIso : q ∈ I.blowupToBase.isoLocus :=
    I.blowupToBase.le_isoLocus_iff.mpr I.isIso_blowupToBase_restrict_compl_support hqU
  have hqD' := (isNodeOfReducedBoundary_ker_blowupMap_iff_of_notMem_support I D s hqU).mp hqD
  have hJ' := I.blowupToBase.comap_ker_fromSpecResidueField_of_mem_isoLocus hq hqIso
  obtain ⟨p', hp', hp'π, hI'⟩ :=
    J.blowupToBase.exists_comap_ker_fromSpecResidueField_of_isIso_morphismRestrict p hp _ hpU
  have hpIso : J.blowupToBase p' ∈ J.blowupToBase.isoLocus :=
    hp'π ▸ J.blowupToBase.le_isoLocus_iff.mpr J.isIso_blowupToBase_restrict_compl_support hpU
  have hsmooth := (D.mem_smoothBoundaryPoints_comap_iff_of_mem_isoLocus s _ hpIso).mpr (hp'π ▸ hpD)
  have hd : Disjoint (I.support : Set X) J.support := by
    simpa only [hIp, hJq, Set.disjoint_singleton] using haway.symm
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq s 2).mp inferInstance).2 q hq
  have : IsRegularLocalRing (X.presheaf.stalk q) := isRegularLocalRing_stalk_of_smooth s q
  have : IsReduced (J.comap J.blowupToBase).subscheme := by
    dsimp only [J]
    rw [Scheme.ker_fromSpecResidueField_eq_vanishingIdeal]
    exact @isReduced_of_isIntegral _ (isIntegral_exceptional_blowup_closed_point hdim hq)
  let J' := J.comap I.blowupToBase
  have : IsLocallyNoetherian I.blowup := LocallyOfFiniteType.isLocallyNoetherian I.blowupToBase
  have : IsReduced (J'.comap J'.blowupToBase).subscheme := by
    dsimp only [J']
    rw [hJ', Scheme.ker_fromSpecResidueField_eq_vanishingIdeal]
    exact @isReduced_of_isIntegral _
      (I.blowupToBase.isIntegral_exceptional_blowup_of_mem_isoLocus hdim hq' hqIso)
  let e := I.blowupCommOfDisjoint J hd
  refine ⟨p', e, hq, hqD', hJ', hp', hp'π, hI', ?_,
    I.blowupCommOfDisjoint_hom_blowupMap J hd, I.blowupCommOfDisjoint_hom_blowupToBase J hd,
    ?_, ?_, ?_⟩
  · rw [smoothBoundaryPoints_radical]
    exact hsmooth
  · apply comap_ker_blowupMap_reduced_total_blowupCommOfDisjoint I J D hd
    · exact (le_ker_fromSpecResidueField_iff_mem_support D hq).mpr
        (mem_support_of_isNodeOfReducedBoundary hqD')
    · rw [hJ']
      exact (le_ker_fromSpecResidueField_iff_mem_support _ hq').mpr
        (mem_support_of_isNodeOfReducedBoundary hqD)
  · rw [← pullback_blowupExceptionalClass_blowupMap I J.blowupToBase,
      LineBundleClass.pullback_comp, I.blowupCommOfDisjoint_hom_blowupMap J hd]
  · rw [LineBundleClass.pullback_comp, I.blowupCommOfDisjoint_hom_blowupToBase J hd,
      pullback_blowupExceptionalClass_blowupMap]

end Point

end AlgebraicGeometry.Scheme.IdealSheafData
