/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.AlgebraicGeometry.CartierDivisor.Support
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes
import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.CartierDivisor.BoundaryPrimes
import QPainleve.AlgebraicGeometry.Curves.Node.Order
import QPainleve.AlgebraicGeometry.IdealSheaf.Stalk
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Smooth
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced
import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Multiplicities of the total boundary under nodal blowups

For a tower of blowups at nodes of the reduced boundary, the total transform of the original
reduced divisor recovers the exceptional curves. At a prime divisor its multiplicity is at
least two exactly when the projection contracts that divisor. The calculation uses stalk
orders, so it applies to a tower starting at a self-node and to infinitely near centers.
-/

public section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsNodalBoundaryTower

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  {s : X ⟶ Spec (.of k)} [SmoothOfRelativeDimension 2 s]
  {D : X.IdealSheafData} {n : ℕ} {T : BlowupTower X n Y}

/-- The generic point of a prime divisor lies over the centre of a nodal tower exactly when
the total transform has multiplicity at least two there. -/
theorem mem_centre_iff_two_le_stalkOrder (hT : IsNodalBoundaryTower D s (𝟙 X) T)
    (hD : D.IsEffectiveCartier) (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (x : CodimensionOnePoint Y) :
    T.toBase x ∈ T.toBase.centre ↔ 2 ≤ (D.comap T.toBase).stalkOrder x := by
  have hred : IsReduced D.subscheme := hnodal.isReduced
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 s
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  constructor
  · intro hx
    obtain ⟨z, hz, hn⟩ := (D.isNodeOfReducedBoundary_iff_of_isReduced s _).mp
      (hT.centre_subset_nodes hx)
    let : X.Over (Spec (.of k)) := ⟨s⟩
    have : SmoothOfRelativeDimension 2 (X ↘ Spec (.of k)) := ‹SmoothOfRelativeDimension 2 s›
    let : D.subscheme.Over (Spec (.of k)) := ⟨D.subschemeι ≫ s⟩
    have : D.subschemeι.IsOver (Spec (.of k)) := ⟨rfl⟩
    have : SyntomicOfRelativeDimension 1 (D.subscheme ↘ Spec (.of k)) := hnodal.syntomic
    have hsing : z ∈ (D.subscheme.singularLocus k).support :=
      (D.subscheme.mem_support_singularLocus_iff_notMem_smoothLocus z).mpr
        ((Scheme.Hom.isNodeAt_iff_notMem_smoothLocus _ hnodal z).mp hn)
    have htwo := D.subschemeι.stalkOrder_eq_two_of_node
      (by simpa only [Scheme.IdealSheafData.ker_subschemeι] using hD) hnodal z hsing
    rw [Scheme.IdealSheafData.ker_subschemeι, hz] at htwo
    exact htwo.ge.trans (D.stalkOrder_le_comap T.toBase (x : Y))
  · intro hx
    by_contra h
    have ho : T.toBase x ∈ T.toBase.isoLocus := by simpa [Scheme.Hom.centre_def] using h
    have := T.toBase.isIso_stalkMap_of_mem_isoLocus ho
    rw [D.stalkOrder_comap_of_isIso_stalkMap] at hx
    let y : CodimensionOnePoint X :=
      ⟨T.toBase x, (T.toBase.coheight_eq_of_apply_mem_isoLocus ho).trans x.property⟩
    have : IsRegularLocalRing (X.presheaf.stalk (y : X)) := isRegularLocalRing_stalk_of_smooth s _
    have := CodimensionOnePoint.isDiscreteValuationRing_stalk y
    exact not_le_of_gt (by decide : (1 : ℕ∞) < 2)
      (hx.trans (hD.stalkOrder_le_one_of_isReduced (y : X)))

/-- The Weil coefficients of the total boundary transform detect the contracted prime
divisors of a nodal tower. -/
theorem mem_centre_iff_two_le_coeff_totalTransform [PerfectField k] [IsIntegral X] [IsNoetherian X]
    (hT : IsNodalBoundaryTower D s (𝟙 X) T)
    (hD : D.IsEffectiveCartier) (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (x : CodimensionOnePoint Y) :
    let := hT.isClosedPointTower.isIntegral s
    let := T.isNoetherian
    let := hT.isClosedPointTower.surjective s
    let hPullback := hD.comap_of_isDominant T.toBase
    T.toBase x ∈ T.toBase.centre ↔
      2 ≤ WeilDivisor.coeff hPullback.toCartierDivisor.toWeilDivisor x := by
  intro _ _ _ hPullback
  have hSmooth : Smooth (T.toBase ≫ s) :=
    (hT.isClosedPointTower.smoothOfRelativeDimension s).smooth
  have : IsRegularLocalRing (Y.presheaf.stalk (x : Y)) :=
    isRegularLocalRing_stalk_of_smooth (T.toBase ≫ s) _
  have := CodimensionOnePoint.isDiscreteValuationRing_stalk x
  have hfinite : (D.comap T.toBase).stalkOrder (x : Y) ≠ ⊤ := by
    rw [stalkOrder_def, ne_eq, Ideal.localOrder_eq_top_iff_eq_bot]
    exact hPullback.stalkIdeal_ne_bot _
  rw [hPullback.coeff_toWeilDivisor_eq_stalkOrder x,
    hT.mem_centre_iff_two_le_stalkOrder hD hnodal x]
  conv_lhs => rw [← ENat.natCast_toNat hfinite]
  exact ENat.natCast_le_natCast.trans (Int.ofNat_le).symm

/-- A prime of the total boundary survives the nodal contraction exactly when its
Weil multiplicity is one. -/
theorem toBase_mem_boundaryPrimes_iff_coeff_totalTransform_eq_one
    [PerfectField k] [IsIntegral X] [IsNoetherian X]
    (hT : IsNodalBoundaryTower D s (𝟙 X) T)
    (hD : D.IsEffectiveCartier) (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (p : (D.comap T.toBase).boundaryPrimes) :
    letI := hT.isClosedPointTower.isIntegral s
    letI := T.isNoetherian
    let htotal := hT.isClosedPointTower.isEffectiveCartier_totalTransform s hD
    T.toBase p.val ∈ D.boundaryPrimes ↔
      WeilDivisor.coeff htotal.toCartierDivisor.toWeilDivisor
        ((D.comap T.toBase).boundaryPrimeEmbedding p) = 1 := by
  intro htotal
  let : IsIntegral Y := hT.isClosedPointTower.isIntegral s
  let : IsNoetherian Y := T.isNoetherian
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 s
  have : IsRegular X := IsRegular.of_smooth s
  have := hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two s
  have : Smooth (T.toBase ≫ s) := (hT.isClosedPointTower.smoothOfRelativeDimension s).smooth
  have : IsRegular Y := IsRegular.of_smooth (T.toBase ≫ s)
  let x := (D.comap T.toBase).boundaryPrimeEmbedding p
  let W := htotal.toCartierDivisor.toWeilDivisor
  have hnonneg : 0 ≤ W :=
    (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
      htotal.isEffective_toCartierDivisor
  have hne : WeilDivisor.coeff W x ≠ 0 := by
    simpa only [x, IsEffectiveCartier.boundaryPrimesEquivWeilSupport_apply_val] using
      WeilDivisor.mem_support_iff.mp (htotal.boundaryPrimesEquivWeilSupport p).property
  have hpos : 0 < WeilDivisor.coeff W x := (hnonneg x).lt_of_ne hne.symm
  have hcentre : 2 ≤ WeilDivisor.coeff W x ↔ T.toBase p.val ∉ D.boundaryPrimes :=
    (hT.mem_centre_iff_two_le_coeff_totalTransform hD hnodal x).symm.trans
      (by simpa only [x, coe_boundaryPrimeEmbedding] using
        D.mem_centre_iff_notMem_boundaryPrimes_of_mem_boundaryPrimes_comap T.toBase p.property)
  have hweight : (¬ 2 ≤ WeilDivisor.coeff W x) ↔ WeilDivisor.coeff W x = 1 := by omega
  exact not_not.symm.trans ((not_congr hcentre.symm).trans hweight)

attribute [local instance] specializationOrder

/-- Nodal projections whose total boundary transforms correspond under an
isomorphism contract the same prime divisors under that isomorphism. -/
theorem exceptional_divisors_eq_of_totalTransform_eq {X' W : Scheme.{u}}
    {s' : X' ⟶ Spec (.of k)} [SmoothOfRelativeDimension 2 s']
    {D' : X'.IdealSheafData} {m : ℕ} {U : BlowupTower X' m W}
    (hT : IsNodalBoundaryTower D s (𝟙 X) T) (hU : IsNodalBoundaryTower D' s' (𝟙 X') U)
    (e : Y ≅ W)
    (hD : D.IsEffectiveCartier) (hD' : D'.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (D'.subschemeι ≫ s'))
    (h : D.comap T.toBase = (D'.comap U.toBase).comap e.hom)
    (x : Y) (hx : coheight x = 1) :
    T.toBase x ∈ T.toBase.centre ↔ U.toBase (e.hom x) ∈ U.toBase.centre := by
  have he := e.hom.isoLocus_eq_top_iff.mpr inferInstance
  have hxe : coheight (e.hom x) = 1 :=
    (e.hom.coheight_eq_of_apply_mem_isoLocus (x := x) (by simp [he])).trans hx
  rw [hT.mem_centre_iff_two_le_stalkOrder hD hnodal ⟨x, hx⟩,
    hU.mem_centre_iff_two_le_stalkOrder hD' hnodal' ⟨e.hom x, hxe⟩]
  exact Iff.of_eq (congrArg (fun J : Y.IdealSheafData ↦ 2 ≤ J.stalkOrder x) h) |>.trans
    (by rw [stalkOrder_comap_of_isIso_stalkMap])

end QPainleve.BlowupTower.IsNodalBoundaryTower
