/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Curves.Node.Order
import QPainleve.AlgebraicGeometry.IdealSheaf.Stalk
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Smooth
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced
import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk

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

attribute [local instance] specializationOrder

/-- Two nodal projections from the same model with equal total boundary transforms contract
the same prime divisors. -/
theorem exceptional_divisors_eq_of_totalTransform_eq {X' : Scheme.{u}}
    {s' : X' ⟶ Spec (.of k)} [SmoothOfRelativeDimension 2 s']
    {D' : X'.IdealSheafData} {m : ℕ} {U : BlowupTower X' m Y}
    (hT : IsNodalBoundaryTower D s (𝟙 X) T) (hU : IsNodalBoundaryTower D' s' (𝟙 X') U)
    (hD : D.IsEffectiveCartier) (hD' : D'.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (D'.subschemeι ≫ s'))
    (h : D.comap T.toBase = D'.comap U.toBase) :
    {x : Y | T.toBase x ∈ T.toBase.centre ∧ coheight x = 1} =
      {x : Y | U.toBase x ∈ U.toBase.centre ∧ coheight x = 1} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  apply and_congr_left
  intro hx
  exact (hT.mem_centre_iff_two_le_stalkOrder hD hnodal ⟨x, hx⟩).trans
    (h ▸ (hU.mem_centre_iff_two_le_stalkOrder hD' hnodal' ⟨x, hx⟩).symm)

end QPainleve.BlowupTower.IsNodalBoundaryTower
