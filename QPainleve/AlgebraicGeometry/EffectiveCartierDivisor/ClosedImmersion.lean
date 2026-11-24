/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Factorial
import QPainleve.AlgebraicGeometry.IdealSheaf.ClosedImmersion
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint.Basic
import TauCeti.Topology.KrullDimension.Irreducible

/-!
# Curves and closed points as effective Cartier divisors

The ideal of a closed integral curve on a regular integral surface is effective
Cartier. The dimension formula identifies the image of the generic point as a
codimension-one point, and reducedness identifies the ideal of the immersion
with the vanishing ideal of that point's closure. On an irreducible regular curve,
the reduced ideal of a closed point is effective Cartier.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An integral closed curve on a regular integral surface over a field is an
effective Cartier divisor, with the ideal of the given closed immersion. -/
public theorem isEffectiveCartier_ker_of_isRegular_of_dim_eq_two
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C]
    (k : Type u) [Field k] [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [IrreducibleSpace X] [IsRegular X] (hX : topologicalKrullDim X = 2)
    (hC : topologicalKrullDim C = 1) : i.ker.IsEffectiveCartier := by
  rw [i.ker_eq_vanishingIdeal_closure_genericPoint]
  exact IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular
    (fun x ↦ WithBot.coe_le_coe.mp ((coheight_le_topologicalKrullDim x).trans_eq hX))
    (i.coheight_apply_genericPoint_eq_one_of_dim_eq_two k hX hC)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

/-- The reduced ideal of a closed point on a one-dimensional irreducible regular scheme
is effective Cartier. -/
public theorem isEffectiveCartier_ker_fromSpecResidueField_of_dim_eq_one
    {X : Scheme.{u}} [IrreducibleSpace X] [TauCeti.AlgebraicGeometry.IsRegular X]
    {p : X} (hp : IsClosed ({p} : Set X)) (hX : topologicalKrullDim X = 1) :
    (X.fromSpecResidueField p).ker.IsEffectiveCartier := by
  have hp' : p ≠ genericPoint X := by
    intro he
    have hset : ({p} : Set X) = Set.univ :=
      hp.closure_eq.symm.trans (he ▸ genericPoint_closure X)
    have hsub : Subsingleton X := Set.subsingleton_univ_iff.mp
      (hset ▸ Set.subsingleton_singleton)
    exact zero_ne_one
      ((TauCeti.topologicalKrullDim_eq_zero_iff_subsingleton.mpr hsub).symm.trans hX)
  rw [X.ker_fromSpecResidueField_eq_vanishingIdeal]
  have hcodim :=
    (TauCeti.AlgebraicGeometry.Scheme.coheight_eq_one_iff_ne_genericPoint hX.le).mpr hp'
  refine IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular
    (fun x ↦ ?_) hcodim
  have hx := (coheight_le_topologicalKrullDim x).trans_eq hX
  exact (WithBot.coe_le_coe.mp hx).trans (by decide)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

/-- A reduced closed point pulls back along a regular integral curve embedded in the
ambient scheme to an effective Cartier divisor. -/
public theorem isEffectiveCartier_comap_ker_fromSpecResidueField
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] [IrreducibleSpace C]
    [IsRegular C] (hC : topologicalKrullDim C = 1)
    {p : X} (hp : IsClosed ({p} : Set X)) :
    ((X.fromSpecResidueField p).ker.comap i).IsEffectiveCartier := by
  by_cases h : p ∈ Set.range i
  · obtain ⟨q, rfl⟩ := h
    rw [i.comap_ker_fromSpecResidueField_apply]
    apply C.isEffectiveCartier_ker_fromSpecResidueField_of_dim_eq_one _ hC
    simpa only [← Set.image_singleton, i.isClosedEmbedding.injective.preimage_image] using
      hp.preimage i.continuous
  · have htop : (X.fromSpecResidueField p).ker.comap i = ⊤ := by
      rw [IdealSheafData.comap_eq_top_iff, ← Opens.coe_eq_univ, Hom.coe_preimage,
        Closeds.coe_compl, X.support_ker_fromSpecResidueField_of_isClosed hp]
      exact Set.eq_univ_of_forall fun q hq ↦ h ⟨q, hq⟩
    rw [htop]
    exact IdealSheafData.isEffectiveCartier_top C

end AlgebraicGeometry.Scheme.Hom
