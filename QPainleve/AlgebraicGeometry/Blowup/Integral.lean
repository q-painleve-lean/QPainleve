/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
public import Mathlib.AlgebraicGeometry.Properties
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.SchematicDensity
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint

/-!
# Integrality of blowups

A blowup of a Noetherian integral scheme along a center with nonempty complement is
integral. The isomorphism off the center identifies a schematically dense open of the
blowup with an integral open of the base.
In particular, this applies to the blowup of a closed point on a smooth integral surface.
-/

public section

open CategoryTheory Order TopologicalSpace
open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A blowup of a Noetherian integral scheme along a center with nonempty complement is integral. -/
theorem isIntegral_blowup_of_nonempty_compl_support {X : Scheme} [IsIntegral X] [IsNoetherian X]
    (I : X.IdealSheafData) (hU : Nonempty I.support.compl) : IsIntegral I.blowup := by
  let U : X.Opens := I.support.compl
  let e := asIso (I.blowupToBase ∣_ U)
  let j := (I.blowupToBase ⁻¹ᵁ U).ι
  have : Nonempty U := hU
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have : IsIntegral (I.blowupToBase ⁻¹ᵁ U).toScheme := IsIntegral.of_isIso e.inv
  have : IsNoetherian I.blowup := isNoetherian_of_finiteType I.blowupToBase
  have : IsSchemeTheoreticallyDominant j := by
    have hj :=
      I.isEffectiveCartier_comap_blowupToBase.isSchemeTheoreticallyDominant_support_compl_ι
    rwa [compl_support_comap] at hj
  have : IsReduced I.blowup := IsSchemeTheoreticallyDominant.isReduced j
  have : IrreducibleSpace I.blowup := by
    apply (irreducibleSpace_def _).2
    have h := ((IrreducibleSpace.isIrreducible_univ _).image j j.continuous.continuousOn).closure
    rwa [Set.image_univ, j.denseRange.closure_range] at h
  exact isIntegral_of_irreducibleSpace_of_isReduced _

variable {X : Scheme} {p : X}

local notation "Iₚ" =>
  vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)

/-- The blowup of a closed point on a quasi-compact integral smooth surface over a field
is integral. -/
theorem isIntegral_blowup_closed_point {k : Type*} [Field k] [IsIntegral X]
    (g : X ⟶ Spec (.of k)) [QuasiCompact g] [SmoothOfRelativeDimension 2 g]
    (hp : IsClosed ({p} : Set X)) : IsIntegral (Iₚ).blowup := by
  have : Smooth g := SmoothOfRelativeDimension.smooth 2 g
  have : IsNoetherian X := isNoetherian_of_finiteType g
  have hcod := coheight_eq_of_isClosed_of_smoothOfRelativeDimension g (n := 2) hp
  have hgen : coheight (genericPoint X) = 0 :=
    coheight_eq_zero.mpr Scheme.isMax_genericPoint
  apply isIntegral_blowup_of_nonempty_compl_support
  refine ⟨⟨genericPoint X, ?_⟩⟩
  have hs : ((Iₚ).support : Set X) = {p} :=
    (coe_support_vanishingIdeal _).trans hp.closure_eq
  rw [← SetLike.mem_coe, Closeds.coe_compl, Set.mem_compl_iff, hs, Set.mem_singleton_iff]
  intro h
  rw [h, hcod] at hgen
  norm_num at hgen

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme

/-- Blowing up the reduced closure of a non-generic point of a Noetherian integral scheme
gives an integral scheme. -/
theorem isIntegral_pointBlowup (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (p : X) (hp : p ≠ genericPoint X) : IsIntegral (X.fromSpecResidueField p).ker.blowup := by
  apply (X.fromSpecResidueField p).ker.isIntegral_blowup_of_nonempty_compl_support
  refine ⟨genericPoint X, ?_⟩
  rw [← SetLike.mem_coe, Closeds.coe_compl, Set.mem_compl_iff, Scheme.Hom.support_ker,
    range_fromSpecResidueField, ← specializes_iff_mem_closure]
  exact fun h ↦ hp (h.antisymm (genericPoint_specializes p)).eq

end AlgebraicGeometry.Scheme
