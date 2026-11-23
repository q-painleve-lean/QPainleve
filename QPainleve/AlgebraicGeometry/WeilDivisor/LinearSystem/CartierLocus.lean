/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.WeilDivisor.LinearSystem.BaseIdeal
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# The Cartier locus of a linear-system base ideal

The fixed divisor contributes a Cartier factor to the base ideal. Removing it
leaves an ideal whose support contains no codimension-one point. Thus the
original base ideal is locally effective Cartier precisely off the base locus
of the moving system. The comparison uses `IsEffectiveCartier.colon` to cancel
the fixed divisor on each open.
-/

public section

open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry.SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

/-- The restriction of a base ideal to an open is effective Cartier precisely
when the open misses the support of the moving base ideal. -/
theorem isEffectiveCartier_comap_baseIdeal_iff {S : Set (SchemeWeilDivisor X)}
    (hS : ∀ D ∈ S, 0 ≤ D) (hne : S.Nonempty) (U : X.Opens) :
    let M := baseIdeal (WeilDivisor.movingPart S hne hS)
      (fun _ ↦ WeilDivisor.nonneg_of_mem_movingPart hne hS)
    ((baseIdeal S hS).comap U.ι).IsEffectiveCartier ↔ Disjoint (U : Set X) (M.support : Set X) := by
  intro M
  let D : SchemeWeilDivisor X := WeilDivisor.fixedPart S hne hS
  let F := D.idealSheaf (WeilDivisor.fixedPart_nonneg hne hS)
  have hF : (F.comap U.ι).IsEffectiveCartier :=
    (D.isEffectiveCartier_idealSheaf (WeilDivisor.fixedPart_nonneg hne hS)).comap U.ι
  have hfactor : (baseIdeal S hS).comap U.ι = M.comap U.ι * F.comap U.ι := by
    rw [baseIdeal_eq_mul_movingPart hS hne, comap_mul, mul_comm]
  rw [hfactor]
  constructor
  · intro h
    have hM := h.colon hF.locallyPrincipal (fun _ ↦ Ideal.mul_le_right)
    rw [hF.mul_colon_cancel_right] at hM
    refine Set.disjoint_left.mpr fun x hxU hxM ↦ ?_
    have hx : (⟨x, hxU⟩ : U.toScheme) ∈ ((M.comap U.ι).support : Set U.toScheme) := by
      rw [support_comap, Closeds.coe_preimage]
      exact hxM
    obtain ⟨p, hp, _⟩ := hM.mem_support_iff_exists_codimensionOnePoint.mp hx
    apply notMem_support_baseIdeal_movingPart hS hne (p.mapOfIsOpenImmersion U.ι)
    rw [CodimensionOnePoint.coe_mapOfIsOpenImmersion]
    rwa [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage] at hp
  · intro h
    have hM : M.comap U.ι = ⊤ := (comap_eq_top_iff _ _).mpr <| top_unique fun x _ ↦
      Set.disjoint_left.mp h x.property
    rw [hM, top_mul]
    exact hF

end TauCeti.AlgebraicGeometry.SchemeWeilDivisor
