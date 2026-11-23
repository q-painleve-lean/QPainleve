/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes
public import QPainleve.Geometry.Toric.Fan.InternalBlowup

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
import QPainleve.Geometry.Toric.Fan.Boundary.Component
import TauCeti.Geometry.Toric.Algebraic.Fan.Normal

/-!
# Ray primes of ordered toric blowups

The strict boundary of an ordered internal blowup has one prime for every ray.
The projection identifies it with the original toric prime over the isomorphism locus,
including in presentations with repeated or infinitely near centers.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TopologicalSpace
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N)
  {n : ℕ} (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ)

local notation "P" => internalBlowupTower b s c
local notation "j" => WithBoundary.boundaryι (Sigma.snd P)
local notation "π" => toBase (WithBoundary.toTower (Sigma.snd P))
local notation "d" ρ:arg => Φ.rayBoundaryIdeal hΦ ρ
local notation "e" ρ:arg => Ray.boundaryComponentι ρ hΦ ≫ j

private theorem rayBoundaryIdeal_genericPoint (ρ : Φ.Ray) :
    (d ρ).subschemeι (genericPoint (d ρ).subscheme) = Φ.rayBoundaryPoint hΦ ρ := by
  symm
  apply (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ).mem_support_iff_eq_subschemeι_genericPoint
    (Φ.rayBoundaryPoint hΦ ρ).property |>.mp
  rw [← SetLike.mem_coe, coe_support_rayBoundaryIdeal]
  exact subset_closure (Set.mem_singleton _)

variable [Nonempty Φ.cones]

private theorem toBase_rayComponent_genericPoint (ρ : Φ.Ray) :
    π ((e ρ) (genericPoint (d ρ).subscheme)) = Φ.rayBoundaryPoint hΦ ρ := by
  rw [← Scheme.Hom.comp_apply, Category.assoc, WithBoundary.boundaryι_toBase,
    Ray.boundaryComponentι_subschemeι, rayBoundaryIdeal_genericPoint]

private def internalBlowupRayPoint (ρ : Φ.Ray) : CodimensionOnePoint (P).1 := by
  have := isIntegral_internalBlowupTower b s c hΦ
  have := isModification_internalBlowupTower_toBase b s c hΦ
  let x := (e ρ) (genericPoint (d ρ).subscheme)
  have hπ : π x = (Φ.rayBoundaryPoint hΦ ρ).val := toBase_rayComponent_genericPoint hΦ b s c ρ
  have hx : Order.coheight (π x) = 1 := hπ.symm ▸ (Φ.rayBoundaryPoint hΦ ρ).property
  exact ⟨x, ((π).coheight_eq_of_apply_mem_isoLocus
    ((π).mem_isoLocus_of_coheight_eq_one hx)).symm.trans hx⟩

private theorem support_internalBlowup_boundary : ((j).ker.support : Set (P).1) =
    ⋃ ρ : Φ.Ray, closure {(internalBlowupRayPoint hΦ b s c ρ : (P).1)} := by
  rw [(j).support_ker, (j).isClosedEmbedding.isClosed_range.closure_eq, ← Set.image_univ (f := j),
    ← iUnion_range_boundaryComponentι hΦ, Set.image_iUnion]
  refine Set.iUnion_congr fun ρ ↦ ?_
  rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
    ← Set.image_univ (f := e ρ), ← genericPoint_closure,
    ← (e ρ).isClosedEmbedding.closure_image_eq,
    Set.image_singleton]
  rfl

/-- The rays index the prime components of the strict boundary of the ordered internal
blowup. The comparison uses the same labeled ray divisors for every center tuple. -/
def internalBlowupBoundaryPrimeEquiv : Φ.Ray ≃ (j).ker.boundaryPrimes := by
  have hr := (j).ker.boundaryPrimes_eq_range_of_iUnion_closure _
    (support_internalBlowup_boundary hΦ b s c)
  refine Equiv.ofBijective (fun ρ ↦ ⟨internalBlowupRayPoint hΦ b s c ρ, ?_⟩) ⟨?_, ?_⟩
  · rw [hr]
    exact Set.mem_range_self ρ
  · intro ρ τ h
    apply Φ.rayBoundaryPoint_injective hΦ
    apply Subtype.ext
    exact (toBase_rayComponent_genericPoint hΦ b s c ρ).symm.trans
      ((congrArg (fun x : (j).ker.boundaryPrimes ↦ π x.val) h).trans
        (toBase_rayComponent_genericPoint hΦ b s c τ))
  · intro x
    obtain ⟨ρ, hρ⟩ := (Set.ext_iff.mp hr x.val).mp x.property
    exact ⟨ρ, Subtype.ext hρ⟩

/-- The strict boundary prime indexed by a ray projects to the original toric ray prime. -/
@[simp]
theorem toBase_internalBlowupBoundaryPrimeEquiv (ρ : Φ.Ray) :
    π (internalBlowupBoundaryPrimeEquiv hΦ b s c ρ).val = Φ.rayBoundaryPoint hΦ ρ :=
  toBase_rayComponent_genericPoint hΦ b s c ρ

end TauCeti.Toric.Fan
