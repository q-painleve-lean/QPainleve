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

/-!
# Ray primes of ordered toric blowups

The strict boundary of an ordered internal blowup has one prime for every ray.
The projection identifies it with the original toric prime over the isomorphism locus,
including in presentations with repeated or infinitely near centers.
An isomorphism identifying the strict boundary with another boundary transports
the same ray indexing to that boundary.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TopologicalSpace
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

universe u

variable (k : Type u) [Field k] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N)
  {n : ℕ} (s : Fin n → Φ.Ray) (c : Fin n → kˣ)

local notation "P" => internalBlowupTower k b s c
local notation "j" => WithBoundary.boundaryι (Sigma.snd P)
local notation "π" => toBase (WithBoundary.toTower (Sigma.snd P))
local notation "d" ρ:arg => Φ.rayDivisorIdeal k hΦ ρ
local notation "e" ρ:arg => Ray.boundaryComponentι k ρ hΦ ≫ j

private theorem rayBoundaryIdeal_genericPoint (ρ : Φ.Ray) :
    (d ρ).subschemeι (genericPoint (d ρ).subscheme) = Φ.rayBoundaryChartPoint (R := k) hΦ ρ := by
  symm
  apply (Φ.isEffectiveCartier_rayDivisorIdeal k hΦ ρ).mem_support_iff_eq_subschemeι_genericPoint
    (Φ.rayBoundaryChartPoint (R := k) hΦ ρ).property |>.mp
  rw [← SetLike.mem_coe, coe_support_rayDivisorIdeal k]
  exact subset_closure (Set.mem_singleton _)

variable [Nonempty Φ.cones]

private theorem toBase_rayComponent_genericPoint (ρ : Φ.Ray) :
    π ((e ρ) (genericPoint (d ρ).subscheme)) = Φ.rayBoundaryChartPoint (R := k) hΦ ρ := by
  rw [← Scheme.Hom.comp_apply, Category.assoc, WithBoundary.boundaryι_toBase,
    Ray.boundaryComponentι_subschemeι k, rayBoundaryIdeal_genericPoint k]

variable [PerfectField k]

private def internalBlowupRayPoint (ρ : Φ.Ray) : CodimensionOnePoint (P).1 := by
  have := isIntegral_internalBlowupTower k b s c hΦ
  have := isModification_internalBlowupTower_toBase k b s c hΦ
  have := Φ.isNormalScheme_finiteFanScheme (R := k) hΦ
  let x := (e ρ) (genericPoint (d ρ).subscheme)
  have hπ : π x = (Φ.rayBoundaryChartPoint (R := k) hΦ ρ).val :=
    toBase_rayComponent_genericPoint k hΦ b s c ρ
  have hx : Order.coheight (π x) = 1 := hπ.symm ▸ (Φ.rayBoundaryChartPoint (R := k) hΦ ρ).property
  exact ⟨x, ((π).coheight_eq_of_apply_mem_isoLocus
    ((π).mem_isoLocus_of_coheight_eq_one hx)).symm.trans hx⟩

private theorem range_rayComponent_internalBlowupRayPoint (ρ : Φ.Ray) :
    Set.range (e ρ) = closure {(internalBlowupRayPoint k hΦ b s c ρ : (P).1)} := by
  rw [← Set.image_univ (f := e ρ), ← genericPoint_closure,
    ← (e ρ).isClosedEmbedding.closure_image_eq, Set.image_singleton]
  rfl

private theorem support_internalBlowup_boundary : ((j).ker.support : Set (P).1) =
    ⋃ ρ : Φ.Ray, closure {(internalBlowupRayPoint k hΦ b s c ρ : (P).1)} := by
  rw [(j).support_ker, (j).isClosedEmbedding.isClosed_range.closure_eq, ← Set.image_univ (f := j),
    ← iUnion_range_boundaryComponentι k hΦ, Set.image_iUnion]
  refine Set.iUnion_congr fun ρ ↦ ?_
  rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base]
  exact range_rayComponent_internalBlowupRayPoint k hΦ b s c ρ

/-- The rays index the prime components of the strict boundary of the ordered internal
blowup. The comparison uses the same labeled ray divisors for every center tuple. -/
def internalBlowupBoundaryPrimeEquiv : Φ.Ray ≃ (j).ker.boundaryPrimes := by
  have hr := (j).ker.boundaryPrimes_eq_range_of_iUnion_closure _
    (support_internalBlowup_boundary k hΦ b s c)
  refine Equiv.ofBijective (fun ρ ↦ ⟨internalBlowupRayPoint k hΦ b s c ρ, ?_⟩) ⟨?_, ?_⟩
  · rw [hr]
    exact Set.mem_range_self ρ
  · intro ρ τ h
    apply Φ.rayBoundaryChartPoint_injective (R := k) hΦ
    apply Subtype.ext
    exact (toBase_rayComponent_genericPoint k hΦ b s c ρ).symm.trans
      ((congrArg (fun x : (j).ker.boundaryPrimes ↦ π x.val) h).trans
        (toBase_rayComponent_genericPoint k hΦ b s c τ))
  · intro x
    obtain ⟨ρ, hρ⟩ := (Set.ext_iff.mp hr x.val).mp x.property
    exact ⟨ρ, Subtype.ext hρ⟩

/-- The embedded ray component is the closure of the corresponding strict boundary prime. -/
theorem range_rayComponent_internalBlowupBoundaryPrimeEquiv (ρ : Φ.Ray) :
    Set.range (e ρ) = closure {((internalBlowupBoundaryPrimeEquiv k hΦ b s c ρ).val : (P).1)} :=
  range_rayComponent_internalBlowupRayPoint k hΦ b s c ρ

/-- The strict boundary is the union of the closures of the labeled ray primes. -/
theorem coe_support_ker_boundaryι_eq_iUnion_closure :
    ((j).ker.support : Set (P).1) =
      ⋃ ρ : Φ.Ray, closure {((internalBlowupBoundaryPrimeEquiv k hΦ b s c ρ).val : (P).1)} :=
  support_internalBlowup_boundary k hΦ b s c

/-- The strict boundary prime indexed by a ray projects to the original toric ray prime. -/
@[simp]
theorem toBase_internalBlowupBoundaryPrimeEquiv (ρ : Φ.Ray) :
    π (internalBlowupBoundaryPrimeEquiv k hΦ b s c ρ).val = Φ.rayBoundaryChartPoint (R := k) hΦ ρ :=
  toBase_rayComponent_genericPoint k hΦ b s c ρ

section Iso

variable {X : Scheme.{u}} {D : X.IdealSheafData}
  (g : (internalBlowupTower k b s c).1 ≅ X)
  (hg : (D.comap g.hom).support = (internalBlowupTower k b s c).2.boundaryι.ker.support)

/-- Index the primes of a boundary with the same support as the strict boundary, transported
along the model isomorphism, by the rays of the ordered toric model. -/
def internalBlowupBoundaryPrimeEquivOfIso : Φ.Ray ≃ D.boundaryPrimes :=
  (internalBlowupBoundaryPrimeEquiv k hΦ b s c).trans
    ((Set.equivOfEq (boundaryPrimes_eq_of_support_eq hg.symm)).trans (D.boundaryPrimesEquivOfIso g))

/-- The transported prime is the image of the strict boundary prime under the isomorphism. -/
@[simp]
theorem internalBlowupBoundaryPrimeEquivOfIso_apply_val (ρ : Φ.Ray) :
    (internalBlowupBoundaryPrimeEquivOfIso k hΦ b s c g hg ρ).val =
      g.hom (internalBlowupBoundaryPrimeEquiv k hΦ b s c ρ).val := by
  simp [internalBlowupBoundaryPrimeEquivOfIso]

/-- The strict boundary prime of the recovered ray is the inverse image of the given prime. -/
@[simp]
theorem internalBlowupBoundaryPrimeEquivOfIso_symm_apply_val (x : D.boundaryPrimes) :
    (internalBlowupBoundaryPrimeEquiv k hΦ b s c
      ((internalBlowupBoundaryPrimeEquivOfIso k hΦ b s c g hg).symm x)).val = g.inv x.val := by
  simp [internalBlowupBoundaryPrimeEquivOfIso]

/-- The image of a ray component is the closure of its transported prime. -/
theorem range_rayComponent_internalBlowupBoundaryPrimeEquivOfIso (ρ : Φ.Ray) :
    Set.range ((e ρ) ≫ g.hom) =
      closure {((internalBlowupBoundaryPrimeEquivOfIso k hΦ b s c g hg ρ).val : X)} := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    range_rayComponent_internalBlowupBoundaryPrimeEquiv k hΦ b s c ρ,
    ← g.hom.isClosedEmbedding.closure_image_eq, Set.image_singleton,
    internalBlowupBoundaryPrimeEquivOfIso_apply_val]

end Iso

end TauCeti.Toric.Fan
