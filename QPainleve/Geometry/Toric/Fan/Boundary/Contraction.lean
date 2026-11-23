/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
public import QPainleve.Geometry.Toric.Fan.Boundary.Prime
public import QPainleve.Geometry.Toric.Fan.Boundary.Valuation

import QPainleve.AlgebraicGeometry.OrderOfVanishing.IsoLocus
import TauCeti.Geometry.Toric.Algebraic.Fan.Normal

/-!
# Boundary orders on contracted toric models

Every prime of the contracted boundary determines a strict ray prime on the ordered
internal blowup model. Its valuation is the toric ray valuation on rational functions
identified by the two projections. For finite-index charges this identifies the
boundary component from the orders of the scaled charge characters.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] (hΦ : Φ.IsRegular)
  (b : Module.Basis (Fin 2) ℤ N) {n : ℕ} (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ)

local notation "P" => internalBlowupTower b s c
local notation "B" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd P))
local notation "π" => toBase (WithBoundary.toTower (Sigma.snd P))
local notation "F" => Φ.algebraicRealization

variable {X : Scheme} [IsIntegral X] [IsNormalScheme X] [IsLocallyNoetherian X]
  {D : X.IdealSheafData} (p : (internalBlowupTower b s c).1 ⟶ X) [IsModification p]
  (hD : (D.comap p).support =
    (Scheme.Hom.ker (WithBoundary.boundaryι (internalBlowupTower b s c).2)).support)

include hΦ hD in
private theorem bijOn_contractedBoundaryPrimes :
    Set.BijOn p ((B).boundaryPrimes ∩ p ⁻¹' (p.isoLocus : Set X)) D.boundaryPrimes := by
  have := isIntegral_internalBlowupTower b s c hΦ
  have hsub : D.boundaryPrimes ⊆ (p.isoLocus : Set X) :=
    fun _ hx ↦ p.mem_isoLocus_of_coheight_eq_one (mem_boundaryPrimes.mp hx).2
  rw [← boundaryPrimes_eq_of_support_eq hD]
  simpa only [Set.inter_eq_left.mpr hsub] using
    D.bijOn_boundaryPrimes_comap_of_subset_isoLocus p (U := p.isoLocus) Set.Subset.rfl

local notation "E" => Set.BijOn.equiv p (bijOn_contractedBoundaryPrimes hΦ b s c p hD)
local notation "R" => internalBlowupBoundaryPrimeEquiv hΦ b s c

/-- The boundary primes on a contraction of an ordered toric model embed into the rays of
the presenting fan by taking strict transforms. The omitted rays have image outside the
isomorphism locus of the contraction. -/
def contractedBoundaryRayEmbedding : D.boundaryPrimes ↪ Φ.Ray :=
  ((E).symm.toEmbedding.trans
    ⟨Set.inclusion Set.inter_subset_left, Set.inclusion_injective Set.inter_subset_left⟩).trans
    (R).symm.toEmbedding

/-- The ray assigned to a contracted boundary prime projects to that prime from the
ordered model. -/
@[simp]
theorem contraction_internalBlowupBoundaryPrimeEquiv (x : D.boundaryPrimes) :
    p ((R) (contractedBoundaryRayEmbedding hΦ b s c p hD x)).val = x.val := by
  have h : p ((E).symm x).val = x.val := congrArg Subtype.val ((E).apply_symm_apply x)
  simpa only [contractedBoundaryRayEmbedding, Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply, Equiv.apply_symm_apply, Function.Embedding.coeFn_mk,
    Set.inclusion] using h

/-- A ray represents a boundary prime of the contraction exactly when its strict prime
on the ordered model maps to that prime. -/
theorem contractedBoundaryRayEmbedding_eq_iff (x : D.boundaryPrimes) (ρ : Φ.Ray) :
    contractedBoundaryRayEmbedding hΦ b s c p hD x = ρ ↔ p ((R) ρ).val = x.val := by
  constructor
  · rintro rfl
    exact contraction_internalBlowupBoundaryPrimeEquiv hΦ b s c p hD x
  · intro h
    have := isIntegral_internalBlowupTower b s c hΦ
    have hx := p.mem_isoLocus_of_coheight_eq_one (mem_boundaryPrimes.mp x.property).2
    have h' := contraction_internalBlowupBoundaryPrimeEquiv hΦ b s c p hD x
    apply (R).injective
    apply Subtype.ext
    exact p.injOn_preimage_isoLocus (Set.mem_preimage.mpr (h'.symm ▸ hx))
      (Set.mem_preimage.mpr (h.symm ▸ hx)) (h'.trans h.symm)

local notation "ρₓ" x:arg => contractedBoundaryRayEmbedding hΦ b s c p hD x

/-- A function on the toric surface, transported to the contraction via the ordered
model, has the same order along a contracted boundary prime as along its presenting ray. -/
theorem ord_contracted_toric_boundary (x : D.boundaryPrimes) (a : (F).functionField) :
    let := isIntegral_internalBlowupTower b s c hΦ
    let := isModification_internalBlowupTower_toBase b s c hΦ
    let := p.isIso_functionFieldMap_of_isModification
    X.ord (CategoryTheory.inv p.functionFieldMap ((π).functionFieldMap a)) x.val =
      (F).ord a (Φ.rayBoundaryPoint hΦ (ρₓ x)).val := by
  intro _ _ _
  have : IsNoetherian (P).1 := (WithBoundary.toTower (Sigma.snd P)).isNoetherian
  let y := ((R) (ρₓ x)).val
  have hpy : p y = x.val := contraction_internalBlowupBoundaryPrimeEquiv hΦ b s c p hD x
  have hπy : π y = (Φ.rayBoundaryPoint hΦ (ρₓ x)).val :=
    toBase_internalBlowupBoundaryPrimeEquiv hΦ b s c _
  have hp := p.mem_isoLocus_of_coheight_eq_one (mem_boundaryPrimes.mp x.property).2
  have hπ := (π).mem_isoLocus_of_coheight_eq_one (Φ.rayBoundaryPoint hΦ (ρₓ x)).property
  rw [← hpy, ← p.ord_functionFieldMap_of_mem_isoLocus (hpy.symm ▸ hp), IsIso.inv_hom_id_apply]
  rw [(π).ord_functionFieldMap_of_mem_isoLocus (hπy.symm ▸ hπ), hπy]

local notation "Xchar" l:arg =>
  algebraMap ℂ (Scheme.functionField F) (c l : ℂ) *
    Φ.character (ofAdd (LinearMap.toAddMonoidHom (b.detDualEquiv (Ray.primitiveGenerator (s l)))))

/-- The orders of the scaled charge functions on the contraction are the determinant
order vector of the corresponding ray. -/
theorem ord_contracted_toric_boundary_chargeCharacter (x : D.boundaryPrimes) (l : Fin n) :
    let := isIntegral_internalBlowupTower b s c hΦ
    let := isModification_internalBlowupTower_toBase b s c hΦ
    let := p.isIso_functionFieldMap_of_isModification
    X.ord (CategoryTheory.inv p.functionFieldMap ((π).functionFieldMap (Xchar l))) x.val =
      rayBoundaryOrders b s (ρₓ x) l := by
  intro _ _ _
  rw [ord_contracted_toric_boundary hΦ b s c p hD, ord_rayBoundaryPoint_chargeCharacter]

/-- Searching the rays of a numbered contracted boundary recovers the index of a prime
exactly when its scaled charge functions have the specified orders. The finite-index
condition makes that index unique. -/
theorem boundaryRayOfOrders_eq_some_iff_ord_contracted
    {m : ℕ} (boundary : Fin m ↪ D.boundaryPrimes) (orders : Fin n → ℤ)
    (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0) (j : Fin m) :
    let := isIntegral_internalBlowupTower b s c hΦ
    let := isModification_internalBlowupTower_toBase b s c hΦ
    let := p.isIso_functionFieldMap_of_isModification
    boundaryRayOfOrders b s (boundary.trans (contractedBoundaryRayEmbedding hΦ b s c p hD))
      orders = some j ↔ ∀ l,
      X.ord (CategoryTheory.inv p.functionFieldMap ((π).functionFieldMap (Xchar l)))
        (boundary j).val = orders l := by
  intro _ _ _
  rw [boundaryRayOfOrders_eq_some_iff _ _ _ _ hindex]
  simp only [ord_contracted_toric_boundary_chargeCharacter hΦ b s c p hD,
    Function.Embedding.trans_apply, funext_iff]

end TauCeti.Toric.Fan
