/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.Support
public import QPainleve.Geometry.Toric.Fan.Picard.WeightedBoundary
public import QPainleve.SignedClusterModularGroup.Realization.Agreement
public import QPainleve.SignedClusterModularGroup.Realization.Boundary

/-!
# Total boundary exponents in a contracted toric presentation

The class of the boundary downstairs pulls back to a weighted sum of the strict
toric boundary upstairs. The resulting charge coordinates are the multiplicities
at the rays of the ordered centers, including those on contracted rays.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open QPainleve.CharacterTorus TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData LineBundleClass

namespace QPainleve.SignedClusterModularGroup.ContractedToricFiber

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n] {L : Type} [AddCommGroup L]
  {B : LinearMap.BilinForm ℤ L} {b : Module.Basis (Fin 2) ℤ N}
  {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Dtor[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))

variable [PrestableFamily (Dtor[Φ,h₀] ↘ S)] {γ : Type*}
  {a : γ → (Dtor[Φ,h₀] ↘ S).smoothLocus}
  {T : NodalCycleNumbering a m} {origin : ZMod m}
  {ι : L →ₗ[ℤ] (Additive (LineBundleClass Φ.algebraicRealization) × (Fin r → ℤ))}
  {c : Multiplicative (Fin r → ℤ) →* ℂˣ} {M : MarkedSurface ℂ n B (scheme ℂ (Fin r →₀ ℤ))}
  (p : ContractedToricFiber b s hΦ T origin ι c M)

local notation "center" => (fun j : Fin r ↦ c (ofAdd (Pi.single j 1)))

/-- The Weil multiplicity of the total transform of the boundary along a strict toric ray. -/
def totalBoundaryRayMultiplicity (hD : D[M].IsEffectiveCartier) (ρ : Φ.Ray) : ℤ :=
  letI := Fan.isIntegral_internalBlowupTower b s center hΦ
  letI := M.integral
  Fan.internalBlowupRayMultiplicity hΦ b s center (hD.comap_of_isDominant p.projection) ρ

/-- The contracted boundary multiplicity is the ray coefficient of the pulled-back divisor. -/
theorem totalBoundaryRayMultiplicity_def (hD : D[M].IsEffectiveCartier) (ρ : Φ.Ray) :
    letI := Fan.isIntegral_internalBlowupTower b s center hΦ
    letI := M.integral
    p.totalBoundaryRayMultiplicity hD ρ =
      Fan.internalBlowupRayMultiplicity hΦ b s center (hD.comap_of_isDominant p.projection) ρ :=
  (rfl)

/-- Every ray of the strict toric boundary occurs in the total transform. -/
theorem totalBoundaryRayMultiplicity_pos (hD : D[M].IsEffectiveCartier) (ρ : Φ.Ray) :
    0 < p.totalBoundaryRayMultiplicity hD ρ := by
  rw [p.totalBoundaryRayMultiplicity_def, Fan.internalBlowupRayMultiplicity_pos_iff,
    p.support_comap]
  exact (mem_boundaryPrimes.mp
    (Fan.internalBlowupBoundaryPrimeEquiv hΦ b s center ρ).property).1

/-- The marked inclusion sends the total boundary class to the weighted strict boundary
class with its actual pullback multiplicities. -/
theorem inclusion_sum_boundaryClass (hD : D[M].IsEffectiveCartier) :
    ι (∑ j, M.boundaryClass hD j) =
      Fan.markedBoundaryMap hΦ s (p.totalBoundaryRayMultiplicity hD) := by
  let := Fan.isIntegral_internalBlowupTower b s center hΦ
  let := M.integral
  have hPullback := hD.comap_of_isDominant p.projection
  have hclass : pullback p.projection (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ =
      (LineBundleClass.mk hPullback.toInvertibleSheaf)⁻¹ := by
    rw [pullback_inv, hD.pullback_mk_toInvertibleSheaf hPullback]
  rw [← p.marked_pullback, M.picardMarking_sum_boundaryClass, toMul_ofMul, hclass]
  exact Fan.internalBlowupPicardMarking_symm_ofMul_inv_toInvertibleSheaf
    hΦ b s center hPullback p.support_comap.le

end QPainleve.SignedClusterModularGroup.ContractedToricFiber
