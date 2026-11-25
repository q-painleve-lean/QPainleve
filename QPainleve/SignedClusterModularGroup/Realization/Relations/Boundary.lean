/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Relations
public import QPainleve.SignedClusterModularGroup.Realization.NumberedRays

/-!
# Reading the boundary index of a signed loop

The finite search in the integer loop invariants returns the forward image of
component zero. One reference nodal contraction of the presentation suffices
to tabulate the target orders, even when the reference center lies outside the
domain of the loop. The comparison combines
`GeometricRealization.boundaryRayOfOrders_eq_boundaryPerm` with
`ContractedToricFiber.numberedBoundaryRays_eq_of_nodalContractions`.
-/

public section

open AlgebraicGeometry CategoryTheory Module Multiplicative
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric Scheme

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n]
  {L : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {b : Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}
  {E : SkewExchangeMatrix (Fin r)} {w : Word E E}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "T" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "χ[" c "]" => pointsEquiv ℂ (Fin r → ℤ)
  (Subtype.mk (Over.Hom.left (c : Point T)) (Over.w c))
local notation "src[" C "," x "]" => x ≫ PartialMap.domainSource (X := T) (Y := T) C
local notation "dst[" C "," x "]" => x ≫ PartialMap.domainTarget (X := T) (Y := T) C

variable [PrestableFamily ((Φ.boundaryIdeal hΦ₀).subscheme ↘ S)]
  {γ : Type*} {a : γ → ((Φ.boundaryIdeal hΦ₀).subscheme ↘ S).smoothLocus}
  {τ : NodalCycleNumbering a m} {origin : ZMod m}
  {ι : L →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin r → ℤ)}
  {P : Point (Over.mk (structureMap ℂ (Fin r → ℤ))) →
    MarkedSurface ℂ n B (scheme ℂ (Fin r →₀ ℤ))}
  {C : (scheme ℂ (Fin r → ℤ)).PartialMap (scheme ℂ (Fin r → ℤ))} [IsDominant C.hom]
  [C.IsOver (Over.mk (structureMap ℂ (Fin r → ℤ))).hom
    (Over.mk (structureMap ℂ (Fin r → ℤ))).hom]

local notation "fiberAt[" c "]" => ContractedToricFiber b s hΦ τ origin ι χ[c] (P c)
local notation "Aux" => LinearMap.BilinForm.prod
  (Chow.intersectionBilinForm ℂ Φ.algebraicRealization)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))

/-- The boundary search for a realized signed loop returns the forward label of
component zero. The target order table may be taken from any reference nodal
contraction with the same auxiliary Picard inclusion. -/
theorem signedLoopInvariants_boundary_eq_some
    [Φ.algebraicRealization.IsProjectiveOver ℂ]
    [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S)]
    (hsep : (Aux).SeparatingRight)
    (R : GeometricRealization (T₀ := T) (T₁ := T) P P C (w.xRationalMap ℂ))
    (x : CenterPoint (U := T) (V := T) C)
    (hcΦ : Φ.IsComplete)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap s))
    (hindex : (Fan.rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    {c₀ : Point T} (p₀ : fiberAt[c₀]) (hnodal₀ : p₀.IsNodalContraction)
    (p : fiberAt[src[C,x]]) (q : fiberAt[dst[C,x]]) (hnodal : q.IsNodalContraction)
    (h₀ : D[P (src[C,x])].IsEffectiveCartier)
    {κ : Type*} (basisVectors : κ → Fin r → ℤ) :
    let orders (j : Fin n) := Fan.rayBoundaryOrders b s
      (p₀.numberedBoundaryRays hnodal₀.cartier ((ZMod.finEquiv n).toEquiv j))
    let source := Fan.rayBoundaryOrders b s
      ((Φ.boundaryNormalizationComponentEquiv hΦ).symm (τ.component origin))
    ((w.signedLoopInvariants basisVectors orders source).2.2).map (ZMod.finEquiv n).toEquiv =
      some (R.boundaryPerm 0) := by
  have h := R.boundaryRayOfOrders_eq_boundaryPerm x p q h₀ hnodal.cartier hcΦ hE hindex
  rw [q.numberedBoundaryRays_eq_of_nodalContractions p₀ hnodal hnodal₀ hsep] at h
  simpa only [Quiver.Path.signedLoopInvariants_def, Fan.boundaryRayOfOrders_eq_find_coordinates,
    Function.Embedding.trans_apply, Equiv.toEmbedding_apply, ← Fan.rayBoundaryOrders_apply_eq_repr,
    ← funext_iff] using h

end QPainleve.SignedClusterModularGroup.GeometricRealization
