/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Mutation.Tropical
public import QPainleve.SignedClusterModularGroup.Realization.Agreement
public import QPainleve.SignedClusterModularGroup.Realization.Boundary

import QPainleve.Geometry.Toric.Fan.Boundary.NumberedPrime

/-!
# Boundary labels from tropical words

The tropical action on the orders of the independent X coordinates computes the
forward action on the numbered components of a marked boundary. In an ordered
toric presentation the order vectors use the surviving rays. With finite-index
target charges, a finite search among these rays recovers the target label.

The valuation transport is `Fan.rayBoundaryOrders_eq_tropical_of_comp_contractedXEvaluation`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory DihedralGroup Multiplicative Quiver
open QPainleve.Cluster TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Xtor[" r "]" => Spec (CommRingCat.of (LaurentRing ℂ (Fin r)))
local notation "Dtor[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)
local notation "Pic[" Φ "," r "]" =>
  Additive (LineBundleClass (Fan.algebraicRealization Φ)) × (Fin r → ℤ)
local notation "D[" P "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair P)))
local notation "center" c:arg => (fun j : Fin _ ↦ c (ofAdd (Pi.single j 1)))

section Source

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n] {L : Type} [AddCommGroup L]
  {B : LinearMap.BilinForm ℤ L} {M : MarkedSurface ℂ n B Xtor[r]}
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}
  [PrestableFamily (Dtor[Φ,hΦ₀] ↘ S)]
  {α : Type*} {a : α → (Dtor[Φ,hΦ₀] ↘ S).smoothLocus}
  {T : Scheme.NodalCycleNumbering a m} {o : ZMod m} {μ : L →ₗ[ℤ] Pic[Φ,r]}
  {c : Multiplicative (Fin r → ℤ) →* ℂˣ}
  (p : ContractedToricFiber b s hΦ T o μ c M)

namespace ContractedToricFiber

/-- Each numbered component of a contracted boundary determines its surviving toric ray. -/
def numberedBoundaryRays (hM : D[M].IsEffectiveCartier) : ZMod n ↪ Φ.Ray :=
  (M.numberedBoundaryPrimes hM).trans
    (Fan.contractedBoundaryRayEmbedding hΦ b s (center c) p.projection p.support_comap)

/-- The ray at a numbered component is the strict transform of its boundary prime. -/
theorem numberedBoundaryRays_apply (hM : D[M].IsEffectiveCartier) (j : ZMod n) :
    p.numberedBoundaryRays hM j =
      Fan.contractedBoundaryRayEmbedding hΦ b s (center c) p.projection p.support_comap
        (M.numberedBoundaryPrimes hM j) :=
  (rfl)

/-- The numbered rays are exactly the surviving rays of the contraction. -/
theorem range_numberedBoundaryRays (hM : D[M].IsEffectiveCartier) :
    Set.range (p.numberedBoundaryRays hM) =
      Set.range (Fan.contractedBoundaryRayEmbedding hΦ b s (center c) p.projection
        p.support_comap) := by
  rw [numberedBoundaryRays, Function.Embedding.coe_trans,
    (M.numberedBoundaryPrimes_surjective hM).range_comp]

/-- A ray occurs in the boundary numbering exactly when its strict prime
projects to a boundary prime of the contracted surface. -/
theorem mem_range_numberedBoundaryRays_iff (hM : D[M].IsEffectiveCartier) (ρ : Φ.Ray) :
    ρ ∈ Set.range (p.numberedBoundaryRays hM) ↔
      p.projection (Fan.internalBlowupBoundaryPrimeEquiv hΦ b s (center c) ρ).val ∈
        D[M].boundaryPrimes := by
  rw [p.range_numberedBoundaryRays, Fan.mem_range_contractedBoundaryRayEmbedding_iff]

/-- A numbered toric component gives the ray of a contracted component exactly
when its generic point maps to that contracted component's generic point. -/
theorem numberedBoundaryRays_eq_iff (hM : D[M].IsEffectiveCartier) (j : ZMod n) (k : ZMod m) :
    letI : PrestableFamily (M.boundary ↘ S) := M.prestable
    p.numberedBoundaryRays hM j =
        (Φ.boundaryNormalizationComponentEquiv hΦ).symm (T.component k) ↔
      p.boundaryMap (T.componentGenericPoint k) = M.cycle.componentGenericPoint j := by
  let : PrestableFamily (M.boundary ↘ S) := M.prestable
  let : IsClosedImmersion M.pair.hom.left := M.closedImmersion
  rw [numberedBoundaryRays, Function.Embedding.trans_apply,
    Fan.contractedBoundaryRayEmbedding_eq_iff, Fan.internalBlowupBoundaryPrime_val,
    Equiv.apply_symm_apply, ← T.componentGenericPoint_def,
    ← Scheme.Hom.comp_apply, ← p.boundary_comp, Scheme.Hom.comp_apply,
    MarkedSurface.numberedBoundaryPrimes_apply_val, MarkedSurface.coe_boundaryPrime]
  exact M.pair.hom.left.isClosedEmbedding.injective.eq_iff

/-- The starting ray is determined by the toric numbering and the chosen origin,
independently of the center parameters. -/
@[simp]
theorem numberedBoundaryRays_zero (hM : D[M].IsEffectiveCartier) :
    p.numberedBoundaryRays hM 0 =
      (Φ.boundaryNormalizationComponentEquiv hΦ).symm (T.component o) :=
  (p.numberedBoundaryRays_eq_iff hM 0 o).mpr p.component_zero

end ContractedToricFiber

variable {N' V' : Type} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
  {i' : N' →+ V'} {Ψ : Fan i'} [hΨ₀ : Nonempty Ψ.cones]
  {m' : ℕ} [NeZero m'] {L' : Type} [AddCommGroup L']
  {B' : LinearMap.BilinForm ℤ L'} {M' : MarkedSurface ℂ n B' Xtor[r]}
  {b' : Module.Basis (Fin 2) ℤ N'} {s' : Fin r → Ψ.Ray} {hΨ : Ψ.IsRegular}
  [PrestableFamily (Dtor[Ψ,hΨ₀] ↘ S)]
  {α' : Type*} {a' : α' → (Dtor[Ψ,hΨ₀] ↘ S).smoothLocus}
  {T' : Scheme.NodalCycleNumbering a' m'} {o' : ZMod m'} {μ' : L' →ₗ[ℤ] Pic[Ψ,r]}
  {c' : Multiplicative (Fin r → ℤ) →* ℂˣ}
  (q : ContractedToricFiber b' s' hΨ T' o' μ' c' M')
  {E E' : SkewExchangeMatrix (Fin r)} {w : Word E E'}

local notation "trop[" w "]" =>
  DFunLike.coe (F := Equiv.Perm (Fin r → ℤ))
    (CategoryTheory.Functor.map (Paths.lift (tropicalPrefunctor (A := ℤ) (Fin r))) w)

namespace FiberRealization

variable {p q}
variable {I : B'.IsometryEquiv B} {g : DihedralGroup n}
  (R : FiberRealization M M' (w.xRationalMap ℂ) I g)
  (hM : D[M].IsEffectiveCartier) (hM' : D[M'].IsEffectiveCartier)
  (hcΦ : Φ.IsComplete)
  (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap s))

include R hcΦ hE in
/-- The order vector of the image of a numbered component under a signed word
is the tropical word applied to the source vector. This formula applies at every
center with a fiber realization, including for charges of deficient rank. -/
theorem rayBoundaryOrders_tropical (j : ZMod n) :
    Fan.rayBoundaryOrders b' s' (q.numberedBoundaryRays hM' (cycleVertexPerm g j)) =
      trop[w] (Fan.rayBoundaryOrders b s (p.numberedBoundaryRays hM j)) := by
  have heval := R.evaluation_eq
  rw [p.evaluation_eq, q.evaluation_eq] at heval
  have hpoint := M.map_boundaryPrime hM hM' R.iso j
  rw [R.boundaryAction_eq] at hpoint
  have himage :
      (MarkedSurface.surfaceIso R.iso).hom (M.numberedBoundaryPrimes hM j).val =
        (M'.numberedBoundaryPrimes hM' (cycleVertexPerm g j)).val := by
    simpa only [MarkedSurface.numberedBoundaryPrimes_apply_val,
      CodimensionOnePoint.coe_mapOfIsOpenImmersion] using
      congrArg Subtype.val hpoint
  exact Fan.rayBoundaryOrders_eq_tropical_of_comp_contractedXEvaluation
    b b' s s' hΦ hΨ c c' p.projection q.projection w (MarkedSurface.surfaceIso R.iso)
    p.support_comap q.support_comap hcΦ hE heval _ _ himage

include R hcΦ hE in
/-- Searching the surviving target rays at the tropical order vector returns the
forward label of the source component, read as an element of `Fin n`. -/
theorem boundaryRayOfOrders_eq_some_cycleVertexPerm
    (hindex : (Fan.rayChargeMap s').range.toAddSubgroup.index ≠ 0) (j : ZMod n) :
    Fan.boundaryRayOfOrders b' s'
      ((ZMod.finEquiv n).toEquiv.toEmbedding.trans (q.numberedBoundaryRays hM'))
      (trop[w] (Fan.rayBoundaryOrders b s (p.numberedBoundaryRays hM j))) =
        some ((ZMod.finEquiv n).toEquiv.symm (cycleVertexPerm g j)) := by
  apply (Fan.boundaryRayOfOrders_eq_some_iff _ _ _ _ hindex _).mpr
  simpa only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.apply_symm_apply] using
      R.rayBoundaryOrders_tropical (p := p) (q := q) hM hM' hcΦ hE j

end FiberRealization

namespace GeometricRealization

variable {U₀ U₁ : Over S} [Nonempty U₀.left] [Smooth U₀.hom]
  {P₀ : Point U₀ → MarkedSurface ℂ n B Xtor[r]}
  {P₁ : Point U₁ → MarkedSurface ℂ n B' Xtor[r]}
  {C : U₀.left.PartialMap U₁.left} [IsDominant C.hom] [C.IsOver U₀.hom U₁.hom]

/-- Start the signed tropical word at the fixed toric origin and search the surviving
target rays at any center in the realization domain. The result is the forward image of
component zero in the marked boundary numbering. -/
theorem boundaryRayOfOrders_eq_boundaryPerm
    (R : GeometricRealization P₀ P₁ C (w.xRationalMap ℂ)) (x : CenterPoint C)
    (p₀ : ContractedToricFiber b s hΦ T o μ c (P₀ (x ≫ C.domainSource)))
    (p₁ : ContractedToricFiber b' s' hΨ T' o' μ' c' (P₁ (x ≫ C.domainTarget)))
    (h₀ : D[P₀ (x ≫ C.domainSource)].IsEffectiveCartier)
    (h₁ : D[P₁ (x ≫ C.domainTarget)].IsEffectiveCartier)
    (hcΦ : Φ.IsComplete)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap s))
    (hindex : (Fan.rayChargeMap s').range.toAddSubgroup.index ≠ 0) :
    (Fan.boundaryRayOfOrders b' s'
      ((ZMod.finEquiv n).toEquiv.toEmbedding.trans (p₁.numberedBoundaryRays h₁))
      (trop[w] (Fan.rayBoundaryOrders b s
        ((Φ.boundaryNormalizationComponentEquiv hΦ).symm (T.component o))))).map
      (ZMod.finEquiv n).toEquiv = some (R.boundaryPerm 0) := by
  have h := (R.fiber x).boundaryRayOfOrders_eq_some_cycleVertexPerm
    (p := p₀) (q := p₁) h₀ h₁ hcΦ hE hindex 0
  rw [p₀.numberedBoundaryRays_zero] at h
  rw [h, Option.map_some, Equiv.apply_symm_apply, R.boundaryPerm_def]

end GeometricRealization

end Source

end QPainleve.SignedClusterModularGroup
