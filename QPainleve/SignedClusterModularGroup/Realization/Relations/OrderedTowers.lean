/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.ExchangeMatrix
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Reference
public import QPainleve.SignedClusterModularGroup.Realization.Relations.Reference

import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber

/-!
# Signed cluster relations from ordered blowup towers

A specified toric presentation supplies a marked reference fiber and a contraction for the
integer relation criterion. The reference fiber retains the original surface, numbering and
center labels. Its boundary orders also certify the Boolean comparison of signed generator lists.
-/

public section

open AlgebraicGeometry CategoryTheory Module Quiver
open QPainleve.CharacterTorus QPainleve.Cluster
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "parameters[" c "]" => (fun j ↦ χ[c] (Multiplicative.ofAdd (Pi.single j 1)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {n r : ℕ} [NeZero n]

variable {X : Scheme} [X.Over S] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [Scheme.IsRationalOver (X ↘ S)]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]

local notation "B" => Chow.intersectionBilinForm ℂ X
local notation "Pic" => Additive (LineBundleClass X)
local notation "L" => Fin (Module.finrank ℤ Pic) → ℤ

local instance instIsIntegralOrderedTowersSurface : IsIntegral X := by
  let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  exact Scheme.IsRationalOver.isIntegral_of_smooth (f := X ↘ S) inferInstance

/-- A specified toric presentation of a numbered primitive nef square-zero anticanonical
cycle supplies a reference contraction and the complete integer criterion over every field.
The order table uses the surviving rays in the original boundary numbering. The fan and
ray labels stay fixed. Transposing the frame to agree with the numbering inverts all reference
center parameters. -/
theorem exists_xPullback_eq_iff_signedLoopInvariants_eq_of_toric_presentation
    (P : D.ToricPresentation (X ↘ S) b i r)
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (hD : D.IsEffectiveCartier)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD))) (hnef : classOf(hD).IsNef ℂ (X ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ X classOf(hD) classOf(hD) = 0) :
    ∃ (H : LinearMap.BilinForm ℤ L) (μ : H.IsometryEquiv B)
      (b' : Basis (Fin 2) ℤ N) (R : MarkedReferenceFiber i b' r A μ),
    let Q := R.presentation
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    let M := MarkedSurface.ofBoundary D A μ R.evaluation
    ∃ p₀ : ContractedToricFiber b' Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[R.center] M,
      p₀.IsNodalContraction ∧
      ((b' = b ∧ parameters[R.center] = P.parameters) ∨
        (b' = b.reindex (Equiv.swap 0 1) ∧ parameters[R.center] = P.parameters⁻¹)) ∧
      (∃ hfan : Q.fan = P.fan, hfan ▸ Q.rays = P.rays) ∧
      let E := Fan.rayExchangeMatrix b' Q.rays
      ∀ (k : Type*) [Field k] (w v : Word E E)
        {d : ℕ} (β : Basis (Fin d) ℤ E.matrix.mulVecLin.ker),
        let orders := p₀.numberedBoundaryOrders M.isEffectiveCartier_boundaryIdeal
        w.xPullback k = v.xPullback k ↔
          w.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0) =
            v.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0) := by
  let : Module.Free ℤ Pic := X.free_picard_of_isRationalOver ℂ
  let : Module.Finite ℤ Pic := X.finite_picard_of_isRationalOver ℂ
  let a : L ≃ₗ[ℤ] Pic := (Module.finBasis ℤ Pic).equivFun.symm
  let H := (B).comp a.toLinearMap a.toLinearMap
  let μ : H.IsometryEquiv B := ((B).isometryEquivOfCompLinearEquiv a).symm
  obtain ⟨b', R, hframe, hrays⟩ :=
    exists_marked_reference_fiber_of_ordered_towers P.regular P.complete P.rays P.parameters
      P.isNodal P.iso P.iso_over P.iso_boundary hD A μ
  let M := MarkedSurface.ofBoundary D A μ R.evaluation
  let hD' := M.isEffectiveCartier_boundaryIdeal
  obtain ⟨p₀, hnodal₀⟩ := R.hasNodalModel.exists_isNodalContraction hD'
  have hδ : classOf(hD') = classOf(hD) :=
    congrArg Inv.inv (LineBundleClass.mk_toInvertibleSheaf_congr _ _
      (MarkedSurface.ofBoundary_ker D A μ R.evaluation))
  refine ⟨H, μ, b', R, p₀, hnodal₀, hframe, hrays, fun k _ w v _ β ↦ ?_⟩
  exact R.presentation.xPullback_eq_iff_signedLoopInvariants_eq_of_nodal_contraction k p₀ hnodal₀
    (Fan.rayExchangeMatrix_matrix b' R.presentation.rays)
    (by rwa [hδ]) (by rwa [hδ]) (by rwa [hδ]) w v β

end QPainleve.SignedClusterModularGroup
