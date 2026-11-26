/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Reference.Finite
public import QPainleve.SignedClusterModularGroup.Realization.Relations.Reference

import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber

/-!
# Signed cluster relations from ordered blowup towers

A specified toric presentation supplies a marked reference contraction for the
complete integer relation criterion. Its numbered boundary orders and exchange
matrix give an input to the same comparison theorems used with integer tables
supplied separately.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module
open QPainleve.CharacterTorus QPainleve.Cluster
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {n : ℕ} [NeZero n]

variable {X : Scheme} [X.Over S] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]

local notation "Pic" => Additive (LineBundleClass X)

local notation "cartier[" M "]" => MarkedSurface.isEffectiveCartier_boundaryIdeal M

/-- The reference contraction and boundary hypotheses for the integer comparison of signed
loops. The chosen marked reference fiber supplies the seed, and the contraction supplies
the numbered boundary order table. -/
@[ext]
structure OrderedToricRelationCriterion [IsIntegral X] {i : N →+ V} {r : ℕ}
    {A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n}
    (R : FiniteMarkedReferenceFiber i r A) where
  /-- The contraction to the original numbered surface. -/
  contraction :
    let Q := R.reference.presentation
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    ContractedToricFiber R.basis Q.rays Q.regular Q.cycle Q.origin Q.inclusion
      χ[R.reference.center] R.reference.markedSurface
  /-- The contraction is realized by a nodal blowup tower. -/
  isNodalContraction :
    let Q := R.reference.presentation
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    contraction.IsNodalContraction
  /-- The total boundary class is primitive. -/
  boundary_primitive : IsPrimitive (Additive.ofMul classOf(cartier[R.reference.markedSurface]))
  /-- The total boundary class is nef. -/
  boundary_nef : (classOf(cartier[R.reference.markedSurface])).IsNef ℂ (X ↘ S)
  /-- The total boundary class has self-intersection zero. -/
  boundary_square_zero :
    let δ := classOf(cartier[R.reference.markedSurface])
    Chow.classIntersectionNumber ℂ X δ δ = 0

namespace OrderedToricRelationCriterion

variable [IsIntegral X] {i : N →+ V} {r : ℕ}
  {A : Scheme.NodalCycleNumbering (X := D.subscheme)
    (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n}
  {R : FiniteMarkedReferenceFiber i r A} (C : OrderedToricRelationCriterion R)

local notation "Q" => R.reference.presentation

local instance : Nonempty (Q).fan.cones := (Q).complete.nonempty_cones
local instance : PrestableFamily (((Q).fan.boundaryIdeal
    (Q).complete.nonempty_cones).subscheme ↘ S) := (Q).prestable
local instance : NeZero (Q).length := (Q).neZero

/-- The orders of the independent coordinates along the numbered surviving boundary. -/
def boundaryOrders : Fin n → Fin r → ℤ :=
  C.contraction.numberedBoundaryOrders cartier[R.reference.markedSurface]

/-- The reference contraction certifies its seed and order table for signed loop comparison. -/
theorem comparisonInput : (Q).IsSignedLoopComparisonInput C.contraction R.reference.exchangeMatrix
    C.boundaryOrders :=
  ⟨Fan.rayExchangeMatrix_matrix R.basis (Q).rays, rfl⟩

end OrderedToricRelationCriterion

variable {i : N →+ V} {b : Basis (Fin 2) ℤ N} {r : ℕ}

/-- A chosen reference fiber of a primitive nef square-zero anticanonical cycle
supplies the contraction and boundary data for the integer relation criterion. -/
theorem FiniteMarkedReferenceFiber.nonempty_orderedToricRelationCriterion [IsIntegral X]
    {A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n}
    (R : FiniteMarkedReferenceFiber i r A) (hD : D.IsEffectiveCartier)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD))) (hnef : classOf(hD).IsNef ℂ (X ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ X classOf(hD) classOf(hD) = 0) :
    Nonempty (OrderedToricRelationCriterion R) := by
  let hD' := cartier[R.reference.markedSurface]
  obtain ⟨p₀, hnodal₀⟩ := R.reference.hasNodalModel.exists_isNodalContraction hD'
  have hδ : classOf(hD') = classOf(hD) :=
    MarkedSurface.ofBoundary_boundaryIdeal_class D A R.marking R.reference.evaluation hD' hD
  exact ⟨⟨p₀, hnodal₀, by rwa [hδ], by rwa [hδ], by rwa [hδ]⟩⟩

variable [Scheme.IsRationalOver (X ↘ S)]

local instance instIsIntegralOrderedTowersSurface : IsIntegral X := by
  let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  exact Scheme.IsRationalOver.isIntegral_of_smooth (f := X ↘ S) inferInstance

/-- A specified toric presentation supplies a reference contraction and the certified
input to the complete integer criterion over every field. The original numbering, fan,
and ray labels are retained. Transposing the frame to agree with the numbering inverts all
reference center parameters. -/
theorem exists_ordered_toric_relation_criterion
    (P : D.ToricPresentation (X ↘ S) b i r)
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (hD : D.IsEffectiveCartier)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD))) (hnef : classOf(hD).IsNef ℂ (X ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ X classOf(hD) classOf(hD) = 0) :
    ∃ R : FiniteMarkedReferenceFiber i r A,
      R.reference.HasToricData P ∧ Nonempty (OrderedToricRelationCriterion R) := by
  let : Module.Free ℤ Pic := X.free_picard_of_isRationalOver ℂ
  let : Module.Finite ℤ Pic := X.finite_picard_of_isRationalOver ℂ
  obtain ⟨R, hR⟩ := exists_fin_marked_reference_fiber_of_toric_presentation P hD A
  exact ⟨R, hR, R.nonempty_orderedToricRelationCriterion hD hprim hnef hsq⟩

end QPainleve.SignedClusterModularGroup
