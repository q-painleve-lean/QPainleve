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
local notation "parameters[" c "]" => (fun j ↦ χ[c] (Multiplicative.ofAdd (Pi.single j 1)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {n r : ℕ} [NeZero n]

variable {X : Scheme} [X.Over S] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]

local notation "B" => Chow.intersectionBilinForm ℂ X
local notation "Pic" => Additive (LineBundleClass X)
local notation "L" => Fin (Module.finrank ℤ Pic) → ℤ

local notation "marked[" A "," μ "," R "]" =>
  MarkedSurface.ofBoundary D A μ (MarkedReferenceFiber.evaluation R)
local notation "cartier[" M "]" => MarkedSurface.isEffectiveCartier_boundaryIdeal M

/-- The reference contraction of a specified toric presentation of a numbered
primitive nef square-zero anticanonical cycle, with its finite Picard marking.
The contraction and the marking determine the seed and numbered order table. -/
@[ext]
structure OrderedToricRelationCriterion [IsIntegral X] (i : N →+ V) (r : ℕ)
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n) where
  /-- The form in the coordinates of the finite Picard marking. -/
  form : LinearMap.BilinForm ℤ L
  /-- The Picard marking of the original surface. -/
  marking : form.IsometryEquiv B
  /-- The oriented frame for the charge determinants. -/
  basis : Basis (Fin 2) ℤ N
  /-- The reference fiber on the original numbered surface. -/
  reference : MarkedReferenceFiber i basis r A marking
  /-- The contraction to the original numbered surface. -/
  contraction :
    let Q := reference.presentation
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    ContractedToricFiber basis Q.rays Q.regular Q.cycle Q.origin Q.inclusion
      χ[reference.center] marked[A, marking, reference]
  /-- The contraction is realized by a nodal blowup tower. -/
  isNodalContraction :
    let Q := reference.presentation
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    contraction.IsNodalContraction
  /-- The total boundary class is primitive. -/
  boundary_primitive : IsPrimitive (Additive.ofMul classOf(cartier[marked[A, marking, reference]]))
  /-- The total boundary class is nef. -/
  boundary_nef : (classOf(cartier[marked[A, marking, reference]])).IsNef ℂ (X ↘ S)
  /-- The total boundary class has self-intersection zero. -/
  boundary_square_zero :
    let δ := classOf(cartier[marked[A, marking, reference]])
    Chow.classIntersectionNumber ℂ X δ δ = 0

namespace OrderedToricRelationCriterion

variable [IsIntegral X]
  {A : Scheme.NodalCycleNumbering (X := D.subscheme)
    (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n}
  (R : OrderedToricRelationCriterion i r A)

local notation "Q" => MarkedReferenceFiber.presentation (OrderedToricRelationCriterion.reference R)

local instance : Nonempty (Q).fan.cones := (Q).complete.nonempty_cones
local instance : PrestableFamily (((Q).fan.boundaryIdeal
    (Q).complete.nonempty_cones).subscheme ↘ S) := (Q).prestable
local instance : NeZero (Q).length := (Q).neZero

/-- The seed matrix is the determinant pairing of the labeled rays in the oriented frame. -/
abbrev exchangeMatrix : SkewExchangeMatrix (Fin r) :=
  Fan.rayExchangeMatrix R.basis (Q).rays

/-- The orders of the independent coordinates along the numbered surviving boundary. -/
def boundaryOrders : Fin n → Fin r → ℤ :=
  R.contraction.numberedBoundaryOrders cartier[marked[A, R.marking, R.reference]]

/-- The reference contraction certifies its seed and order table for signed loop comparison. -/
theorem comparisonInput : (Q).IsSignedLoopComparisonInput R.contraction R.exchangeMatrix
    R.boundaryOrders :=
  ⟨Fan.rayExchangeMatrix_matrix R.basis (Q).rays, rfl⟩

end OrderedToricRelationCriterion

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
    ∃ R : OrderedToricRelationCriterion i r A,
      ((R.basis = b ∧ parameters[R.reference.center] = P.parameters) ∨
        (R.basis = b.reindex (Equiv.swap 0 1) ∧ parameters[R.reference.center] = P.parameters⁻¹)) ∧
      (∃ hfan : R.reference.presentation.fan = P.fan,
        hfan ▸ R.reference.presentation.rays = P.rays) := by
  let : Module.Free ℤ Pic := X.free_picard_of_isRationalOver ℂ
  let : Module.Finite ℤ Pic := X.finite_picard_of_isRationalOver ℂ
  obtain ⟨H, μ, b', R, hframe, hrays⟩ :=
    exists_fin_marked_reference_fiber_of_toric_presentation P hD A
  let hD' := cartier[marked[A, μ, R]]
  obtain ⟨p₀, hnodal₀⟩ := R.hasNodalModel.exists_isNodalContraction hD'
  have hδ : classOf(hD') = classOf(hD) :=
    MarkedSurface.ofBoundary_boundaryIdeal_class D A μ R.evaluation hD' hD
  exact ⟨⟨H, μ, b', R, p₀, hnodal₀, by rwa [hδ], by rwa [hδ], by rwa [hδ]⟩, hframe, hrays⟩

end QPainleve.SignedClusterModularGroup
