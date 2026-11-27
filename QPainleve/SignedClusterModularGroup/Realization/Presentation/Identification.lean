/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Presentation.PicardGroupIdentification

import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Group

/-!
# Cluster modular groups of numbered surface presentations

Specified nodal and internal blowup towers determine the seed and the Picard
group identifications of the original numbered surface. A finite integral
marking supplies the moving family, and conjugation by that marking recovers
the group on the actual Picard lattice. The oriented toric basis is chosen by
`exists_fin_marked_reference_fiber_of_toric_presentation`, and the identifications are
given by `CompleteToricPresentation.exists_picardGroupEquivs_of_nodal_model`.
-/

public section

open AlgebraicGeometry CategoryTheory Module
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀] [Uncountable k₀] [NeZero (2 : k₀)]

open GeometricRealization

local notation "S" => Spec (CommRingCat.of k₀)
local notation "δ[" h "]" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N}
  {X : Scheme} [X.Over (Spec (.of k₀))] [X.IsProjectiveOver k₀]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k₀))]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ Spec (.of k₀))]
  {n r : ℕ} [NeZero n]

local notation "Pic" => Additive (LineBundleClass X)
local notation "classes[" A "," hD "]" =>
  (fun j ↦ Additive.ofMul (LineBundleClass.primeDivisorClass
    (D.boundaryPrimeEmbedding (Scheme.NodalCycleNumbering.boundaryPrimeEquiv A hD j))))

/-- The chosen numbered reference fiber determines the signed and unsigned Picard
equivalences, with its existing marking and X evaluation. -/
theorem FiniteMarkedReferenceFiber.nonempty_picardGroupIdentification [IsIntegral X]
    {A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n}
    (R : FiniteMarkedReferenceFiber i r A) (hD : D.IsEffectiveCartier)
    (hprim : IsPrimitive (Additive.ofMul δ[hD])) (hnef : δ[hD].IsNef k₀ (X ↘ S))
    (hsq : Chow.classIntersectionNumber k₀ X δ[hD] δ[hD] = 0) :
    Nonempty (PicardGroupIdentification R hD) := by
  let M₀ := R.reference.markedSurface
  have hδ : δ[M₀.isEffectiveCartier_boundaryIdeal] = δ[hD] :=
    MarkedSurface.ofBoundary_boundaryIdeal_class D A R.marking R.reference.evaluation
      M₀.isEffectiveCartier_boundaryIdeal hD
  have hE := Fan.rayExchangeMatrix_matrix R.basis R.reference.presentation.rays
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let d := classes[A,hD]
  have hd : M₀.boundaryClass M₀.isEffectiveCartier_boundaryIdeal = R.marking.symm ∘ d :=
    funext (MarkedSurface.boundaryClass_ofBoundary D A R.marking R.reference.evaluation hD)
  have hgroups := R.reference.presentation.exists_picardGroupEquivs_of_nodal_model (M₀ := M₀)
    R.reference.hasNodalModel hE (by rwa [hδ]) (by rwa [hδ]) (by rwa [hδ])
  rw [hd] at hgroups
  obtain ⟨identification, hM⟩ := hgroups
  exact ⟨⟨identification, hM⟩⟩

variable [Scheme.IsRationalOver (X ↘ Spec (.of k₀))]

/-- For a specified ordered toric presentation of a primitive nef square-zero
anticanonical cycle, the signed and unsigned opposite cluster modular groups
identify with the signed boundary isometries and rotations of the original
Picard group. The reference family keeps the original surface and numbering.
The oriented frame retains the input fan and all ray labels, and in the
transposed frame the reference center parameters are inverted. The signed
equivalence evaluates by geometric Picard pullback and the branch sign. -/
theorem exists_picardGroupEquivs_of_toric_presentation
    (P : D.ToricPresentation (X ↘ S) b i r)
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (hD : D.IsEffectiveCartier)
    (hprim : IsPrimitive (Additive.ofMul δ[hD])) (hnef : δ[hD].IsNef k₀ (X ↘ S))
    (hsq : Chow.classIntersectionNumber k₀ X δ[hD] δ[hD] = 0) :
    letI : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    letI : IsIntegral X := (inferInstance : Scheme.IsRationalOver (X ↘ S)).isIntegral_of_smooth
    ∃ R : FiniteMarkedReferenceFiber i r A,
      R.reference.HasToricData P ∧ Nonempty (PicardGroupIdentification R hD) := by
  let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsIntegral X := (inferInstance : Scheme.IsRationalOver (X ↘ S)).isIntegral_of_smooth
  let : Module.Free ℤ Pic := X.free_picard_of_isRationalOver k₀
  let : Module.Finite ℤ Pic := X.finite_picard_of_isRationalOver k₀
  obtain ⟨R, hR⟩ := exists_fin_marked_reference_fiber_of_toric_presentation P hD A
  exact ⟨R, hR, R.nonempty_picardGroupIdentification hD hprim hnef hsq⟩

end QPainleve.SignedClusterModularGroup
