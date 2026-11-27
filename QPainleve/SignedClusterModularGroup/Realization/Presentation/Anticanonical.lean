/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Identification

import QPainleve.Geometry.Toric.Fan.Picard.Complexity
import QPainleve.Geometry.Toric.Fan.Presentation.Induction

/-!
# Cluster modular groups of anticanonical pairs

A numbered primitive nef square-zero anticanonical cycle on a smooth projective
rational surface determines a seed with one label for each internal center
of a toric presentation. The number of labels is twelve minus the number of
boundary components. The opposite cluster modular groups of the resulting seed
act by signed boundary isometries and boundary rotations on the original Picard
lattice. The moving family retains the original pair as its reference fiber.

The construction combines `IdealSheafData.hasToricPresentation_of_anticanonical_cycle` with
`exists_picardGroupEquivs_of_toric_presentation`.
-/

public section

open AlgebraicGeometry CategoryTheory Module
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀] [Uncountable k₀] [NeZero (2 : k₀)]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "δ[" h "]" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N}
  {X : Scheme} [X.Over (Spec (.of k₀))] [X.IsProjectiveOver k₀]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k₀))] [Scheme.IsRationalOver (X ↘ Spec (.of k₀))]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ Spec (.of k₀))]
  {n : ℕ} [NeZero n]

local notation "K" => LineBundleClass.mk (canonicalBundle k₀ X 2)
/-- A numbered primitive nef square-zero anticanonical cycle on a smooth projective
rational surface admits a toric seed on `Fin (12 - n)`. Its signed and
unsigned opposite cluster modular groups identify with the signed boundary
isometries and rotations of the original Picard lattice. The
`PicardGroupIdentification` records the original numbered fiber and the nodal
family. On loops the signed equivalence evaluates by geometric Picard pullback
and retains the sign on the ordered branches. -/
theorem exists_picardGroupEquivs_of_anticanonical_cycle
    (hi : IsIntegralLattice i)
    (A : Scheme.NodalCycleNumbering (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (hD : D.IsEffectiveCartier) (hcan : LineBundleClass.mk hD.toInvertibleSheaf = K)
    (hprim : IsPrimitive (Additive.ofMul δ[hD])) (hnef : δ[hD].IsNef k₀ (X ↘ S))
    (hsq : Chow.classIntersectionNumber k₀ X δ[hD] δ[hD] = 0) :
    letI : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    letI : IsIntegral X := (inferInstance : Scheme.IsRationalOver (X ↘ S)).isIntegral_of_smooth
    ∃ R : FiniteMarkedReferenceFiber i (12 - n) A,
      (R.basis = b ∨ R.basis = b.reindex (Equiv.swap 0 1)) ∧
        Nonempty (PicardGroupIdentification R hD) := by
  let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsIntegral X := (inferInstance : Scheme.IsRationalOver (X ↘ S)).isIntegral_of_smooth
  obtain ⟨r, ⟨P⟩⟩ := (hasToricPresentation_iff ..).mp
    (D.hasToricPresentation_of_anticanonical_cycle k₀ b hi A hD hcan)
  have hr := Fan.centerCount_eq_of_square_zero k₀ P.regular P.complete P.rays P.parameters
    P.isNodal P.iso P.iso_boundary A hD hcan hsq
  subst r
  obtain ⟨R, hR, hQ⟩ := exists_picardGroupEquivs_of_toric_presentation P A hD hprim hnef hsq
  exact ⟨R, hR.basis_parameters.imp And.left And.left, hQ⟩

end QPainleve.SignedClusterModularGroup
