/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Reference

/-!
# Reference fibers with finite Picard coordinates

A finite Picard marking gives a reference fiber in integer coordinates while retaining
the original surface and its numbered boundary. This marking is shared by the Picard
action and the integer comparison of signed loops.
-/

public section

open AlgebraicGeometry Module TauCeti.AlgebraicGeometry
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

local notation "S" => Spec (CommRingCat.of k₀)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {X : Scheme} [X.Over (Spec (.of k₀))] [IsIntegral X] [X.IsProjectiveOver k₀]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k₀))] {D : X.IdealSheafData}
  [PrestableFamily (D.subscheme ↘ Spec (.of k₀))] {n : ℕ} [NeZero n]

local notation "Pic" => Additive (LineBundleClass X)
local notation "L" => (Fin (Module.finrank ℤ Pic) → ℤ)

/-- A reference fiber on a numbered surface with a Picard marking by integer coordinates. -/
@[ext]
structure FiniteMarkedReferenceFiber (i : N →+ V) (r : ℕ)
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n) where
  /-- The intersection form in the coordinates of the Picard marking. -/
  form : LinearMap.BilinForm ℤ L
  /-- The marking on the original surface's Picard lattice. -/
  marking : form.IsometryEquiv (Chow.intersectionBilinForm k₀ X)
  /-- The oriented frame of the toric presentation. -/
  basis : Basis (Fin 2) ℤ N
  /-- The original surface as a reference fiber in the oriented frame. -/
  reference : MarkedReferenceFiber k₀ i basis r A marking

variable {i : N →+ V} {b : Basis (Fin 2) ℤ N} {r : ℕ}

/-- A specified toric presentation on a surface with finite free Picard group admits a
reference fiber marked by a finite coordinate lattice. The fan and ray labels are retained.
The reference center parameters are inverted if the lattice basis is transposed. -/
theorem exists_fin_marked_reference_fiber_of_toric_presentation
    [Module.Free ℤ Pic] [Module.Finite ℤ Pic]
    (P : D.ToricPresentation (X ↘ S) b i r) (hD : D.IsEffectiveCartier)
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n) :
    ∃ R : FiniteMarkedReferenceFiber i r A, R.reference.HasToricData P := by
  let a := (Module.finBasis ℤ Pic).equivFun.symm
  let μ := ((Chow.intersectionBilinForm k₀ X).isometryEquivOfCompLinearEquiv a).symm
  obtain ⟨b', R, hR⟩ := P.exists_marked_reference_fiber hD A μ
  exact ⟨⟨_, μ, b', R⟩, hR⟩

end QPainleve.SignedClusterModularGroup
