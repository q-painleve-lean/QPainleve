/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import QPainleve.Geometry.Toric.Fan.Boundary.Basic

/-!
# The boundary under a fan subdivision

The inverse image of the dense torus under a subdivision is the dense torus.
Consequently the reduced inverse image of the toric boundary is the toric
boundary of the subdividing fan.
-/

public section

open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.IsSubdivision

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ)
  (hΦ : Nonempty Φ.cones) (hΨ : Nonempty Ψ.cones)

/-- The reduced inverse image of the toric boundary is the boundary of the subdivision. -/
theorem radical_comap_boundaryIdeal :
    ((Ψ.boundaryIdeal hΨ).comap h.toFanHom.algebraicMap).radical = Φ.boundaryIdeal hΦ := by
  rw [← vanishingIdeal_support, Φ.boundaryIdeal_def]
  congr 1
  apply SetLike.coe_injective
  rw [support_comap, Closeds.coe_preimage, Ψ.support_boundaryIdeal,
    Set.preimage_compl, h.preimage_range_denseTorusι hΦ hΨ]
  rfl

end TauCeti.Toric.Fan.IsSubdivision
