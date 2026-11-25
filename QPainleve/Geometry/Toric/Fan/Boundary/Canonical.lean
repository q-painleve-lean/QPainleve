/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import QPainleve.Geometry.Toric.Fan.Boundary.Node

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Canonical
import QPainleve.Geometry.Toric.Fan.CommonRefinement
import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Canonical
import QPainleve.Geometry.Toric.Fan.Smooth
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# The anticanonical boundary of a complete regular surface fan

The ideal of the reduced toric boundary represents the canonical class.
The plane calculation extends to every complete regular surface fan by
passing to a common regular subdivision and comparing the reduced total
transforms under the two nodal blowup towers.
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Φ "]" => Fan.algebraicRealization Φ
local notation "s[" Φ "]" => (X[Φ] ↘ S)
local notation "D[" Φ "," h "]" => Fan.boundaryIdeal Φ (Fan.IsComplete.nonempty_cones h)
local notation "K[" X "]" => LineBundleClass.mk (canonicalBundle ℂ X 2)

/-- The reduced toric boundary is anticanonical before a regular subdivision
of a complete rank-two fan exactly when it is anticanonical after it. -/
theorem IsSubdivision.canonicalClass_boundaryIdeal_iff (H : Ψ.IsSubdivision Φ)
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hc : Φ.IsComplete)
    (hN : finrank ℤ N = 2)
    (hD : (D[Φ,hc]).IsEffectiveCartier)
    (hE : (D[Ψ,H.isComplete_iff.mpr hc]).IsEffectiveCartier)
    [SmoothOfRelativeDimension 2 s[Φ]] [SmoothOfRelativeDimension 2 s[Ψ]] :
    LineBundleClass.mk hE.toInvertibleSheaf = K[X[Ψ]] ↔
      LineBundleClass.mk hD.toInvertibleSheaf = K[X[Φ]] := by
  let := hc.nonempty_cones
  let : Smooth s[Φ] := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian X[Φ] := isNoetherian_of_finiteType s[Φ]
  obtain ⟨_, _, T, e, hT, he, hB, -⟩ :=
    H.exists_toric_subdivision_blowup_tower hΦ hΨ hc.nonempty_cones hN
  have ht : e.hom ≫ T.toBase ≫ s[Φ] = s[Ψ] := by
    rw [← Category.assoc, he, algebraicRealization_over, algebraicRealization_over,
      FanHom.algebraicMap_comp_algebraicRealizationStructureMap]
  have hNodal : AtWorstNodalOfRelativeDimensionOne ((D[Φ,hc]).subschemeι ≫ s[Φ]) := by
    rw [algebraicRealization_over]
    exact Φ.atWorstNodalOfRelativeDimensionOne_boundary hΦ hc hN
  have hT' := Φ.algebraicRealization_over.symm ▸ hT
  exact hT'.canonicalClass_radical_comap_toBase_iff_of_iso hD hNodal e ht hE hB

/-- The Cartier ideal of the reduced boundary on a complete regular toric
surface represents its canonical class. -/
theorem canonicalClass_boundaryIdeal (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (b : Basis (Fin 2) ℤ N) (hD : (D[Φ,hc]).IsEffectiveCartier)
    [SmoothOfRelativeDimension 2 s[Φ]] :
    LineBundleClass.mk hD.toInvertibleSheaf = K[X[Φ]] := by
  let P := projectiveSpace b Φ.lattice
  let hp := isRegular_projectiveSpace b Φ.lattice
  let cp := isComplete_projectiveSpace b Φ.lattice
  let rankTwo := (finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  obtain ⟨Ω, H, J, hΩ⟩ :=
    (FanEquiv.refl P).exists_common_regular_subdivision_of_complete hΦ hp hc cp b
  let co := H.isComplete_iff.mpr hc
  let := cp.nonempty_cones
  let := co.nonempty_cones
  let : SmoothOfRelativeDimension 2 s[P] := by
    rw [algebraicRealization_over]
    exact rankTwo ▸ P.smoothOfRelativeDimension_algebraicRealizationStructureMap hp
  let : SmoothOfRelativeDimension 2 s[Ω] := by
    rw [algebraicRealization_over]
    exact rankTwo ▸ Ω.smoothOfRelativeDimension_algebraicRealizationStructureMap hΩ
  let hP := P.isEffectiveCartier_boundaryIdeal hp cp rankTwo
  let hO := Ω.isEffectiveCartier_boundaryIdeal hΩ co rankTwo
  exact (H.canonicalClass_boundaryIdeal_iff hΦ hΩ hc rankTwo hD hO).mp
    ((J.canonicalClass_boundaryIdeal_iff hp hΩ cp rankTwo hP hO).mpr
      (mk_toInvertibleSheaf_boundaryIdeal_projectivePlane b Φ.lattice hP))

end TauCeti.Toric.Fan
