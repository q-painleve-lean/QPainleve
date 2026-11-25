/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import QPainleve.Geometry.Toric.Fan.Presentation.Basic

import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Canonical
import QPainleve.Geometry.Toric.Fan.Boundary.Canonical
import QPainleve.Geometry.Toric.Fan.Logarithmic.InternalBlowup
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback

/-!
# Anticanonical boundaries from toric presentations

Internal blowups preserve the anticanonical class of the strict boundary,
and a nodal tower detects the anticanonical condition on its original pair.
Thus the condition holds on the surface of a toric presentation, even
when some ordered internal centers are infinitely near.
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry TauCeti.Toric Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.IdealSheafData

local notation "S" => Spec (CommRingCat.of ℂ)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N}
  {X : Scheme} [X.Over S] [IsIntegral X] [IsNoetherian X]
  [SmoothOfRelativeDimension 2 (X ↘ S)] {D : X.IdealSheafData}

/-- A nodal Cartier boundary with a toric presentation is anticanonical. -/
theorem HasToricPresentation.canonicalClass (h : D.HasToricPresentation (X ↘ S) b i)
    (hD : D.IsEffectiveCartier) (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S)) :
    LineBundleClass.mk hD.toInvertibleSheaf = LineBundleClass.mk (canonicalBundle ℂ X 2) := by
  obtain ⟨Φ, hΦ, hc, n, rays, c, m, Y, T, hT, e, he, hB⟩ := (hasToricPresentation_iff ..).mp h
  let := hc.nonempty_cones
  let rankTwo := (finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let A := Fan.internalBlowupTower b rays c
  let : A.1.Over S := ⟨A.2.toTower.toBase ≫ Φ.algebraicRealization ↘ S⟩
  let : SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S) := by
    rw [Fan.algebraicRealization_over]
    exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : SmoothOfRelativeDimension 2 (A.1 ↘ S) := by
    exact (Fan.isClosedPointTower_internalBlowupTower b rays c).smoothOfRelativeDimension _
  have hStructure : A.1 ↘ S = A.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap :=
    congrArg (A.2.toTower.toBase ≫ ·) Φ.algebraicRealization_over
  have he' : e.hom ≫ T.toBase ≫ X ↘ S = A.1 ↘ S := he.trans hStructure.symm
  let hF : A.2.boundaryι.ker.IsEffectiveCartier :=
    hB ▸ (hT.radical_comap_toBase hD hN).1.comap e.hom
  let hBase := Φ.isEffectiveCartier_boundaryIdeal hΦ hc rankTwo
  exact (hT.canonicalClass_radical_comap_toBase_iff_of_iso hD hN e he' hF hB).mp
    (Fan.canonicalClass_internalBlowupTower b rays c hΦ hBase hF
      (Φ.canonicalClass_boundaryIdeal hΦ hc b hBase))

end AlgebraicGeometry.Scheme.IdealSheafData
