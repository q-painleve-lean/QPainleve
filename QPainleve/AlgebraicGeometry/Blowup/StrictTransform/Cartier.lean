/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Multiplicity

import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Integral
import QPainleve.AlgebraicGeometry.Blowup.Smooth
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Cartier reduced total transforms on smooth surfaces

After blowing up a closed point on a reduced effective Cartier divisor,
the reduced total transform is effective Cartier. Its ideal is the product
of the strict-transform ideal and the reduced exceptional ideal.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  {D : X.IdealSheafData} {p : X}

local notation "I" => vanishingIdeal (Closeds.closure (singleton p))

/-- At a closed point on a reduced Cartier divisor, its reduced total transform
is Cartier. It consists of the strict transform and the reduced exceptional divisor. -/
theorem IsEffectiveCartier.radical_comap_blowupToBase_of_closedPoint
    (hD : D.IsEffectiveCartier)
    (s : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 s] [QuasiCompact s] [IsReduced D.subscheme]
    (hp : IsClosed ({p} : Set X)) (hpD : p ∈ D.support) :
    (D.comap (I).blowupToBase).radical.IsEffectiveCartier := by
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 _
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have := isRegularLocalRing_stalk_of_smooth s p
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq s 2).mp
    inferInstance).2 p hp
  have hIntegral : IsIntegral (I).blowup := isIntegral_blowup_closed_point s hp
  have : Surjective (I).blowupToBase := surjective_blowupToBase_point hp hdim
  have : IsReduced ((I).comap (I).blowupToBase).subscheme :=
    @isReduced_of_isIntegral _ (isIntegral_exceptional_blowup_closed_point hdim hp)
  have hDI : D ≤ I := (X.ker_fromSpecResidueField_eq_vanishingIdeal p) ▸
    (D.le_ker_fromSpecResidueField_iff_mem_support hp).mpr hpD
  rw [(I).radical_comap_blowupToBase_eq_ker_blowupMap_subschemeι_mul D hDI]
  have hCartier : (D.comap (I).blowupToBase).IsEffectiveCartier :=
    hD.comap_of_isDominant (I).blowupToBase
  let : IsIntegral
      (vanishingIdeal ⟨closure (singleton p), isClosed_closure⟩).blowup := hIntegral
  exact TauCeti.isEffectiveCartier_mul
    (hD.exists_strictTransform_cartierDivisor hp hdim hCartier).choose
    (I).isEffectiveCartier_comap_blowupToBase

end AlgebraicGeometry.Scheme.IdealSheafData
