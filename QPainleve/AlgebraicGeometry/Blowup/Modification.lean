/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic

import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.SchematicDensity
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Blowups that are modifications

A blowup with nowhere dense center on a locally Noetherian scheme is a modification.
The isomorphism away from the center has dense preimage because the exceptional ideal
is effective Cartier.
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}}

/-- On a locally Noetherian scheme, the blowup of a center with dense complement is a
modification. -/
theorem isModification_blowupToBase [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (hI : Dense (I.support.compl : Set X)) : IsModification I.blowupToBase := by
  let E := I.comap I.blowupToBase
  have : IsLocallyNoetherian I.blowup := LocallyOfFiniteType.isLocallyNoetherian I.blowupToBase
  have : IsSchemeTheoreticallyDominant (Scheme.Opens.ι E.support.compl) :=
    I.isEffectiveCartier_comap_blowupToBase.isSchemeTheoreticallyDominant_support_compl_ι
  have hE : Dense (E.support.compl : Set I.blowup) := by
    have h := (inferInstance : IsDominant (Scheme.Opens.ι E.support.compl)).denseRange
    simpa only [DenseRange, Opens.range_ι] using h
  have hpre : E.support.compl = I.blowupToBase ⁻¹ᵁ I.support.compl :=
    I.compl_support_comap I.blowupToBase
  exact ⟨⟨I.support.compl, hI, hpre ▸ hE, I.isIso_blowupToBase_restrict_compl_support⟩⟩

end AlgebraicGeometry.Scheme.IdealSheafData
