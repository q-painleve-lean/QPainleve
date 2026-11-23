/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.Basic
public import TauCeti.AlgebraicGeometry.Curves.Normalization

import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Curves.Genus.Zero
import TauCeti.AlgebraicGeometry.Geometrically.GlobalSections
import TauCeti.AlgebraicGeometry.Normalization.Finite
import TauCeti.AlgebraicGeometry.RationalPoint.Image

/-!
# Integral proper curves of arithmetic genus zero

Over an algebraically closed field, the normalization comparison for the arithmetic
genus forces a proper integral curve of genus zero to be regular. A rational point
then gives an isomorphism to the projective line over the field. This connects the
normalization formula with Tau Ceti's genus-zero classification for regular curves.
See [Stacks Project, Section 53.10](https://stacks.math.columbia.edu/tag/0C6L).
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
  [C.Over (Spec (.of k))] [C.IsCurveOver k]

/-- A proper integral curve of arithmetic genus zero over an algebraically closed field
is regular. The genus of the normalization and the dimension of the global sections of
the normalization cokernel both vanish. -/
theorem isRegular_of_genus_eq_zero_of_isAlgClosed (hC : C.genus k = 0) : IsRegular C := by
  let g := C.fromSpecStalk (genericPoint C)
  let : g.normalization.Over (Spec (.of k)) := ⟨g.fromNormalization ≫ C ↘ Spec (.of k)⟩
  let : g.fromNormalization.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsFinite g.fromNormalization :=
    isFinite_fromNormalization_fromSpecStalk_genericPoint_of_locallyOfFiniteType
      (C ↘ Spec (.of k))
  have : g.normalization.IsCurveOver k := IsCurveOver.isCurveOver_normalization (X := C) k
  have hconstants : Function.Surjective (Modules.baseRingToGlobalSections k g.normalization) := by
    rw [funext (Modules.baseRingToGlobalSections_apply k g.normalization)]
    exact (g.normalization.appTop_bijective_of_isAlgClosed_of_isReduced_of_connectedSpace
      k).surjective.comp (ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective
  have hgen : g.normalization.genus k ≤ C.genus k :=
    genus_le_of_isModification k g.fromNormalization
  have hnormalization : g.normalization.genus k = 0 := Nat.eq_zero_of_le_zero (hC ▸ hgen)
  exact (IsCurveOver.isRegular_iff_genus_eq_genus_normalization k hconstants).mpr
    (hC.trans hnormalization.symm)

/-- Over an algebraically closed field, a proper integral curve has arithmetic genus zero
exactly when it is isomorphic to the projective line over the field. -/
theorem genus_eq_zero_iff_exists_iso_projectiveLine :
    C.genus k = 0 ↔ ∃ e : C ≅ projectiveLine k, e.hom.IsOver (Spec (.of k)) := by
  constructor
  · intro h
    have : IsRegular C := isRegular_of_genus_eq_zero_of_isAlgClosed h
    have : IsNoetherian C := IsCurveOver.isNoetherian k C
    have (x : CodimensionOnePoint C) : IsDiscreteValuationRing (C.presheaf.stalk (x : C)) :=
      inferInstance
    obtain ⟨p, hp, -⟩ := isOpen_univ.isLocallyClosed.exists_rationalPoint_mem
      (C ↘ Spec (.of k)) Set.univ_nonempty
    exact C.exists_iso_projectiveLine_of_genus_eq_zero_of_section
      (by simpa only [genus_def] using h) hp
  · rintro ⟨e, he⟩
    have : e.hom.IsOver (Spec (.of k)) := he
    rw [genus_def, e.hom.finrank_cohomology_trivial_of_isIso k 1, ← genus_def]
    exact projectiveLine.genus_eq_zero k

end AlgebraicGeometry.Scheme
