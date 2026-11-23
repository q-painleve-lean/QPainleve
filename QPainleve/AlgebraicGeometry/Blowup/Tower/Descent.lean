/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point

import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Point.Cohomology
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Descent.Contraction
import TauCeti.AlgebraicGeometry.Morphisms.Epi
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Descent along towers of closed point blowups

The projection from a tower of closed point blowups of a smooth surface identifies the
sections of the structure sheaf on every open with those on its inverse image. The
projection is proper and surjective. A map constant on its fibers therefore descends
uniquely, and the descent preserves the specified composite to a base scheme.

The descent uses Tau Ceti's `Scheme.Hom.existsUnique_comp_eq_of_universallyClosed`.
For its use in surface factorization, see
[Stacks Project, Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R).
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [PerfectField k]
variable {X Y Z S : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}
variable (hT : IsClosedPointTower X T) (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]

include hT f

private theorem contraction_properties :
    IsProper T.toBase ∧ Surjective T.toBase ∧ ∀ U, IsIso (T.toBase.app U) := by
  induction hT with
  | nil =>
    simp only [toBase_nil]
    refine ⟨inferInstance, inferInstance, fun U ↦ ?_⟩
    rw [toBase_nil, Scheme.Hom.id_app]
    exact (inferInstance : IsIso (𝟙 Γ(X, U)))
  | @snoc _ W R I hR p hp hI ih =>
    obtain ⟨hproper, hsurjective, happ⟩ := ih
    subst I
    rw [toBase_snoc, Scheme.ker_fromSpecResidueField_eq_vanishingIdeal]
    have := hR.smoothOfRelativeDimension f
    obtain ⟨hsmooth, hdim⟩ :=
      (smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (R.toBase ≫ f) 2).mp inferInstance
    have := LocallyOfFiniteType.isLocallyNoetherian (R.toBase ≫ f)
    have := isRegularLocalRing_stalk_of_smooth (R.toBase ≫ f) p
    have := Scheme.IdealSheafData.surjective_blowupToBase_point hp (hdim p hp)
    refine ⟨inferInstance, inferInstance, fun U ↦ ?_⟩
    rw [Scheme.Hom.comp_app]
    exact IsIso.comp_isIso' (happ U)
      (Scheme.IdealSheafData.isIso_app_pointBlowup hp (hdim p hp) (R.toBase ⁻¹ᵁ U))

/-- Pullback along a closed point blowup tower of a smooth surface identifies sections
of the structure sheaf on any open with sections on its inverse image. -/
theorem isIso_app_toBase (U : X.Opens) : IsIso (T.toBase.app U) :=
  (hT.contraction_properties f).2.2 U

/-- The projection of a closed point blowup tower of a smooth surface is an epimorphism. -/
theorem epi_toBase : Epi T.toBase := by
  have := (hT.contraction_properties f).2.1
  exact T.toBase.epi_of_surjective_of_app_injective fun U ↦ by
    have := hT.isIso_app_toBase f U
    exact (ConcreteCategory.bijective_of_isIso (T.toBase.app U)).1

/-- A morphism constant on the fibers of a closed point blowup tower of a smooth surface
descends uniquely to the base of the tower. -/
theorem existsUnique_comp_eq_toBase (g : Y ⟶ Z) (hg : Function.FactorsThrough g T.toBase) :
    ∃! h : X ⟶ Z, T.toBase ≫ h = g := by
  obtain ⟨hproper, hsurjective, _⟩ := hT.contraction_properties f
  exact T.toBase.existsUnique_comp_eq_of_universallyClosed (hT.isIso_app_toBase f) g hg

/-- The descent of a morphism constant on a surface blowup tower's fibers preserves its
specified composite to another scheme. -/
theorem existsUnique_comp_eq_toBase_over (g : Y ⟶ Z) (p : X ⟶ S) (q : Z ⟶ S)
    (hcomm : g ≫ q = T.toBase ≫ p) (hg : Function.FactorsThrough g T.toBase) :
    ∃! h : X ⟶ Z, T.toBase ≫ h = g ∧ h ≫ q = p := by
  obtain ⟨h, hh, huniq⟩ := hT.existsUnique_comp_eq_toBase f g hg
  have := hT.epi_toBase f
  refine ⟨h, ⟨hh, (cancel_epi T.toBase).mp ?_⟩, fun h' hh' ↦ huniq h' hh'.1⟩
  rwa [← Category.assoc, hh]

end QPainleve.BlowupTower.IsClosedPointTower
