/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus
import TauCeti.AlgebraicGeometry.Morphisms.FiniteType
import TauCeti.RingTheory.RegularLocalRing.Smooth

/-!
# Smoothness at a regular point over a perfect field

The affine criterion for the smooth locus identifies smoothness at a point with formal
smoothness of its local algebra. Over a perfect field this follows from regularity.
-/

public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

/-- A regular point of a scheme locally of finite presentation over a perfect field lies
in the smooth locus of its structure morphism. -/
theorem mem_smoothLocus_of_isRegularLocalRing_over_perfectField {k : Type u}
    [Field k] [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFinitePresentation f] (x : X) [IsRegularLocalRing (X.presheaf.stalk x)] :
    x ∈ f.smoothLocus := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let φ := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top
  let := φ.hom.toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := f.finiteType_ΓSpecIso_inv_comp_appLE hU
  let q := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  let := (X.presheaf.germ U x hx).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨x, hx⟩
  let e := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) (X.presheaf.stalk x)
  have : IsRegularLocalRing (Localization.AtPrime q) :=
    IsRegularLocalRing.of_ringEquiv e.toRingEquiv.symm
  have : Algebra.EssFiniteType k (IsLocalRing.ResidueField (Localization.AtPrime q)) :=
    .comp k (Localization.AtPrime q) _
  have : Algebra.FormallySmooth k (IsLocalRing.ResidueField (Localization.AtPrime q)) :=
    Algebra.FormallySmooth.of_perfectField
  exact (f.mem_smoothLocus_iff_isSmoothAt (U := ⟨U, hU⟩) hx).mpr
    (TauCeti.formallySmooth_of_isRegularLocalRing (k := k) (S := Localization.AtPrime q))

end AlgebraicGeometry.Scheme.Hom
