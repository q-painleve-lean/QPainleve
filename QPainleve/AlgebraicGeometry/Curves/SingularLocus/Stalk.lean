/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Scheme.Stalk
public import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk

/-!
# The stalk ideal of the singular subscheme

For a syntomic relative curve over an affine base, the ideal of the singular
subscheme at a point is the first Fitting ideal of the Kähler differentials
of the local ring.
-/

public section

open CategoryTheory Opposite TopologicalSpace KaehlerDifferential
open TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The first Fitting ideal of the differentials of a syntomic curve's local ring
is the stalk ideal of its singular subscheme. -/
theorem singularLocus_stalkIdeal_eq_fittingIdeal
    {k : Type u} [CommRing k] {C : Scheme.{u}} [C.Over (Spec (.of k))]
    [SyntomicOfRelativeDimension 1 (C ↘ Spec (.of k))] (p : C) :
    letI := C.essFiniteType_stalk k p
    (C.singularLocus k).stalkIdeal p =
      fittingIdeal (C.presheaf.stalk p) Ω[C.presheaf.stalk p⁄k] 1 := by
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top p)
  let V : C.affineOpens := ⟨U, hU⟩
  let A := Γ(C, V)
  let L := C.presheaf.stalk p
  let : Algebra k A := ((C.baseRingToStructurePresheaf k).app (op U)).hom.toAlgebra
  let := C.presheaf.algebra_section_stalk ⟨p, hpU⟩
  let : IsScalarTower k A L := isScalarTower_base_section_stalk k C ⟨p, hpU⟩
  let q := (hU.primeIdealOf ⟨p, hpU⟩).asIdeal
  have : IsLocalization q.primeCompl L := hU.isLocalization_stalk ⟨p, hpU⟩
  have : Algebra.FormallyEtale A L := .of_isLocalization q.primeCompl
  have : Algebra.FiniteType k A := finiteType_sections_of_locallyOfFiniteType k C V
  have : Algebra.EssFiniteType k L := C.essFiniteType_stalk k p
  rw [(C.singularLocus k).stalkIdeal_eq_map V p hpU, C.singularLocus_ideal (R := k) V,
    (KaehlerDifferential.isBaseChange_of_formallyEtale k A L).fittingIdeal_eq_map 1,
    C.presheaf.stalk_open_algebraMap ⟨p, hpU⟩]

end AlgebraicGeometry.Scheme
