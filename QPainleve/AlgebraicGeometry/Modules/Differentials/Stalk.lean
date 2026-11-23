/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Quasicoherent
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.StandardSmooth

/-!
# Differentials of the stalks of a smooth scheme

A smooth scheme over a field has a basis of Kähler differentials at each stalk
indexed by its relative dimension. Localization of the standard smooth chart
transports the basis by `KaehlerDifferential.isBaseChange_of_formallyEtale`.
-/

public section

open CategoryTheory Opposite TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The differentials of the local ring of a smooth scheme over a field have a basis
indexed by the relative dimension. -/
theorem nonempty_basis_kaehlerDifferential_stalk {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (n : ℕ) [SmoothOfRelativeDimension n (X ↘ Spec (.of k))]
    (x : X) :
    Nonempty (Module.Basis (Fin n) (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k]) := by
  obtain ⟨U, hxU, hU⟩ := exists_isStandardSmoothOfRelativeDimension k n x
  let A := Γ(X, U)
  let P := X.presheaf.stalk x
  let : Algebra k A := ((X.baseRingToStructurePresheaf k).app (op U.val)).hom.toAlgebra
  let : Algebra A P := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let : IsScalarTower k A P := isScalarTower_base_section_stalk k X ⟨x, hxU⟩
  let q := (U.property.primeIdealOf ⟨x, hxU⟩).asIdeal
  have : IsLocalization q.primeCompl P := U.property.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.FormallyEtale A P := .of_isLocalization q.primeCompl
  have : Algebra.IsStandardSmoothOfRelativeDimension n k A := hU.toAlgebra
  have : Algebra.IsStandardSmooth k A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Nonempty U.val := ⟨⟨x, hxU⟩⟩
  let b := Module.finBasisOfFinrankEq A Ω[A⁄k]
    (Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n))
  exact ⟨(KaehlerDifferential.isBaseChange_of_formallyEtale k A P).basis b⟩

end AlgebraicGeometry.Scheme
