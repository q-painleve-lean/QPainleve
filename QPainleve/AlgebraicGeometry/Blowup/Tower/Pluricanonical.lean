/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Canonical
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField

/-!
# Pluricanonical sections under point blowups

The comparison of pluricanonical sections for a single closed point blowup iterates along
towers and identifies the spaces of sections on two smooth surfaces with a common resolution.

The bicanonical case gives the space used in [Vakil, *Complex Algebraic Surfaces*, Class 16][Vakil].

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass16A.pdf
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y Z : Scheme.{u}} {n d : ℕ} {T : BlowupTower X n Z}
  (k : Type u) [Field k] [PerfectField k] [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

private theorem nonempty_cohomologyZero_pluricanonicalLinearEquiv_of_comp
    (hT : IsClosedPointTower X T) (m : ℕ) (g : Z ⟶ Spec (.of k))
    (hg : g = T.toBase ≫ X ↘ Spec (.of k)) (hgSmooth : SmoothOfRelativeDimension 2 g) :
    letI : Z.Over (Spec (.of k)) := ⟨g⟩
    letI : SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k)) := hgSmooth
    Nonempty (Cohomology ((canonicalBundle k X 2).tensorPow m).obj 0 ≃ₗ[k]
      Cohomology ((canonicalBundle k Z 2).tensorPow m).obj 0) := by
  induction hT with
  | nil =>
    rw [toBase_nil, Category.id_comp] at hg
    subst g
    exact ⟨LinearEquiv.refl k _⟩
  | @snoc _ W S I hS p hp hI ih =>
    have hcenter := hI.trans (W.ker_fromSpecResidueField_eq_vanishingIdeal p)
    clear hI
    subst I
    rw [toBase_snoc, Category.assoc] at hg
    subst g
    let : W.Over (Spec (.of k)) := ⟨S.toBase ≫ X ↘ Spec (.of k)⟩
    have : SmoothOfRelativeDimension 2 (W ↘ Spec (.of k)) :=
      hS.smoothOfRelativeDimension (X ↘ Spec (.of k))
    obtain ⟨e⟩ := ih (W ↘ Spec (.of k)) rfl inferInstance
    exact ⟨e.trans (Scheme.IdealSheafData.cohomologyZeroPluricanonicalLinearEquiv k hp m)⟩

variable [Z.Over (Spec (.of k))]

/-- A tower of closed point blowups of a smooth surface preserves each pluricanonical
space. The comparison applies to towers with infinitely near centers. -/
theorem nonempty_cohomologyZero_pluricanonicalLinearEquiv
    [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k))]
    (hT : IsClosedPointTower X T) [T.toBase.IsOver (Spec (.of k))] (m : ℕ) :
    Nonempty (Cohomology ((canonicalBundle k X 2).tensorPow m).obj 0 ≃ₗ[k]
      Cohomology ((canonicalBundle k Z 2).tensorPow m).obj 0) :=
  nonempty_cohomologyZero_pluricanonicalLinearEquiv_of_comp k hT m (Z ↘ Spec (.of k))
    (comp_over T.toBase (Spec (.of k))).symm inferInstance

variable [Y.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  {U : BlowupTower Y d Z}

/-- Two smooth surfaces with a common resolution by closed point blowups have isomorphic
spaces of global sections of every nonnegative tensor power of their canonical bundles. -/
theorem nonempty_cohomologyZero_pluricanonicalLinearEquiv_of_common_resolution
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Y U)
    [T.toBase.IsOver (Spec (.of k))] [U.toBase.IsOver (Spec (.of k))] (m : ℕ) :
    Nonempty (Cohomology ((canonicalBundle k X 2).tensorPow m).obj 0 ≃ₗ[k]
      Cohomology ((canonicalBundle k Y 2).tensorPow m).obj 0) := by
  have : SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k)) := by
    rw [← comp_over T.toBase (Spec (.of k))]
    exact hT.smoothOfRelativeDimension (X ↘ Spec (.of k))
  obtain ⟨eT⟩ := hT.nonempty_cohomologyZero_pluricanonicalLinearEquiv k m
  obtain ⟨eU⟩ := hU.nonempty_cohomologyZero_pluricanonicalLinearEquiv k m
  exact ⟨eT.trans eU.symm⟩

end QPainleve.BlowupTower.IsClosedPointTower
