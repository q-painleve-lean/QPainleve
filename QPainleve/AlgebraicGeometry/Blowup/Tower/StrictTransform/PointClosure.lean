/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Basic

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField

/-!
# Strict transforms of reduced point closures

If a point avoids all projected centers, its reduced closure has strict
transform given by the reduced closure of the lifted point. This lets two
factorizations of a birational projection compare scheme-theoretic strict
transforms by their generic points.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

/-- The strict transform of a reduced point closure is the reduced closure of
the lifted point if its projection is distinct from every projected center. -/
theorem strictTransform_vanishingIdeal_closure_singleton
    {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}
    (hT : IsClosedPointTower X T) (q : Y)
    (hq : ∀ j, T.toBase q ≠ hT.baseCenter j) :
    T.strictTransform (vanishingIdeal ⟨closure {T.toBase q}, isClosed_closure⟩) =
      vanishingIdeal ⟨closure {q}, isClosed_closure⟩ := by
  induction hT with
  | nil =>
    simp
  | @snoc n W T I hT p hp hI ih =>
    simp only [toBase_snoc, Scheme.Hom.comp_apply, strictTransform_snoc] at hq ⊢
    rw [ih (I.blowupToBase q) (fun j ↦ by
      simpa only [baseCenter_snoc_castSucc] using hq j.castSucc)]
    apply I.ker_blowupMap_vanishingIdeal_closure_singleton
    have hsupport : (I.support : Set W) = {p} := by
      rw [hI, Scheme.support_ker_fromSpecResidueField_of_isClosed hp]
    rw [support_comap, Closeds.coe_preimage, Set.mem_preimage, hsupport, Set.mem_singleton_iff]
    intro he
    exact hq (Fin.last n) (by rw [baseCenter_snoc_last, lastCenter_eq _ p hp hI, he])

end QPainleve.BlowupTower.IsClosedPointTower
