/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Blowup.Projective.Global

/-!
# Projectivity along blowup towers

A finite tower of blowups over a projective scheme is projective over the
same Noetherian coefficient ring.
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry

namespace QPainleve.BlowupTower

universe u

/-- The final scheme of a finite blowup tower over a projective scheme is projective
over the original Noetherian coefficient ring. -/
theorem isProjectiveOver {X Y : Scheme.{u}} {n : ℕ} (T : BlowupTower X n Y)
    (R : Type u) [CommRing R] [IsNoetherianRing R] [X.Over (Spec (.of R))] [X.IsProjectiveOver R] :
    let : Y.Over (Spec (.of R)) := ⟨T.toBase ≫ (X ↘ Spec (.of R))⟩
    Y.IsProjectiveOver R := by
  induction T with
  | nil =>
    dsimp only
    rw [toBase_nil, Category.id_comp]
    exact (inferInstance : X.IsProjectiveOver R)
  | @snoc _ Z U I ih =>
    let : Z.Over (Spec (.of R)) := ⟨U.toBase ≫ (X ↘ Spec (.of R))⟩
    have : Z.IsProjectiveOver R := ih
    dsimp only
    rw [toBase_snoc, Category.assoc]
    exact I.isProjectiveOver_blowup_of_isNoetherianRing R

end QPainleve.BlowupTower
