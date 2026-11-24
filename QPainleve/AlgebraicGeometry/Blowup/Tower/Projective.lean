/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Blowup.Point.Projective
import QPainleve.AlgebraicGeometry.Blowup.Projective.Global

/-!
# Projectivity along blowup towers

A finite tower of blowups over a projective scheme is projective over the
same Noetherian coefficient ring. For a smooth integral surface over an
algebraically closed field, projectivity also descends through a tower of
closed point blowups by `Scheme.IsProjectiveOver.of_pointBlowup`.
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

/-- The base of a tower of closed point blowups of a smooth integral surface
over an algebraically closed field is projective if the last surface is projective. -/
theorem IsClosedPointTower.isProjectiveOver_base {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)
    [X.Over (Spec (.of k))] [IsIntegral X] [IsNoetherian X]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] :
    let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ (X ↘ Spec (.of k))⟩
    Y.IsProjectiveOver k → X.IsProjectiveOver k := by
  induction hT with
  | nil =>
    dsimp only
    rw [toBase_nil, Category.id_comp]
    exact id
  | @snoc _ W U I hU p hp he ih =>
    subst I
    let : W.Over (Spec (.of k)) := ⟨U.toBase ≫ (X ↘ Spec (.of k))⟩
    let : IsIntegral W := hU.isIntegral (X ↘ Spec (.of k))
    let : IsNoetherian W := U.isNoetherian
    let : SmoothOfRelativeDimension 2 (W ↘ Spec (.of k)) :=
      hU.smoothOfRelativeDimension (X ↘ Spec (.of k))
    let I := (W.fromSpecResidueField p).ker
    have heq : (U.snoc I).toBase ≫ (X ↘ Spec (.of k)) =
        I.blowupToBase ≫ U.toBase ≫ (X ↘ Spec (.of k)) := by
      rw [toBase_snoc, Category.assoc]
    intro hOver hproj
    have hOverEq : hOver = ⟨I.blowupToBase ≫ U.toBase ≫ (X ↘ Spec (.of k))⟩ := by
      exact congrArg (fun f ↦ (⟨f⟩ : I.blowup.Over (Spec (.of k)))) heq
    exact ih (Scheme.IsProjectiveOver.of_pointBlowup p hp (hOverEq ▸ hproj))

end QPainleve.BlowupTower
