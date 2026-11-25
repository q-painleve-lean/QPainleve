/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Canonical
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField

/-!
# The canonical class of a point-blowup tower

The canonical class has coefficient one at each total-transform exceptional divisor,
by iterating the canonical-bundle formula for a single point blowup.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open LineBundleClass

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}
  (k : Type u) [Field k] [PerfectField k] [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "f" => (X ↘ S)

-- Keep the structure morphism explicit while reassociating the composite at each stage.
private noncomputable def canonicalClass {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k))
    (hg : SmoothOfRelativeDimension 2 g) : LineBundleClass Z :=
  letI : Z.Over (Spec (.of k)) := ⟨g⟩
  letI : SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k)) := hg
  mk (canonicalBundle k Z 2)

private theorem mk_canonicalBundle_picardHom_aux (hT : IsClosedPointTower X T) :
    ∀ (g : Y ⟶ Spec (.of k)), g = T.toBase ≫ f →
      ∀ (hg : SmoothOfRelativeDimension 2 g),
        canonicalClass k g hg = (T.picardHom
          (Additive.ofMul (canonicalClass k f inferInstance), fun _ ↦ 1)).toMul := by
  induction hT with
  | nil =>
    intro g hg _
    rw [toBase_nil, Category.id_comp] at hg
    subst g
    rw [picardHom_nil, toMul_ofMul]
  | @snoc d W U I hU p hp hI ih =>
    rw [W.ker_fromSpecResidueField_eq_vanishingIdeal] at hI
    subst I
    intro g' hg' hg
    rw [toBase_snoc, Category.assoc] at hg'
    subst g'
    let g := U.toBase ≫ f
    let : W.Over (Spec (.of k)) := ⟨g⟩
    have hgsmooth : SmoothOfRelativeDimension 2 g := hU.smoothOfRelativeDimension f
    let : SmoothOfRelativeDimension 2 (W ↘ Spec (.of k)) := hgsmooth
    rw [picardHom_snoc_apply_toMul, ← ih g rfl hgsmooth, zpow_one]
    -- This is the single-blowup comparison on the same reduced center ideal.
    exact Scheme.IdealSheafData.mk_canonicalBundle_pointBlowup k hp

/-- Along a tower of closed-point blowups, the canonical class has the base canonical
class as its base coordinate and coefficient one at every total-transform exceptional divisor. -/
theorem mk_canonicalBundle_picardHom (hT : IsClosedPointTower X T)
    [Y.Over S] [T.toBase.IsOver S] [SmoothOfRelativeDimension 2 (Y ↘ S)] :
    mk (canonicalBundle k Y 2) =
      (T.picardHom (Additive.ofMul (mk (canonicalBundle k X 2)), fun _ ↦ 1)).toMul :=
  mk_canonicalBundle_picardHom_aux k hT (Y ↘ S) (comp_over T.toBase S).symm inferInstance

end QPainleve.BlowupTower.IsClosedPointTower
