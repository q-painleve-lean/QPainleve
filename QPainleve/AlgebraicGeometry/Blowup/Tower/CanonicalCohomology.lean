/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Point.CanonicalCohomology
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField

/-!
# Canonical cohomology along towers of point blowups

The comparison on canonical cohomology composes along a specified tower of closed point
blowups, including towers with infinitely near centers. In degree two its inverse
transports a trace from the original surface to the blown-up model.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Z : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Z}
  (k : Type u) [Field k] [PerfectField k] [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

private def cohomologyCanonicalBundleLinearEquivStep {W : Scheme.{u}}
    [W.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (W ↘ Spec (.of k))]
    (I : W.IdealSheafData) {p : W} (hp : IsClosed ({p} : Set W))
    (hI : I = (W.fromSpecResidueField p).ker)
    (hsmooth : SmoothOfRelativeDimension 2 (I.blowupToBase ≫ W ↘ Spec (.of k))) (q : ℕ) :
    letI : I.blowup.Over (Spec (.of k)) := ⟨I.blowupToBase ≫ W ↘ Spec (.of k)⟩
    letI : SmoothOfRelativeDimension 2 (I.blowup ↘ Spec (.of k)) := hsmooth
    Cohomology (canonicalBundle k W 2).obj q ≃ₗ[k]
      Cohomology (canonicalBundle k I.blowup 2).obj q := by
  have hcenter := hI.trans (W.ker_fromSpecResidueField_eq_vanishingIdeal p)
  clear hI
  subst I
  exact Scheme.IdealSheafData.cohomologyCanonicalBundlePointBlowupLinearEquiv k hp q

private def cohomologyCanonicalBundleLinearEquivOfComp
    (hT : IsClosedPointTower X T) (q : ℕ) (g : Z ⟶ Spec (.of k))
    (hg : g = T.toBase ≫ X ↘ Spec (.of k)) (hsmooth : SmoothOfRelativeDimension 2 g) :
    letI : Z.Over (Spec (.of k)) := ⟨g⟩
    letI : SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k)) := hsmooth
    Cohomology (canonicalBundle k X 2).obj q ≃ₗ[k] Cohomology (canonicalBundle k Z 2).obj q := by
  induction T with
  | nil =>
    rw [toBase_nil, Category.id_comp] at hg
    subst g
    exact LinearEquiv.refl k _
  | @snoc _ W S I ih =>
    obtain ⟨hS, hcenter⟩ := snoc_iff.mp hT
    rw [toBase_snoc, Category.assoc] at hg
    subst g
    let : W.Over (Spec (.of k)) := ⟨S.toBase ≫ X ↘ Spec (.of k)⟩
    let : SmoothOfRelativeDimension 2 (W ↘ Spec (.of k)) :=
      hS.smoothOfRelativeDimension (X ↘ Spec (.of k))
    exact (ih hS (W ↘ Spec (.of k)) rfl inferInstance).trans
      (cohomologyCanonicalBundleLinearEquivStep k I hcenter.choose_spec.1
        hcenter.choose_spec.2 hsmooth q)

/-- The cohomology comparison for the canonical bundle along a specified tower of closed
point blowups. The projection is a morphism over the base field. -/
def cohomologyCanonicalBundleLinearEquiv
    [Z.Over (Spec (.of k))] (hT : IsClosedPointTower X T)
    [T.toBase.IsOver (Spec (.of k))] (q : ℕ) :
    let : SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k)) :=
      comp_over T.toBase (Spec (.of k)) ▸ hT.smoothOfRelativeDimension (X ↘ Spec (.of k))
    Cohomology (canonicalBundle k X 2).obj q ≃ₗ[k] Cohomology (canonicalBundle k Z 2).obj q :=
  cohomologyCanonicalBundleLinearEquivOfComp k hT q (Z ↘ Spec (.of k))
    (comp_over T.toBase (Spec (.of k))).symm
    (comp_over T.toBase (Spec (.of k)) ▸ hT.smoothOfRelativeDimension (X ↘ Spec (.of k)))

end QPainleve.BlowupTower.IsClosedPointTower
