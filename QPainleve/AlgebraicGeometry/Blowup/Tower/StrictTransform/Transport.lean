/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Basic

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Basic
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.Stalk

/-!
# Strict-transform coefficients along ordered blowup towers

A lift between ordered towers identifies their strict transforms and
strict-transform coefficients when it identifies the initial ideals.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower

variable {X X' Y Y' : Scheme.{u}} {m : ℕ} {T : BlowupTower X m Y}
  {T' : BlowupTower X' m Y'} {e : X ≅ X'} {g : Y ≅ Y'}

/-- A lift between ordered blowup towers identifies the strict transforms of
ideals identified by the base isomorphism. -/
theorem IsLift.comap_strictTransform (h : IsLift e T T' g) (C : X'.IdealSheafData) :
    (T'.strictTransform C).comap g.hom = T.strictTransform (C.comap e.hom) := by
  induction T generalizing Y' with
  | nil =>
    cases T'
    obtain rfl := IsLift.nil_iff.mp h
    simp only [strictTransform_nil]
  | @snoc m W T I ih =>
    cases T' with
    | snoc T' I' =>
      obtain ⟨q, hq, hI, rfl⟩ := IsLift.snoc_iff.mp h
      simp only [strictTransform_snoc]
      refine (I'.comap_ker_blowupMap_subschemeι_blowupIso (T'.strictTransform C) q hI).trans ?_
      exact congrArg (fun D : W.IdealSheafData ↦ (I.blowupMap D.subschemeι).ker) (ih hq)

/-- A lift matching the ordered closed point centers preserves every
strict-transform coefficient, including those at infinitely near centers. -/
theorem IsLift.strictTransformCoefficients_eq (h : IsLift e T T' g)
    (hT : IsClosedPointTower X T) (hT' : IsClosedPointTower X' T')
    (C : X'.IdealSheafData) :
    hT.strictTransformCoefficients (C.comap e.hom) = hT'.strictTransformCoefficients C := by
  funext j
  induction T generalizing Y' with
  | nil => exact j.elim0
  | snoc T I ih =>
    cases T' with
    | snoc T' I' =>
      obtain ⟨q, hq, hI, rfl⟩ := IsLift.snoc_iff.mp h
      obtain ⟨hprefix, p, hp, hIp⟩ := IsClosedPointTower.snoc_iff.mp hT
      obtain ⟨hprefix', p', hp', hI'p'⟩ := IsClosedPointTower.snoc_iff.mp hT'
      refine Fin.lastCases ?_ (fun l ↦ ?_) j
      · have hmem : p ∈ (I.support : Set _) := by
          rw [hIp, Scheme.support_ker_fromSpecResidueField_of_isClosed hp]
          exact Set.mem_singleton p
        have hpq : q.hom p = p' := by
          rw [← hI, support_comap, Closeds.coe_preimage, Set.mem_preimage, hI'p',
            Scheme.support_ker_fromSpecResidueField_of_isClosed hp'] at hmem
          exact hmem
        simp only [IsClosedPointTower.strictTransformCoefficients_snoc_last _ _ p hp hIp,
          IsClosedPointTower.strictTransformCoefficients_snoc_last _ _ p' hp' hI'p',
          ← hq.comap_strictTransform C, stalkOrder_comap_of_isIso_stalkMap, hpq]
      · simpa only [IsClosedPointTower.strictTransformCoefficients_snoc_castSucc] using
          ih hq hprefix hprefix' l

end QPainleve.BlowupTower
