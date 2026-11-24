/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField

/-!
# Lifting ordered blowups with distinct projected centers

For disjoint centers, the images on the base determine the center ideals at
all stages. An isomorphism that matches the images in order therefore lifts
through the two towers and preserves their total exceptional classes.
-/

public section

open AlgebraicGeometry CategoryTheory

universe u

namespace QPainleve.BlowupTower

variable {X X' Y Y' : Scheme.{u}} {n : ℕ}

namespace IsClosedPointTower

/-- Two ordered towers of closed-point blowups with the same distinct projected centers
under a base isomorphism have a unique lift of that isomorphism through the towers. -/
theorem existsUnique_isLift_of_baseCenter_eq {T : BlowupTower X n Y} {U : BlowupTower X' n Y'}
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower X' U) (e : X ≅ X')
    (hinj : Function.Injective hT.baseCenter)
    (he : ∀ j, e.hom (hT.baseCenter j) = hU.baseCenter j) :
    ∃! g : Y ≅ Y', IsLift e T U g := by
  suffices ∃ g : Y ≅ Y', IsLift e T U g by
    obtain ⟨g, hg⟩ := this
    exact ⟨g, hg, fun _ hf ↦ hf.unique hg⟩
  induction hT generalizing Y' with
  | nil =>
    cases U
    exact ⟨e, IsLift.nil_iff.mpr rfl⟩
  | @snoc d W T I hT p hp hI ih =>
    cases hU with
    | @snoc _ W' U J hU q hq hJ =>
      have hprefix (j : Fin d) := he j.castSucc
      simp only [baseCenter_snoc_castSucc] at hprefix
      have hinj' : Function.Injective hT.baseCenter := by
        intro a b hab
        apply Fin.castSucc_injective d
        exact hinj (by simpa only [baseCenter_snoc_castSucc] using hab)
      obtain ⟨g, hg⟩ := ih hU hinj' hprefix
      have hlast := he (Fin.last d)
      simp only [baseCenter_snoc_last, lastCenter_eq _ p hp hI, lastCenter_eq _ q hq hJ] at hlast
      -- Over the last projected center, the preceding tower still has at most one preimage.
      have havoid : U.toBase q ∉ Set.range hU.baseCenter := by
        rintro ⟨j, hj⟩
        have heq := e.hom.injective ((hprefix j).trans (hj.trans hlast.symm))
        exact Fin.castSucc_ne_last j (hinj (by
          simpa only [baseCenter_snoc_castSucc, baseCenter_snoc_last, lastCenter_eq _ p hp hI]
            using heq))
      have hpq : U.toBase (g.hom p) = U.toBase q := by
        rw [← Scheme.Hom.comp_apply, hg.hom_toBase, Scheme.Hom.comp_apply, hlast]
      have havoid' : U.toBase (g.hom p) ∉ Set.range hU.baseCenter := hpq.symm ▸ havoid
      have hq' : g.hom p = q := hU.injOn_toBase_compl_range_baseCenter havoid' havoid hpq
      have hcomap : J.comap g.hom = I := by
        rw [hJ, ← hq', g.hom.comap_ker_fromSpecResidueField_apply, hI]
      exact ⟨_, hg.snoc hcomap⟩

end IsClosedPointTower

end QPainleve.BlowupTower
