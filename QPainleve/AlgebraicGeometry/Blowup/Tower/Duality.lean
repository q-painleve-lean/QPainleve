/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.CanonicalCohomology
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
public import QPainleve.AlgebraicGeometry.Cohomology.TracePairing

import QPainleve.AlgebraicGeometry.Blowup.Tower.GlobalSections
import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Blowup.Tower.SecondCohomology
import QPainleve.AlgebraicGeometry.Modules.Differentials.TraceDuality
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-!
# Top-degree trace duality along point-blowup towers

If the total-transform exceptional coefficients of a line bundle are at most one, its
second cohomology agrees with that of its base coordinate. The canonical complement has
nonnegative exceptional coefficients, so its sections agree as well. Thus perfection of
the trace pairing is equivalent on the two surfaces for nonzero traces. In particular,
the comparison descends perfection for a pulled-back bundle along a common resolution.

The coefficient calculation uses `canonical_complement_picardHom`, and the comparison
of pairings uses `InvertibleSheaf.isPerfPair_cohomologyTracePairing_iff_finrank`.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules LineBundleClass

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}
  (k : Type u) [Field k] [PerfectField k] [Infinite k] [IsIntegral X] [X.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "K[" W "]" => canonicalBundle k W 2

/-- Top-degree trace duality for a line bundle in the Picard marking is equivalent to
duality for its base coordinate when every total-transform exceptional coefficient is
at most one. The two traces can be chosen independently, provided both are nonzero. -/
theorem isPerfPair_cohomologyTracePairing_picardHom_iff
    (hT : IsClosedPointTower X T) (L : InvertibleSheaf X) (b : Fin n → ℤ)
    (hb : ∀ j, b j ≤ 1) (M : InvertibleSheaf Y)
    (hM : mk M = (T.picardHom (Additive.ofMul (mk L), b)).toMul)
    (tr : Cohomology K[X].obj 2 →ₗ[k] k) (htr : tr ≠ 0) :
    let : Y.Over S := ⟨T.toBase ≫ X ↘ S⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension (X ↘ S)
    ∀ (trY : Cohomology K[Y].obj 2 →ₗ[k] k) (_ : trY ≠ 0),
      (cohomologyTracePairing (M := M.obj) k 2 trY).IsPerfPair ↔
        (cohomologyTracePairing (M := L.obj) k 2 tr).IsPerfPair := by
  intro _ _ trY htrY
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let : IsIntegral Y := hT.isIntegral (X ↘ S)
  let : Y.IsProjectiveOver k := T.isProjectiveOver k
  obtain ⟨e₂⟩ := hT.nonempty_cohomologyTwoLinearEquiv_picardHom k L b hb M hM
  obtain ⟨e₀⟩ := hT.nonempty_cohomologyZeroLinearEquiv_picardHom k (K[X].tensorProduct L.dual)
    (fun j ↦ 1 - b j) (fun j ↦ sub_nonneg.mpr (hb j)) (K[Y].tensorProduct M.dual)
    (canonical_complement_picardHom k hT L b M hM)
  let e := (L.sectionsInternalHomLinearEquiv k K[X]).trans
    (e₀.trans (M.sectionsInternalHomLinearEquiv k K[Y]).symm)
  rw [M.isPerfPair_cohomologyTracePairing_iff_finrank k K[Y]
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y ↘ S) (n := 2)).le trY htrY,
    L.isPerfPair_cohomologyTracePairing_iff_finrank k K[X]
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)).le tr htr,
    ← e₂.finrank_eq, ← e.finrank_eq]

omit [Infinite k] [IsIntegral X] [X.IsProjectiveOver k] in
private theorem cohomologyCanonicalBundleLinearEquiv_comp_symm_ne_zero
    (hT : IsClosedPointTower X T) [Y.Over S] [T.toBase.IsOver S]
    (tr : Cohomology K[X].obj 2 →ₗ[k] k) (htr : tr ≠ 0) :
    tr.comp (hT.cohomologyCanonicalBundleLinearEquiv k 2).symm.toLinearMap ≠ 0 := by
  let e := (hT.cohomologyCanonicalBundleLinearEquiv k 2).symm
  intro h
  exact htr ((LinearMap.cancel_right e.surjective).mp (h.trans (LinearMap.zero_comp _).symm))

/-- The canonical cohomology comparison along a tower transports a nonzero trace.
With this transported trace the pullback of a line bundle pairs perfectly exactly
when the original line bundle does. -/
theorem isPerfPair_cohomologyTracePairing_of_blowup_tower
    (hT : IsClosedPointTower X T) (L : InvertibleSheaf X)
    (tr : Cohomology K[X].obj 2 →ₗ[k] k) (htr : tr ≠ 0) :
    let : Y.Over S := ⟨T.toBase ≫ X ↘ S⟩
    let : T.toBase.IsOver S := ⟨rfl⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension (X ↘ S)
    let trY := tr.comp (hT.cohomologyCanonicalBundleLinearEquiv k 2).symm.toLinearMap
    let M := (InvertibleSheaf.pullback T.toBase).obj L
    (cohomologyTracePairing (M := M.obj) k 2 trY).IsPerfPair ↔
      (cohomologyTracePairing (M := L.obj) k 2 tr).IsPerfPair := by
  intro _ _ _ trY M
  have hM : mk M = (T.picardHom (Additive.ofMul (mk L), 0)).toMul := by
    rw [picardHom_apply_zero, toMul_ofMul, pullback_mk]
  exact hT.isPerfPair_cohomologyTracePairing_picardHom_iff k L 0
    (fun _ ↦ zero_le_one) M hM tr htr trY
    (cohomologyCanonicalBundleLinearEquiv_comp_symm_ne_zero k hT tr htr)

/-- To test perfection on a surface, one may pull the line bundle to a specified
point-blowup resolution and identify its endpoint with another smooth model. The
resolved line bundle is specified by its Picard class, and its trace can be any
nonzero trace on the canonical cohomology of that model. -/
theorem isPerfPair_cohomologyTracePairing_iff_of_pullback_tower_iso
    (hT : IsClosedPointTower X T) {W : Scheme.{u}} [W.Over S]
    [SmoothOfRelativeDimension 2 (W ↘ S)] (e : W ≅ Y)
    (he : e.hom ≫ T.toBase ≫ X ↘ S = W ↘ S)
    (L : InvertibleSheaf X) (M : InvertibleSheaf W)
    (hM : mk M = LineBundleClass.pullback (e.hom ≫ T.toBase) (mk L))
    (tr : Cohomology K[X].obj 2 →ₗ[k] k) (htr : tr ≠ 0)
    (trW : Cohomology K[W].obj 2 →ₗ[k] k) (htrW : trW ≠ 0) :
    (cohomologyTracePairing (M := M.obj) k 2 trW).IsPerfPair ↔
      (cohomologyTracePairing (M := L.obj) k 2 tr).IsPerfPair := by
  let : Y.Over S := ⟨T.toBase ≫ X ↘ S⟩
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : e.hom.IsOver S := ⟨he⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension (X ↘ S)
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let : IsIntegral Y := hT.isIntegral (X ↘ S)
  let : Y.IsProjectiveOver k := T.isProjectiveOver k
  let A := (InvertibleSheaf.pullback T.toBase).obj L
  let trY := tr.comp (hT.cohomologyCanonicalBundleLinearEquiv k 2).symm.toLinearMap
  have hclass : mk M = LineBundleClass.pullback e.hom (mk A) := by
    simpa only [A, ← pullback_mk, LineBundleClass.pullback_comp] using hM
  have htrY := cohomologyCanonicalBundleLinearEquiv_comp_symm_ne_zero k hT tr htr
  exact (A.isPerfPair_cohomologyTracePairing_iff_of_pullback_isIso k e.hom M hclass
    trY htrY trW htrW).trans (hT.isPerfPair_cohomologyTracePairing_of_blowup_tower k L tr htr)

end QPainleve.BlowupTower.IsClosedPointTower
