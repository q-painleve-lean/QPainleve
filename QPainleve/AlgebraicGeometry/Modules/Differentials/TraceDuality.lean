/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Cohomology.TracePairing
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical

import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-!
# Top-degree trace duality under isomorphisms

An isomorphism over the base field identifies the cohomology of a line bundle and of
its canonical complement with those of their pullbacks. Perfection of the canonical
trace pairing is therefore preserved for any choice of nonzero traces.
-/

public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules
open QPainleve

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

open LineBundleClass

variable {X Y : Scheme.{u}} (k : Type u) [Field k] [Infinite k]
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [IsIntegral X] [X.IsProjectiveOver k] {n : ℕ}
  [SmoothOfRelativeDimension n (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (.of k))]

local notation "K[" W "]" => canonicalBundle k W n

/-- Under an isomorphism between smooth schemes over the base field, perfection of
the canonical trace pairing is preserved on a line bundle and its pullback. The
traces on both sides can be chosen independently, provided they are nonzero. -/
theorem isPerfPair_cohomologyTracePairing_iff_of_pullback_isIso
    (L : InvertibleSheaf X) (f : Y ⟶ X) [IsIso f] [f.IsOver (Spec (.of k))]
    (M : InvertibleSheaf Y) (hM : mk M = LineBundleClass.pullback f (mk L))
    (tr : Cohomology K[X].obj n →ₗ[k] k) (htr : tr ≠ 0)
    (trY : Cohomology K[Y].obj n →ₗ[k] k) (htrY : trY ≠ 0) :
    (cohomologyTracePairing (M := M.obj) k n trY).IsPerfPair ↔
      (cohomologyTracePairing (M := L.obj) k n tr).IsPerfPair := by
  let : Nonempty Y := Nonempty.map (fun x : X ↦ (inv f) x) inferInstance
  let : IsIntegral Y := isIntegral_of_isOpenImmersion f
  let : Y.IsProjectiveOver k := Scheme.IsProjectiveOver.of_isClosedImmersion k f
  have compare (A : InvertibleSheaf X) (B : InvertibleSheaf Y)
      (hB : mk B = LineBundleClass.pullback f (mk A)) (q : ℕ) :
      Nonempty (Cohomology A.obj q ≃ₗ[k] Cohomology B.obj q) := by
    rw [pullback_mk] at hB
    obtain ⟨e⟩ := mk_eq_mk_iff.mp hB.symm
    have eA : Cohomology A.obj q ≃ₗ[k] Cohomology ((InvertibleSheaf.pullback f).obj A).obj q := by
      rw [InvertibleSheaf.pullback_obj_obj]
      exact (f.cohomologyPullbackBaseLinearEquivOfIsIso k A.obj q).symm
    exact ⟨eA.trans (cohomologyBaseLinearEquivOfIso k e q)⟩
  obtain ⟨eₙ⟩ := compare L M hM n
  have hK : mk (K[Y].tensorProduct M.dual) =
      LineBundleClass.pullback f (mk (K[X].tensorProduct L.dual)) := by
    simp only [mk_tensorProduct, ← inv_mk, hM, pullback_mul, pullback_inv, pullback_mk,
      mk_pullback_canonicalBundle]
  obtain ⟨e₀⟩ := compare (K[X].tensorProduct L.dual) (K[Y].tensorProduct M.dual) hK 0
  let e := (L.sectionsInternalHomLinearEquiv k K[X]).trans
    (e₀.trans (M.sectionsInternalHomLinearEquiv k K[Y]).symm)
  rw [M.isPerfPair_cohomologyTracePairing_iff_finrank k K[Y]
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y ↘ Spec (.of k)) (n := n)).le trY htrY,
    L.isPerfPair_cohomologyTracePairing_iff_finrank k K[X]
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := n)).le tr htr,
    ← eₙ.finrank_eq, ← e.finrank_eq]

end TauCeti.AlgebraicGeometry.InvertibleSheaf
