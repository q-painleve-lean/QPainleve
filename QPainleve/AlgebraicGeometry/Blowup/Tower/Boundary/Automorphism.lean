/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Automorphism
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint

import QPainleve.AlgebraicGeometry.Blowup.Point.Boundary
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Component

/-!
# Boundary components under ordered blowup lifts

For an automorphism lifting through a specified tower of closed point blowups, fixing the
boundary components is equivalent on the base and on the blown-up surface. Each new
exceptional prime is fixed by the ordered lift, and every other prime can be compared over
the isomorphism locus. Combined with Picard descent, this gives a unique descended
automorphism fixing the original boundary components, including for a tower of nodal blowups.
The tower induction uses `fixes_codimensionOne_preimage_blowup_iff` for each blowup.
The Picard descent is supplied by `IsClosedPointTower.existsUnique_isLift_over_of_picard_trivial`.

This is the comparison of boundary components in the toric blowup reduction of
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*, Proposition 2.6](
https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower

variable {k : Type u} [Field k] [PerfectField k]
  {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}
  (s : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 s]

include s in
/-- An ordered lift through a closed point blowup tower fixes all codimension-one points
supported on the reduced total transform exactly when the base isomorphism fixes all
codimension-one points supported on the original boundary. -/
theorem IsLift.fixes_boundary_components_iff (hT : IsClosedPointTower X T)
    {e : X ≅ X} {g : Y ≅ Y} (hg : IsLift e T T g) (D : X.IdealSheafData) :
    (∀ y : CodimensionOnePoint Y, (y : Y) ∈ (D.comap T.toBase).support → g.hom y = y) ↔
      ∀ x : CodimensionOnePoint X, (x : X) ∈ D.support → e.hom x = x := by
  induction hT with
  | nil =>
    rw [IsLift.nil_iff.mp hg, toBase_nil, comap_id]
  | @snoc m W U I hU p hp hI ih =>
    obtain ⟨f, hf, hcenter, rfl⟩ := IsLift.snoc_iff.mp hg
    have := hU.smoothOfRelativeDimension s
    rw [← ih hf, toBase_snoc, comap_comp]
    simpa only [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage] using
      fixes_codimensionOne_preimage_blowup_iff (U.toBase ≫ s) hp hI f hcenter
        ((D.comap U.toBase).support : Set W)

namespace IsClosedPointTower

variable [IsIntegral X] [IsNoetherian X] {D : X.IdealSheafData}

/-- An automorphism fixing the Picard group and all components of the reduced total
boundary descends through the specified closed point blowups to a unique automorphism
over the field. The descended automorphism fixes the Picard group, the reduced boundary
ideal and each boundary component on the original surface. -/
theorem existsUnique_isLift_over_fixing_boundary_of_picard_trivial
    (hT : IsClosedPointTower X T) (hD : D.IsEffectiveCartier)
    (g : Y ≅ Y) (hgPic : ∀ a, LineBundleClass.pullback g.hom a = a)
    (hgOver : g.hom ≫ T.toBase ≫ s = T.toBase ≫ s)
    (hgD : ∀ y : CodimensionOnePoint Y, (y : Y) ∈ (D.comap T.toBase).support → g.hom y = y) :
    ∃! e : X ≅ X, IsLift e T T g ∧ (∀ a, LineBundleClass.pullback e.hom a = a) ∧
      e.hom ≫ s = s ∧ D.radical.comap e.hom = D.radical ∧
      ∀ x : CodimensionOnePoint X, (x : X) ∈ D.support → e.hom x = x := by
  obtain ⟨e, ⟨he, hePic, heOver⟩, huniq⟩ :=
    hT.existsUnique_isLift_over_of_picard_trivial s g hgPic hgOver
  have hfix := (he.fixes_boundary_components_iff s hT D).mp hgD
  exact ⟨e, ⟨he, hePic, heOver, hD.comap_radical_eq_of_fixes_components e hfix, hfix⟩,
    fun a ha ↦ huniq a ⟨ha.1, ha.2.1, ha.2.2.1⟩⟩

end IsClosedPointTower
end QPainleve.BlowupTower
