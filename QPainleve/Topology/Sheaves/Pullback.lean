/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Pullback squares of sheaves on a basis

A square of sheaves is a pullback when its sections form pullback squares over
the opens of a topological basis.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace TopCat.Sheaf

/-- To recognize a pullback of sheaves, it suffices to check the square on a basis. -/
theorem isPullback_of_isPullback_basis {C : Type*} [Category* C] [HasPullbacks C]
    {X : TopCat} {P F G H : Sheaf C X} {a : P ⟶ F} {b : P ⟶ G} {c : F ⟶ H} {d : G ⟶ H}
    (h : CommSq a b c d) {ι : Type*} {B : ι → Opens X} (hB : Opens.IsBasis (Set.range B))
    (hb : ∀ i, IsPullback (a.hom.app (op (B i))) (b.hom.app (op (B i)))
      (c.hom.app (op (B i))) (d.hom.app (op (B i)))) :
    IsPullback a b c d := by
  let l := pullback.lift a b h.w
  have hl : IsIso l := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis hB
    intro i
    let E := sheafToPresheaf (Opens.grothendieckTopology X) C ⋙
      (evaluation _ C).obj (op (B i))
    have hi : IsPullback (E.map a) (E.map b) (E.map c) (E.map d) := hb i
    have hE : E.map l ≫ pullbackComparison E c d = hi.isoPullback.hom := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullbackComparison_comp_fst, ← E.map_comp, pullback.lift_fst,
          hi.isoPullback_hom_fst]
      · rw [Category.assoc, pullbackComparison_comp_snd, ← E.map_comp, pullback.lift_snd,
          hi.isoPullback_hom_snd]
    have hcomp : IsIso (E.map l ≫ pullbackComparison E c d) := by
      rw [hE]
      infer_instance
    exact IsIso.of_isIso_comp_right (E.map l) (pullbackComparison E c d)
  exact IsPullback.of_iso_pullback h (asIso l) (pullback.lift_fst ..) (pullback.lift_snd ..)

end TopCat.Sheaf
