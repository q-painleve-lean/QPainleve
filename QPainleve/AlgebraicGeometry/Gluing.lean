/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Gluing by agreement after a dominant morphism

For maps from an open cover of a reduced scheme to a separated scheme over a base,
a common dominant morphism that factors through each chart detects compatibility on overlaps.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Cover

variable {W X Y S : Scheme} [IsReduced X]
  (𝒰 : X.OpenCover) (d : W ⟶ X) [IsDominant d]
  (j : ∀ i, W ⟶ 𝒰.X i) (hj : ∀ i, j i ≫ 𝒰.f i = d)
  (f : ∀ i, 𝒰.X i ⟶ Y) (g : W ⟶ Y) (hf : ∀ i, j i ≫ f i = g)
  (s : Y ⟶ S) [IsSeparated s] (b : X ⟶ S) (hs : ∀ i, f i ≫ s = 𝒰.f i ≫ b)

/-- Glue maps to a separated scheme over a base using agreement after a dominant
morphism that factors through every member of the cover. -/
def glueMorphismsOfDominant : X ⟶ Y :=
  𝒰.glueMorphisms f fun i k ↦ by
    let l := pullback.lift (j i) (j k) ((hj i).trans (hj k).symm)
    let p := pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i
    have : IsOpenImmersion p := inferInstanceAs (IsOpenImmersion (_ ≫ _))
    have : IsReduced (pullback (𝒰.f i) (𝒰.f k)) := isReduced_of_isOpenImmersion p
    have : IsDominant (l ≫ p) := by
      simpa only [p, l, pullback.lift_fst_assoc, hj] using (inferInstance : IsDominant d)
    have : IsDominant l := IsDominant.of_comp_of_isOpenImmersion l p
    refine ext_of_isDominant_of_isSeparated s ?_ l ?_
    · simp only [Category.assoc, hs, pullback.condition_assoc]
    · simp only [l, pullback.lift_fst_assoc, pullback.lift_snd_assoc, hf]

/-- The glued morphism restricts to the prescribed morphism on each chart. -/
@[reassoc (attr := simp)]
theorem ι_glueMorphismsOfDominant (i : 𝒰.I₀) :
    𝒰.f i ≫ 𝒰.glueMorphismsOfDominant d j hj f g hf s b hs = f i :=
  𝒰.ι_glueMorphisms _ _ i

end AlgebraicGeometry.Scheme.Cover
