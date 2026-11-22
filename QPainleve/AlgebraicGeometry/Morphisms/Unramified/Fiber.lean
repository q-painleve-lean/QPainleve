/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.AlgebraicGeometry.Morphisms.Unramified.Basic

/-!
# Isolating a section of an unramified fiber

A section of the base change of an unramified morphism is open in that base change,
by `TauCeti.AlgebraicGeometry.isOpenImmersion_lift_of_isPullback`. Over a closed
subscheme with one point, this open can be cut out by an affine neighbourhood in
the source. The resulting fiber agrees with the section as a scheme.
-/

public section

open CategoryTheory Limits
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A section over a one-point closed subscheme of the target of an unramified morphism
is the entire base change after restricting the source to a suitable affine open. -/
theorem exists_isAffineOpen_isPullback_of_unramified {X Y Z : Scheme.{u}} [Subsingleton Z]
    (f : X ⟶ Y) [Unramified f] (q : Z ⟶ Y) [IsClosedImmersion q]
    (p : Z ⟶ X) (hp : p ≫ f = q) (z : Z) :
    ∃ (U : X.Opens), IsAffineOpen U ∧ ∃ pU : Z ⟶ U.toScheme,
      pU ≫ U.ι = p ∧ IsPullback pU (𝟙 Z) (U.ι ≫ f) q := by
  let H := IsPullback.of_hasPullback f q
  let i := H.flip.lift (𝟙 Z) p (by simpa using hp.symm)
  have hi : i ≫ pullback.fst f q = p := H.flip.lift_snd _ _ _
  have hi' : i ≫ pullback.snd f q = 𝟙 Z := H.flip.lift_fst _ _ _
  have : IsOpenImmersion i :=
    TauCeti.AlgebraicGeometry.isOpenImmersion_lift_of_isPullback H.flip _
  let j := pullback.fst f q
  obtain ⟨W, hW, hjW⟩ := j.isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.mp
    i.isOpenEmbedding.isOpen_range
  have hz : p z ∈ W := by
    have hz' : i z ∈ j ⁻¹' W := hjW ▸ Set.mem_range_self z
    simpa only [Set.mem_preimage, j, ← Scheme.Hom.comp_apply, hi] using hz'
  obtain ⟨_, ⟨U : X.Opens, hU, rfl⟩, hzU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hz hW
  have hUrange : Set.range p ⊆ Set.range U.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim w z, Scheme.Opens.range_ι]
    exact hzU
  let pU := IsOpenImmersion.lift U.ι p hUrange
  have hfac : pU ≫ U.ι = p := IsOpenImmersion.lift_fac _ _ _
  refine ⟨U, hU, pU, hfac, ?_⟩
  have H' : IsPullback pU i U.ι j := by
    apply IsOpenImmersion.isPullback
    · exact hi.trans hfac.symm
    · rw [Scheme.Opens.opensRange_ι]
      apply SetLike.coe_injective
      rw [Scheme.Hom.coe_preimage, Scheme.Hom.coe_opensRange]
      apply Set.Subset.antisymm
      · intro w hw
        rw [← hjW]
        exact hUW hw
      · rintro _ ⟨w, rfl⟩
        rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, show i ≫ j = p from hi,
          Subsingleton.elim w z]
        exact hzU
  simpa only [hi'] using H'.paste_vert H

end AlgebraicGeometry.Scheme.Hom
