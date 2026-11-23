/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

/-!
# Pullback squares over an isomorphism locus

In a commuting square, if the bottom morphism has image in the isomorphism locus of the
right morphism and the left morphism is an isomorphism, the square is cartesian. A
morphism with image in the isomorphism locus has a lift with this property.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A commuting square over the isomorphism locus of its right map is cartesian if
its left map is an isomorphism. -/
theorem isPullback_of_isIso_of_range_subset_isoLocus {X Y A B : Scheme}
    (f : X ⟶ Y) (i : A ⟶ X) (e : A ⟶ B) (j : B ⟶ Y) [IsIso e]
    (h : i ≫ f = e ≫ j) (hj : Set.range j ⊆ f.isoLocus) :
    IsPullback i e f j := by
  let U := f.isoLocus
  have hjU : Set.range j ⊆ Set.range U.ι := by
    rwa [Scheme.Opens.range_ι]
  have hiU : Set.range i ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨a, rfl⟩
    apply f.mem_preimage.mpr
    have ha : f (i a) = j (e a) := calc
      f (i a) = (i ≫ f) a := (Scheme.Hom.comp_apply i f a).symm
      _ = (e ≫ j) a := congrArg (fun k : A ⟶ Y ↦ k a) h
      _ = j (e a) := Scheme.Hom.comp_apply e j a
    exact ha.symm ▸ hj (Set.mem_range_self (e a))
  let i' := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι i hiU
  let j' := IsOpenImmersion.lift U.ι j hjU
  have hi' : i' ≫ (f ⁻¹ᵁ U).ι = i := IsOpenImmersion.lift_fac _ _ _
  have hj' : j' ≫ U.ι = j := IsOpenImmersion.lift_fac _ _ _
  have hcomm : i' ≫ f ∣_ U = e ≫ j' := by
    apply (cancel_mono U.ι).mp
    simpa only [Category.assoc, morphismRestrict_ι, ← Category.assoc i', hi',
      Category.assoc e, hj'] using h
  have : IsIso (f ∣_ U) := inferInstanceAs (IsIso (f ∣_ f.isoLocus))
  have hpb : IsPullback i' e (f ∣_ U) j' := .of_vert_isIso ⟨hcomm⟩
  simpa only [hi', hj'] using hpb.paste_horiz (isPullback_morphismRestrict f U).flip

/-- A base change is an isomorphism over the inverse image of the original isomorphism locus. -/
theorem preimage_isoLocus_le_of_isPullback {X Y A B : Scheme.{u}}
    {f : X ⟶ Y} {g : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y}
    (h : IsPullback g a b f) :
    b ⁻¹ᵁ f.isoLocus ≤ g.isoLocus := by
  let U := f.isoLocus
  have he : g ⁻¹ᵁ (b ⁻¹ᵁ U) = g ⁻¹ᵁ (b ⁻¹ᵁ U) ⊓ a ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h.w, inf_idem]
  have hr := Scheme.Hom.isPullback_resLE h (US := U) (UT := f ⁻¹ᵁ U)
    (UX := b ⁻¹ᵁ U) le_rfl le_rfl he
  have hIso : IsIso (f ∣_ U) := inferInstanceAs (IsIso (f ∣_ f.isoLocus))
  apply g.le_isoLocus_iff.mpr
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
    hr.isIso_fst_of_isIso (by simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using hIso)

/-- A morphism with image in the isomorphism locus lifts to a cartesian square
whose projection to its source is the identity. -/
theorem exists_isPullback_id_of_range_subset_isoLocus {X Y B : Scheme.{u}}
    (f : X ⟶ Y) (j : B ⟶ Y) (hj : Set.range j ⊆ f.isoLocus) :
    ∃ i : B ⟶ X, IsPullback i (𝟙 B) f j := by
  have hp := IsPullback.of_hasPullback f j
  have htop : j ⁻¹ᵁ f.isoLocus = ⊤ :=
    top_unique fun x _ ↦ j.mem_preimage.mpr (hj (Set.mem_range_self x))
  have : IsIso (pullback.snd f j) :=
    (Scheme.Hom.isoLocus_eq_top_iff _).mp <|
      top_unique (htop ▸ Scheme.Hom.preimage_isoLocus_le_of_isPullback hp.flip)
  exact ⟨inv (pullback.snd f j) ≫ pullback.fst f j,
    hp.of_iso' (asIso (pullback.snd f j)).symm (.refl _) (.refl _) (.refl _)
      (by simp) (by simp) (by simp) (by simp)⟩

end AlgebraicGeometry.Scheme.Hom
