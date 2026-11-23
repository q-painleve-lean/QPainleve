/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.FunctionField

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic

/-!
# Restricting rational maps to dense opens

The morphism of a partial map represents the precomposition of its rational map by
the domain inclusion. This comparison lets a regular restriction be expressed
using the same composition operation as resolution by a dominant morphism. A
resolution is an isomorphism only over opens on which the original map was defined.
-/

public section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.PartialMap

universe u

/-- Restricting the rational map represented by `p` to its domain gives the rational
map of its defining morphism. -/
theorem hom_toRationalMap_eq_comp {X Z : Scheme.{u}} [IsIntegral X] (p : X.PartialMap Z) :
    letI : Nonempty p.domain := Set.nonempty_coe_sort.mpr p.dense_domain.nonempty
    letI := Opens.isDominant_ι p.dense_domain
    p.hom.toRationalMap = p.domain.ι.toRationalMap.comp p.toRationalMap := by
  let : Nonempty p.domain := Set.nonempty_coe_sort.mpr p.dense_domain.nonempty
  let := Opens.isDominant_ι p.dense_domain
  have hη : genericPoint X ∈ p.domain :=
    (genericPoint_specializes _).mem_open p.domain.isOpen p.dense_domain.nonempty.choose_spec
  have h : Spec.map p.domain.ι.functionFieldMap ≫ p.domain.fromSpecStalkOfMem _ hη =
      p.domain.toScheme.fromSpecStalk (genericPoint p.domain.toScheme) := by
    apply (cancel_mono p.domain.ι).mp
    simp [Category.assoc]
  apply RationalMap.eq_of_fromFunctionField_eq
  rw [RationalMap.fromFunctionField_comp, Hom.functionFieldMap_toRationalMap]
  simp only [Hom.toRationalMap, RationalMap.fromFunctionField_toRationalMap,
    PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem_toPartialMap]
  rw [PartialMap.fromSpecStalkOfMem, ← Category.assoc, h]

end AlgebraicGeometry.Scheme.PartialMap

namespace AlgebraicGeometry.Scheme.RationalMap

universe u

/-- Over the domain of a rational map, any morphism resolving it agrees on maps with
the same projection to the source. -/
theorem resolvingHom_eq_of_comp_eq {X Y Z W : Scheme.{u}} [Nonempty X] [IsReduced X]
    [PreirreducibleSpace Y] [IsReduced Y] [Z.IsSeparated]
    (q : X ⤏ Z) (f : Y ⟶ X) [IsDominant f] (g : Y ⟶ Z)
    (hg : g.toRationalMap = f.toRationalMap.comp q) {a b : W ⟶ Y}
    (hab : a ≫ f = b ≫ f) (ha : Set.range (a ≫ f) ⊆ q.domain) : a ≫ g = b ≫ g := by
  let p := q.toPartialMap
  let t := f.toPartialMap
  let r := t.comp p
  let U := t.domain.ι ''ᵁ t.hom ⁻¹ᵁ p.domain
  have hr : r.toRationalMap = g.toRationalMap := by
    rw [hg, ← q.toRationalMap_toPartialMap, RationalMap.toRationalMap_comp]
  have hrg : r.hom = U.ι ≫ g :=
    (PartialMap.equiv_toPartialMap_iff_of_isSeparated (terminal.from Y) (terminal.from Z)
      (by simp)).mp (PartialMap.toRationalMap_eq_iff.mp hr)
  have hd : U = f ⁻¹ᵁ q.domain := by
    have htop : U = (⊤ : Y.Opens).ι ''ᵁ (((⊤ : Y.Opens).ι ≫ f) ⁻¹ᵁ q.domain) := (rfl)
    rw [htop,
      Hom.comp_preimage, Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι, top_inf_eq]
  let d : U.toScheme ⟶ p.domain.toScheme :=
    (t.domain.ι.isoImage _).inv ≫ t.hom ∣_ p.domain
  have hdf : d ≫ p.domain.ι = U.ι ≫ f := by
    dsimp only [d, U]
    rw [Category.assoc, morphismRestrict_ι]
    exact Hom.isoImage_inv_ι_assoc t.domain.ι (t.hom ⁻¹ᵁ p.domain) f
  have hdr : d ≫ p.hom = r.hom := (Category.assoc _ _ _).symm
  have ha' : Set.range a ⊆ Set.range U.ι := by
    rw [Opens.range_ι, hd]
    rintro _ ⟨x, rfl⟩
    exact f.mem_preimage.mpr (ha ⟨x, rfl⟩)
  have hb' : Set.range b ⊆ Set.range U.ι := by
    rw [Opens.range_ι, hd]
    rintro _ ⟨x, rfl⟩
    have ha'' : Set.range (b ≫ f) ⊆ q.domain := hab ▸ ha
    exact f.mem_preimage.mpr (ha'' ⟨x, rfl⟩)
  let a' := IsOpenImmersion.lift U.ι a ha'
  let b' := IsOpenImmersion.lift U.ι b hb'
  have e : a' ≫ d = b' ≫ d := by
    apply (cancel_mono p.domain.ι).mp
    simpa only [Category.assoc, hdf, a', b', IsOpenImmersion.lift_fac_assoc] using hab
  simpa only [Category.assoc, hdr, hrg, a', b', IsOpenImmersion.lift_fac_assoc]
    using congrArg (· ≫ p.hom) e

/-- If a dominant morphism resolves `q`, then every open over which the morphism is
an isomorphism belongs to the domain of `q`. -/
theorem le_domain_of_isIso_morphismRestrict {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (q : X ⤏ Z) (f : Y ⟶ X) [IsDominant f] (g : Y ⟶ Z)
    (hg : g.toRationalMap = f.toRationalMap.comp q)
    (U : X.Opens) [IsIso (f ∣_ U)] : U ≤ q.domain := by
  by_cases hbot : U = ⊥
  · exact hbot.le.trans bot_le
  have hne := (Opens.ne_bot_iff_nonempty U).mp hbot
  have hU : Dense (U : Set X) := U.isOpen.dense hne
  have : Nonempty U := Set.nonempty_coe_sort.mpr hne
  have : IsDominant U.ι := Opens.isDominant_ι hU
  let j := inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι
  have hj : j ≫ f = U.ι := by
    simp only [j, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (_ ≫ _))
  have : IsDominant j := inferInstance
  let p : X.PartialMap Z := ⟨U, hU, j ≫ g⟩
  have hp : (j ≫ g).toRationalMap = U.ι.toRationalMap.comp p.toRationalMap :=
    p.hom_toRationalMap_eq_comp
  have hq : (j ≫ g).toRationalMap = U.ι.toRationalMap.comp q := by
    rw [← Hom.toRationalMap_compHom, ← comp_toRationalMap, hg, ← comp_assoc]
    simp only [comp_toRationalMap, Hom.toRationalMap_compHom, hj]
  have h := comp_left_injective U.ι.toRationalMap (hp.symm.trans hq)
  exact h ▸ p.le_domain_toRationalMap

end AlgebraicGeometry.Scheme.RationalMap
