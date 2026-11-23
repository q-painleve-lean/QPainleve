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

/-- A morphism factoring through a representative also factors through the maximal domain,
with the same value under the rational map. -/
theorem exists_lift_toPartialMap {X Y T : Scheme.{u}} [IsReduced X] [Y.IsSeparated]
    (p : X.PartialMap Y) (a : T ⟶ p.domain) :
    ∃ b : T ⟶ p.toRationalMap.toPartialMap.domain,
      b ≫ p.toRationalMap.toPartialMap.domain.ι = a ≫ p.domain.ι ∧
      b ≫ p.toRationalMap.toPartialMap.hom = a ≫ p.hom := by
  refine ⟨a ≫ X.homOfLE p.le_domain_toRationalMap, ?_, ?_⟩
  · erw [Category.assoc, homOfLE_ι]
  · have h := p.toPartialMap_toRationalMap_restrict
    erw [PartialMap.restrict_hom] at h
    rw [Category.assoc, h]

end AlgebraicGeometry.Scheme.PartialMap

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- A regular morphism is defined on any morphism into its source, where the value
of the associated rational map is ordinary composition. -/
theorem exists_lift_toRationalMap {X Y T : Scheme.{u}} [IsReduced X] [Y.IsSeparated]
    (f : X ⟶ Y) (a : T ⟶ X) :
    ∃ b : T ⟶ f.toRationalMap.toPartialMap.domain,
      b ≫ f.toRationalMap.toPartialMap.domain.ι = a ∧
      b ≫ f.toRationalMap.toPartialMap.hom = a ≫ f := by
  obtain ⟨b, hb, hb'⟩ := f.toPartialMap.exists_lift_toPartialMap (a ≫ X.topIso.inv)
  have hι : (a ≫ X.topIso.inv) ≫ X.topIso.hom = a := by simp
  refine ⟨b, hb.trans hι, hb'.trans ?_⟩
  have he : (a ≫ X.topIso.inv) ≫ X.topIso.hom ≫ f = a ≫ f := by
    rw [Category.assoc, Iso.inv_hom_id_assoc]
  erw [Hom.toPartialMap_hom]
  exact he

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.RationalMap

universe u

/-- A morphism into the domain of each successive rational map lifts to the domain
of their composition. Its value there is the value of the second map. -/
theorem exists_lift_comp {X Y Z T : Scheme.{u}} [PreirreducibleSpace X] [Nonempty Y]
    [IsReduced X] [IsReduced Y] [Y.IsSeparated] [Z.IsSeparated]
    (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z)
    (a : T ⟶ f.toPartialMap.domain) (b : T ⟶ g.toPartialMap.domain)
    (hab : a ≫ f.toPartialMap.hom = b ≫ g.toPartialMap.domain.ι) :
    ∃ c : T ⟶ (f.comp g).toPartialMap.domain,
      c ≫ (f.comp g).toPartialMap.domain.ι = a ≫ f.toPartialMap.domain.ι ∧
      c ≫ (f.comp g).toPartialMap.hom = b ≫ g.toPartialMap.hom := by
  let p := f.toPartialMap
  let q := g.toPartialMap
  have : IsDominant p.hom :=
    p.isDominant_toRationalMap_iff.mp (f.toRationalMap_toPartialMap ▸ ‹f.IsDominant›)
  let H := isPullback_morphismRestrict p.hom q.domain
  let a' := H.lift b a hab.symm
  let c := a' ≫ (p.domain.ι.isoImage (p.hom ⁻¹ᵁ q.domain)).hom
  have hc₁ : c ≫ (p.comp q).domain.ι = a ≫ f.toPartialMap.domain.ι := by
    -- The composite domain is the image of the inverse image under the first open inclusion.
    change c ≫ (p.domain.ι ''ᵁ p.hom ⁻¹ᵁ q.domain).ι = a ≫ p.domain.ι
    dsimp only [c]
    rw [Category.assoc, Hom.isoImage_hom_ι, ← Category.assoc, H.lift_snd]
  have hc₂ : c ≫ (p.comp q).hom = b ≫ g.toPartialMap.hom := by
    dsimp only [c]
    rw [PartialMap.comp_hom, Category.assoc, Iso.hom_inv_id_assoc,
      ← Category.assoc, H.lift_fst]
  have hq : (p.comp q).toRationalMap = f.comp g := by
    simp only [← toRationalMap_comp, p, q, toRationalMap_toPartialMap]
  obtain ⟨d, hd, hd'⟩ := (p.comp q).exists_lift_toPartialMap c
  exact hq ▸ ⟨d, hd.trans hc₁, hd'.trans hc₂⟩

/-- If an open immersion carries a regular representative of a rational map at the generic
point, it factors through the domain of that map and recovers the representative there. -/
theorem exists_lift_of_fromFunctionField_eq {X U Z : Scheme.{u}} [IsIntegral X]
    [Z.IsSeparated] (f : X ⤏ Z) (i : U ⟶ X) [IsOpenImmersion i] (g : U ⟶ Z)
    (η : Spec X.functionField ⟶ U)
    (hη : η ≫ i = X.fromSpecStalk (genericPoint X)) (hg : η ≫ g = f.fromFunctionField) :
    ∃ a : U ⟶ f.toPartialMap.domain,
      a ≫ f.toPartialMap.domain.ι = i ∧ a ≫ f.toPartialMap.hom = g := by
  let e := i.isoOpensRange
  have hmem : genericPoint X ∈ i.opensRange := by
    rw [← SetLike.mem_coe, Hom.coe_opensRange]
    let x : (Spec X.functionField : Scheme) := IsLocalRing.closedPoint X.functionField
    refine ⟨η x, ?_⟩
    rw [← Hom.comp_apply, hη]
    exact fromSpecStalk_closedPoint
  let p : X.PartialMap Z :=
    ⟨i.opensRange, i.opensRange.isOpen.dense ⟨_, hmem⟩, e.inv ≫ g⟩
  have he : p.domain.fromSpecStalkOfMem _ hmem = η ≫ e.hom := by
    apply (cancel_mono p.domain.ι).mp
    have hei : e.hom ≫ p.domain.ι = i := i.isoOpensRange_hom_ι
    rw [Category.assoc, hei, Opens.fromSpecStalkOfMem_ι, hη]
  have hp : p.toRationalMap = f := by
    apply eq_of_fromFunctionField_eq
    rw [fromFunctionField_toRationalMap, PartialMap.fromFunctionField,
      PartialMap.fromSpecStalkOfMem, he]
    simpa only [p, Category.assoc, Iso.hom_inv_id_assoc] using hg
  obtain ⟨a, ha, ha'⟩ := p.exists_lift_toPartialMap e.hom
  exact hp ▸ ⟨a, ha.trans i.isoOpensRange_hom_ι,
    ha'.trans (by simp only [p, Iso.hom_inv_id_assoc])⟩

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
