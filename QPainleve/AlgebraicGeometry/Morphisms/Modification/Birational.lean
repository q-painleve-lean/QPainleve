/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic

import TauCeti.AlgebraicGeometry.Morphisms.Modification.Centre
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# Recognizing modifications of schemes

A proper morphism that sends a dense open subscheme isomorphically onto a dense open
is a modification. This recognizes a regular representative of a specified birational map
after a modification of its source. It also gives cancellation in factorizations where one
factor is already a modification.

These comparisons apply to the intermediate lifts in
[Stacks Project, Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R) and the resolved morphism
in [Lemma 54.17.2](https://stacks.math.columbia.edu/tag/0C5S).
-/

public section

open AlgebraicGeometry CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry.IsModification

variable {X Y Z U : Scheme.{u}}

/-- A proper morphism is a modification if it identifies a dense open of the source
with a dense open of the target. -/
theorem of_isOpenImmersion_comp (f : X ⟶ Y) (i : U ⟶ X)
    [IsProper f] [IsOpenImmersion i] [IsDominant i]
    [IsOpenImmersion (i ≫ f)] [IsDominant (i ≫ f)] : IsModification f := by
  let V := (i ≫ f).opensRange
  let e := (i ≫ f).isoOpensRange
  have hiV : Set.range i ⊆ Set.range (f ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact f.mem_preimage.mpr ⟨x, rfl⟩
  let j := IsOpenImmersion.lift (f ⁻¹ᵁ V).ι i hiV
  have hj : j ≫ (f ⁻¹ᵁ V).ι = i := IsOpenImmersion.lift_fac _ _ _
  have he : j ≫ f ∣_ V = e.hom := by
    apply (cancel_mono V.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hj]
    exact (i ≫ f).isoOpensRange_hom_ι.symm
  have : IsIso (j ≫ f ∣_ V) := he.symm ▸ inferInstanceAs (IsIso e.hom)
  -- The dense open lifts as a section after identifying it with the target open.
  have : IsProper j := IsProper.of_comp j (f ∣_ V)
  have : IsOpenImmersion (j ≫ (f ⁻¹ᵁ V).ι) := hj.symm ▸ inferInstanceAs (IsOpenImmersion i)
  have : IsDominant (j ≫ (f ⁻¹ᵁ V).ι) := hj.symm ▸ inferInstanceAs (IsDominant i)
  have : IsOpenImmersion j := IsOpenImmersion.of_comp j (f ⁻¹ᵁ V).ι
  have : IsDominant j := IsDominant.of_comp_of_isOpenImmersion j (f ⁻¹ᵁ V).ι
  have : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨inferInstance, inferInstance⟩
  refine ⟨⟨V, ?_, ?_, IsIso.of_isIso_comp_left j _⟩⟩
  · exact (i ≫ f).denseRange
  · have hsurj : Set.range j = Set.univ := j.surjective.range_eq
    simpa only [DenseRange, Scheme.Opens.range_ι, ← hj, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, hsurj, Set.image_univ] using i.denseRange

/-- A proper morphism representing a dominant open immersion on a dense open is a modification. -/
theorem of_toRationalMap_eq (f : X ⟶ Y) [IsProper f] (a : X.PartialMap Y)
    [IsOpenImmersion a.hom] [IsDominant a.hom] (h : f.toRationalMap = a.toRationalMap) :
    IsModification f := by
  obtain ⟨W, hW, hWf, hWa, he⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp h
  have he' : W.ι ≫ f = X.homOfLE hWa ≫ a.hom := by
    have hleft : (f.toPartialMap.restrict W hW hWf).hom = W.ι ≫ f := calc
      _ = X.homOfLE hWf ≫ X.topIso.hom ≫ f := rfl
      _ = X.homOfLE hWf ≫ (⊤ : X.Opens).ι ≫ f := by rw [Scheme.topIso_hom]
      _ = _ := X.homOfLE_ι_assoc hWf f
    exact hleft.symm.trans he
  have : IsDominant W.ι := Opens.isDominant_ι hW
  have : IsDominant (X.homOfLE hWa) := Opens.isDominant_homOfLE hW hWa
  have : IsOpenImmersion (X.homOfLE hWa ≫ a.hom) := inferInstance
  have : IsDominant (X.homOfLE hWa ≫ a.hom) := inferInstance
  have : IsOpenImmersion (W.ι ≫ f) := he'.symm ▸ ‹IsOpenImmersion (X.homOfLE hWa ≫ a.hom)›
  have : IsDominant (W.ι ≫ f) := he'.symm ▸ ‹IsDominant (X.homOfLE hWa ≫ a.hom)›
  exact of_isOpenImmersion_comp f W.ι

/-- A factor before a modification is a modification if the composite is a modification. -/
theorem of_comp_right (f : X ⟶ Y) (g : Y ⟶ Z) [IsModification g]
    [IsModification (f ≫ g)] : IsModification f := by
  have : IsProper f := IsProper.of_comp f g
  let W := (f ≫ g).isoLocus ⊓ g.isoLocus
  have hW : Dense (W : Set Z) :=
    (dense_isoLocus (f ≫ g)).inter_of_isOpen_right (dense_isoLocus g) g.isoLocus.is_open'
  have hg : IsIso (g ∣_ W) := g.le_isoLocus_iff.mp inf_le_right
  have hfg : IsIso ((f ≫ g) ∣_ W) := (f ≫ g).le_isoLocus_iff.mp inf_le_left
  rw [morphismRestrict_comp] at hfg
  have hf : IsIso (f ∣_ (g ⁻¹ᵁ W)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ (g ∣_ W) hg hfg
  refine ⟨⟨g ⁻¹ᵁ W, (inferInstance : IsModification g).dense_preimage hW, ?_, hf⟩⟩
  simpa only [Scheme.Hom.comp_preimage] using
    (inferInstance : IsModification (f ≫ g)).dense_preimage hW

/-- A separated, locally finite type factor after a modification is a modification if the
composite is a modification. -/
theorem of_comp_left (f : X ⟶ Y) (g : Y ⟶ Z) [IsModification f]
    [IsSeparated g] [LocallyOfFiniteType g] [IsModification (f ≫ g)] : IsModification g := by
  have : UniversallyClosed g := UniversallyClosed.of_comp_surjective f g
  have : IsProper g := ⟨⟩
  have hU := (inferInstance : IsModification f).dense_preimage (dense_isoLocus f)
  obtain ⟨V, hV, hle, hIso⟩ :=
    (inferInstance : IsModification (f ≫ g)).exists_isIso_morphismRestrict_preimage_le hU
  let W := (f ≫ g) ⁻¹ᵁ V
  let i := W.ι ≫ f
  have hi : i = X.homOfLE hle ≫ (f ∣_ f.isoLocus) ≫ f.isoLocus.ι := by
    dsimp only [i]
    rw [morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
  have : IsIso (f ∣_ f.isoLocus) := f.le_isoLocus_iff.mp le_rfl
  have : IsOpenImmersion i := by
    rw [hi]
    infer_instance
  have : IsDominant W.ι :=
    Opens.isDominant_ι ((inferInstance : IsModification (f ≫ g)).dense_preimage hV)
  have : IsDominant i := inferInstanceAs (IsDominant (W.ι ≫ f))
  have hcomp : i ≫ g = ((f ≫ g) ∣_ V) ≫ V.ι := by
    rw [morphismRestrict_ι, Category.assoc]
  have : IsOpenImmersion (i ≫ g) := by
    rw [hcomp]
    infer_instance
  have : IsDominant V.ι := Opens.isDominant_ι hV
  have : IsDominant (i ≫ g) := by
    rw [hcomp]
    infer_instance
  exact of_isOpenImmersion_comp g i

/-- Resolving a specified partial isomorphism by a modification of its source gives a
modification of the target whenever the resolved morphism is proper. -/
theorem of_resolved_partialIso [PreirreducibleSpace X] [Nonempty Y]
    (p : X ⟶ Y) [IsModification p] (a : Y.PartialIso Z)
    (f : X ⟶ Z) [IsProper f] (h : p.toRationalMap.comp a.toRationalMap = f.toRationalMap) :
    IsModification f := by
  let U := p.isoLocus
  have hU := (inferInstance : IsModification p).dense_preimage (dense_isoLocus p)
  let b := p.toPartialMap.restrict (p ⁻¹ᵁ U) hU le_top
  have hB : b.hom = (p ∣_ U) ≫ U.ι := calc
    _ = X.homOfLE (U := p ⁻¹ᵁ U) (V := ⊤) le_top ≫ X.topIso.hom ≫ p := rfl
    _ = X.homOfLE (U := p ⁻¹ᵁ U) (V := ⊤) le_top ≫ (⊤ : X.Opens).ι ≫ p := by
      rw [Scheme.topIso_hom]
    _ = (p ⁻¹ᵁ U).ι ≫ p := X.homOfLE_ι_assoc le_top p
    _ = _ := (morphismRestrict_ι p U).symm
  have hIso : IsIso (p ∣_ U) := p.le_isoLocus_iff.mp le_rfl
  have : IsDominant U.ι := Opens.isDominant_ι (dense_isoLocus p)
  have : IsOpenImmersion b.hom :=
    hB.symm ▸ inferInstanceAs (IsOpenImmersion ((p ∣_ U) ≫ U.ι))
  have : IsDominant b.hom := hB.symm ▸ inferInstanceAs (IsDominant ((p ∣_ U) ≫ U.ι))
  have : IsDominant a.target.ι := Opens.isDominant_ι a.dense_target
  have : IsOpenImmersion a.toPartialMap.hom :=
    inferInstanceAs (IsOpenImmersion (a.iso.hom ≫ a.target.ι))
  have : IsDominant a.toPartialMap.hom :=
    inferInstanceAs (IsDominant (a.iso.hom ≫ a.target.ι))
  have : IsOpenImmersion (b.hom ∣_ a.toPartialMap.domain) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict b.hom _).flip ‹_›
  let e := b.domain.ι.isoImage (b.hom ⁻¹ᵁ a.toPartialMap.domain)
  have : IsOpenImmersion e.inv := IsOpenImmersion.of_isIso e.inv
  have : IsOpenImmersion (b.comp a.toPartialMap).hom := by
    rw [Scheme.PartialMap.comp_hom]
    exact IsOpenImmersion.comp e.inv (b.hom ∣_ a.toPartialMap.domain ≫ a.toPartialMap.hom)
  have hb : b.equiv p.toPartialMap := p.toPartialMap.restrict_equiv ..
  have he : (b.comp a.toPartialMap).toRationalMap = f.toRationalMap := calc
    _ = (p.toPartialMap.comp a.toPartialMap).toRationalMap :=
      Scheme.PartialMap.toRationalMap_eq_iff.mpr
        (Scheme.PartialMap.comp_equiv_of_equiv_left hb _)
    _ = p.toRationalMap.comp a.toRationalMap :=
      (Scheme.RationalMap.toRationalMap_comp p.toPartialMap a.toPartialMap).symm
    _ = _ := h
  have : IsDominant (b.comp a.toPartialMap).hom :=
    (Scheme.PartialMap.isDominant_toRationalMap_iff _).mp
      (Scheme.RationalMap.toRationalMap_comp b a.toPartialMap ▸ inferInstance)
  exact of_toRationalMap_eq f _ he.symm

end TauCeti.AlgebraicGeometry.IsModification
