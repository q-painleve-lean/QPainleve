/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.AlgebraicGeometry.Morphisms.Pullback.IsoLocus
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Reduced closed subschemes under base change

A compatible closed subscheme of a pullback is the reduced inverse image if it
already gives the reduced inverse image in the base. This applies to strict
boundaries of internal blowup models under a subdivision of their toric bases.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

/-- A closed embedding with the pulled-back ideal of a closed subscheme identifies
its source with that subscheme along the ambient isomorphism. -/
theorem exists_iso_of_comap_eq_ker {X Y Z : Scheme.{u}} (D : Y.IdealSheafData)
    (e : X ≅ Y) (j : Z ⟶ X) [IsClosedImmersion j] (h : D.comap e.hom = j.ker) :
    ∃ d : Z ≅ D.subscheme, d.hom ≫ D.subschemeι = j ≫ e.hom := by
  have hker : D.subschemeι.ker = (j ≫ e.hom).ker := by
    rw [ker_subschemeι]
    have h' := h.trans (j.comap_ker_comp_of_isClosedImmersion e.hom).symm
    simpa only [← comap_comp, Iso.inv_hom_id, comap_id] using congrArg (·.comap e.inv) h'
  let d := IsClosedImmersion.lift D.subschemeι (j ≫ e.hom) hker.le
  have : IsIso d := IsClosedImmersion.isIso_lift _ _ hker
  exact ⟨asIso d, IsClosedImmersion.lift_fac _ _ _⟩

/-- The reduced inverse image of a reduced closed subscheme agrees with that
subscheme over the isomorphism locus of the ambient morphism. -/
theorem preimage_isoLocus_le_subschemeMap_radical {X Y : Scheme.{u}}
    (D : X.IdealSheafData) [IsReduced D.subscheme] (f : Y ⟶ X) :
    D.subschemeι ⁻¹ᵁ f.isoLocus ≤
      (subschemeMap (D.comap f).radical D f
        (le_map_iff_comap_le.mpr (le_radical _))).isoLocus := by
  let I := D.comap f
  let g := subschemeMap I D f (D.le_map_comap f)
  let r := subschemeMap I.radical I (𝟙 Y) (by simpa using I.le_radical)
  let d := subschemeMap I.radical D f (le_map_iff_comap_le.mpr I.le_radical)
  have hr : r ≫ I.subschemeι = I.radical.subschemeι := by simp [r]
  have hd : r ≫ g = d := by
    apply (cancel_mono D.subschemeι).mp
    simp only [Category.assoc, g, d, subschemeMap_subschemeι, reassoc_of% hr]
  have hg : IsPullback I.subschemeι g f D.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (by simp [g]) (by simp [I])
  let V := D.subschemeι ⁻¹ᵁ f.isoLocus
  have hV : IsIso (g ∣_ V) :=
    g.le_isoLocus_iff.mp (Scheme.Hom.preimage_isoLocus_le_of_isPullback hg.flip)
  have : IsClosedImmersion (r ≫ I.subschemeι) := hr.symm ▸ inferInstance
  have : IsClosedImmersion r := .of_comp_isClosedImmersion r I.subschemeι
  have : Surjective r := ⟨fun x ↦ by
    have hx : I.subschemeι x ∈ Set.range I.radical.subschemeι := by
      rw [range_subschemeι, support_radical, ← range_subschemeι]
      exact Set.mem_range_self x
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, I.subschemeι.isClosedEmbedding.injective (by
      simpa only [← Scheme.Hom.comp_apply, hr] using hy)⟩⟩
  have : IsReduced (g ⁻¹ᵁ V).toScheme := isReduced_of_isOpenImmersion (g ∣_ V)
  have : Surjective (r ∣_ (g ⁻¹ᵁ V)) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict r _).flip ‹Surjective r›
  have hR : IsIso (r ∣_ (g ⁻¹ᵁ V)) := isIso_of_isClosedImmersion_of_surjective _
  apply d.le_isoLocus_iff.mpr
  rw [← hd, morphismRestrict_comp]
  exact IsIso.comp_isIso' hR hV

/-- In a cartesian square, a reduced closed subscheme over the reduced inverse image
of a closed subscheme of the base is the reduced inverse image upstairs, provided
the two closed embeddings commute with the projections and the horizontal map. -/
theorem radical_comap_ker_eq_of_isPullback
    {X X' S S' D D' : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} {g : X' ⟶ X} {p : S' ⟶ S}
    (h : IsPullback g f' f p) (j : D ⟶ X) (j' : D' ⟶ X') (d : D' ⟶ D)
    [IsClosedImmersion j] [IsClosedImmersion j'] [IsClosedImmersion (j ≫ f)]
    [IsClosedImmersion (j' ≫ f')] [IsReduced D']
    (hj : j' ≫ g = d ≫ j) (hbase : (((j ≫ f).ker).comap p).radical = (j' ≫ f').ker) :
    (j.ker.comap g).radical = j'.ker := by
  let I := j.ker.comap g
  let q := subschemeMap I j.ker g (j.ker.le_map_comap g) ≫ inv j.toImage
  have hq : q ≫ j = I.subschemeι ≫ g := by
    simp only [q, Category.assoc, ← j.toImage_imageι, IsIso.inv_hom_id_assoc,
      Hom.imageι, subschemeMap_subschemeι]
  let a := I.subschemeι ≫ f'
  have ha : IsPullback q a (j ≫ f) p := by
    refine (j.ker.isPullback_subschemeMap_comap f h).of_iso'
      (Iso.refl _) (asIso j.toImage) (Iso.refl _) (Iso.refl _)
      (by simp [q, I]) (by simp [a, I]) (by simp) (by simp)
  have : IsClosedImmersion a := MorphismProperty.of_isPullback ha inferInstance
  have hk : a.ker = (j ≫ f).ker.comap p := ker_eq_comap_of_isPullback _ ha.flip
  let l := IsClosedImmersion.lift a (j' ≫ f') (hk ▸ (le_radical _).trans_eq hbase)
  have hl : l ≫ a = j' ≫ f' := IsClosedImmersion.lift_fac _ _ _
  have hlq : l ≫ q = d := by
    apply (cancel_mono (j ≫ f)).mp
    rw [Category.assoc, ha.w, ← Category.assoc, hl, Category.assoc, ← h.w,
      ← Category.assoc, hj, Category.assoc]
  have hlj : l ≫ I.subschemeι = j' := by
    apply h.hom_ext
    · rw [Category.assoc, ← hq, ← Category.assoc, hlq, hj]
    · exact hl
  have hr : Set.range a = Set.range (j' ≫ f') := by
    rw [← a.isClosedEmbedding.isClosed_range.closure_eq, ← a.support_ker, hk,
      ← support_radical, hbase, (j' ≫ f').support_ker,
      (j' ≫ f').isClosedEmbedding.isClosed_range.closure_eq]
  have hsurj : Function.Surjective l := by
    intro x
    obtain ⟨y, hy⟩ := hr.subset (Set.mem_range_self x)
    exact ⟨y, a.isClosedEmbedding.injective (by simpa only [← Scheme.Hom.comp_apply, hl] using hy)⟩
  have hsupport : I.support = j'.ker.support := by
    apply SetLike.coe_injective
    rw [← range_subschemeι, j'.support_ker, j'.isClosedEmbedding.isClosed_range.closure_eq,
      ← hlj, Scheme.Hom.comp_base, TopCat.coe_comp, hsurj.range_comp]
  have hreduced : IsReduced j'.ker.subscheme := isReduced_of_isOpenImmersion (inv j'.toImage)
  rw [← vanishingIdeal_support, hsupport, vanishingIdeal_support,
    (isReduced_subscheme_iff_radical_eq _).mp hreduced]

end AlgebraicGeometry.Scheme.IdealSheafData
