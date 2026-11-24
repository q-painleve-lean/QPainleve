/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeProj.BaseChange
public import TauCeti.AlgebraicGeometry.RelativeProj.Basic

/-!
# Base change of relative projective spectra

Relative projective spectra of graded quasi-coherent algebras commute with arbitrary
base change. The comparison is computed by pullback of graded sections on affine opens.

The construction glues the squares from
`GradedQuasicoherentAlgebra.isPullback_proj_pullbackGradedSections`, as in
[Stacks, Lemma 27.16.10](https://stacks.math.columbia.edu/tag/01O3).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open Scheme (AffineZariskiSite)
open Scheme.AffineZariskiSite (toOpensFunctor)

universe u

namespace TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (A : GradedQuasicoherentAlgebra Y) (f : X ⟶ Y)

local notation "B" => ObjectProperty.FullSubcategory.obj (Functor.obj (pullback f) A)
local notation "P[" a "," U "]" =>
  Proj (CommMon.gradedSectionsGrading a (AffineZariskiSite.toOpens U))

/-- A pair of affine opens on which the base-change projection is computed by the
pullback of graded sections. -/
@[ext]
structure BaseChangeChart (f : X ⟶ Y) where
  /-- The affine open in the source. -/
  source : X.AffineZariskiSite
  /-- The affine open in the target. -/
  target : Y.AffineZariskiSite
  /-- The source open lies over the target open. -/
  le : source.toOpens ≤ f ⁻¹ᵁ target.toOpens

/-- The source opens of base-change chart pairs cover the source scheme. -/
theorem BaseChangeChart.exists_mem (x : X) :
    ∃ i : BaseChangeChart f, x ∈ i.source.toOpens := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) (⊤ : Y.Opens).is_open'
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      hxU (f ⁻¹ᵁ U).is_open'
  exact ⟨⟨⟨V, hV⟩, ⟨U, hU⟩, hVU⟩, hxV⟩

/-- Two base-change chart pairs admit a common refinement near any point in their
source overlap, by basic opens in both source and target. -/
theorem BaseChangeChart.exists_refinement (i j : BaseChangeChart f) (x : X)
    (hi : x ∈ i.source.toOpens) (hj : x ∈ j.source.toOpens) :
    ∃ k : BaseChangeChart f, k.source ≤ i.source ∧ k.source ≤ j.source ∧
      k.target ≤ i.target ∧ k.target ≤ j.target ∧ x ∈ k.source.toOpens := by
  obtain ⟨a, b, hab, hfx⟩ :=
    exists_basicOpen_le_affine_inter i.target.property j.target.property (f x)
      ⟨i.le hi, j.le hj⟩
  obtain ⟨c, d, hcd, hx⟩ :=
    exists_basicOpen_le_affine_inter i.source.property j.source.property x ⟨hi, hj⟩
  let W := i.source.basicOpen c
  obtain ⟨e, he, hxe⟩ := W.property.exists_basicOpen_le
    (⟨x, hfx⟩ : ↑(f ⁻¹ᵁ Y.basicOpen a)) hx
  exact ⟨⟨W.basicOpen e, i.target.basicOpen a, he⟩,
    (W.basicOpen_le e).trans (i.source.basicOpen_le c),
    (W.basicOpen_le e).trans ⟨d, hcd.symm⟩,
    i.target.basicOpen_le a, ⟨b, hab.symm⟩, hxe⟩

/-- The affine chart of the base-change projection is the projective map induced by
pullback of graded sections. -/
@[expose]
def relativeProjBaseChangeChartMap {V : X.AffineZariskiSite} {U : Y.AffineZariskiSite}
    (h : V.toOpens ≤ f ⁻¹ᵁ U.toOpens) : P[B,V] ⟶ P[A.obj,U] :=
  Proj.map (A.pullbackGradedSectionsGradedHom f h)
    (A.irrelevant_le_map_pullbackGradedSectionsGradedHom f h U.property V.property)

@[reassoc]
private theorem chartMap_naturality {V V' : X.AffineZariskiSite} {U U' : Y.AffineZariskiSite}
    (v : V' ⟶ V) (u : U' ⟶ U) (h : V.toOpens ≤ f ⁻¹ᵁ U.toOpens)
    (h' : V'.toOpens ≤ f ⁻¹ᵁ U'.toOpens) :
    (B).relativeProjFunctor.map v ≫ relativeProjBaseChangeChartMap A f h =
      relativeProjBaseChangeChartMap A f h' ≫ A.obj.relativeProjFunctor.map u := by
  -- The gluing transition exposes the graded ring map used by the functor.
  change (B).relativeProjGluingData.functor.map v ≫ relativeProjBaseChangeChartMap A f h =
    relativeProjBaseChangeChartMap A f h' ≫ A.obj.relativeProjGluingData.functor.map u
  rw [CommMon.relativeProjGluingData_functor_map, CommMon.relativeProjGluingData_functor_map]
  unfold relativeProjBaseChangeChartMap
  erw [← Proj.map_comp, ← Proj.map_comp]
  apply Proj.map_congr
  exact (restrictGradedSectionsGradedHom_comp_pullbackGradedSectionsGradedHom
    f A h ((toOpensFunctor X).map v)).trans
      (pullbackGradedSectionsGradedHom_comp_restrictGradedSectionsGradedHom
        f A ((toOpensFunctor Y).map u) h').symm

private def baseCover : X.OpenCover where
  I₀ := BaseChangeChart f
  X i := i.source.toOpens
  f i := i.source.toOpens.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ inferInstance⟩
    obtain ⟨i, hi⟩ := BaseChangeChart.exists_mem f x
    exact ⟨i, ⟨⟨x, hi⟩, rfl⟩⟩

private def projCover : (B).relativeProj.OpenCover where
  I₀ := BaseChangeChart f
  X i := P[B,i.source]
  f i := (B).relativeProjCover.f i.source
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ CommMon.isOpenImmersion_relativeProjCover_f B i.source⟩
    obtain ⟨i, hi⟩ := BaseChangeChart.exists_mem f ((B).relativeProjToBase x)
    refine ⟨i, ?_⟩
    have hRange : x ∈ ((B).relativeProjCover.f i.source).opensRange := by
      rwa [← (B).relativeProjToBase_preimage]
    exact hRange

private theorem chartMap_comp_cover {i k : BaseChangeChart f}
    (v : k.source ⟶ i.source) (u : k.target ⟶ i.target) :
    (B).relativeProjFunctor.map v ≫ relativeProjBaseChangeChartMap A f i.le ≫
      A.obj.relativeProjCover.f i.target =
      relativeProjBaseChangeChartMap A f k.le ≫ A.obj.relativeProjCover.f k.target := by
  exact (chartMap_naturality_assoc A f v u i.le k.le _).trans
    (congrArg (relativeProjBaseChangeChartMap A f k.le ≫ ·)
      (colimit.w A.obj.relativeProjGluingData.functor u))

private theorem chartMap_glue (i j : BaseChangeChart f) :
    pullback.fst ((projCover A f).f i) ((projCover A f).f j) ≫
      relativeProjBaseChangeChartMap A f i.le ≫ A.obj.relativeProjCover.f i.target =
    pullback.snd ((projCover A f).f i) ((projCover A f).f j) ≫
      relativeProjBaseChangeChartMap A f j.le ≫ A.obj.relativeProjCover.f j.target := by
  let p := (projCover A f).f i
  let q := (projCover A f).f j
  -- Refine the two pairs of affine opens at each point of the overlap.
  apply Scheme.hom_ext_of_forall
  intro z
  let y := (pullback.fst p q ≫ p) z
  have hy : y = (pullback.snd p q ≫ q) z :=
    congrArg (fun g : Limits.pullback p q ⟶ (B).relativeProj ↦ g z) pullback.condition
  have hi : y ∈ ((B).relativeProjToBase ⁻¹ᵁ i.source.toOpens) := by
    rw [(B).relativeProjToBase_preimage]
    exact ⟨pullback.fst p q z, rfl⟩
  have hj : y ∈ ((B).relativeProjToBase ⁻¹ᵁ j.source.toOpens) := by
    rw [(B).relativeProjToBase_preimage, hy]
    exact ⟨pullback.snd p q z, rfl⟩
  obtain ⟨k, vi, vj, ui, uj, hk⟩ := BaseChangeChart.exists_refinement f i j _ hi hj
  let pi := (B).relativeProjFunctor.map (homOfLE vi)
  let pj := (B).relativeProjFunctor.map (homOfLE vj)
  have hpi : pi ≫ p = (B).relativeProjCover.f k.source :=
    colimit.w (B).relativeProjGluingData.functor (homOfLE vi)
  have hpj : pj ≫ q = (B).relativeProjCover.f k.source :=
    colimit.w (B).relativeProjGluingData.functor (homOfLE vj)
  let l := pullback.lift pi pj (hpi.trans hpj.symm)
  have hfst : l ≫ pullback.fst p q = pi := pullback.lift_fst _ _ _
  have hsnd : l ≫ pullback.snd p q = pj := pullback.lift_snd _ _ _
  have hl : l ≫ pullback.fst p q ≫ p = (B).relativeProjCover.f k.source :=
    ((reassoc_of% hfst) p).trans hpi
  have hOpen : IsOpenImmersion (l ≫ pullback.fst p q ≫ p) :=
    hl ▸ CommMon.isOpenImmersion_relativeProjCover_f B k.source
  have hOverlap : IsOpenImmersion (pullback.fst p q ≫ p) :=
    @IsOpenImmersion.comp _ _ _ _ _
      (IsOpenImmersion.pullback_fst p q (CommMon.isOpenImmersion_relativeProjCover_f B j.source))
      (CommMon.isOpenImmersion_relativeProjCover_f B i.source)
  have hLift : IsOpenImmersion l := @IsOpenImmersion.of_comp _ _ _ l _ hOverlap hOpen
  have hyk : y ∈ ((B).relativeProjCover.f k.source).opensRange := by
    rwa [← (B).relativeProjToBase_preimage]
  obtain ⟨z', hz'⟩ := hyk
  have hz : z ∈ @Scheme.Hom.opensRange _ _ l hLift :=
    ⟨z', (@Scheme.Hom.isOpenEmbedding _ _ _ hOverlap).injective
      ((congrArg (fun g : P[B,k.source] ⟶ (B).relativeProj ↦ g z') hl).trans hz')⟩
  refine ⟨_, hz, (cancel_epi (@Scheme.Hom.isoOpensRange _ _ l hLift).hom).mp ?_⟩
  let F := relativeProjBaseChangeChartMap A f i.le ≫ A.obj.relativeProjCover.f i.target
  let G := relativeProjBaseChangeChartMap A f j.le ≫ A.obj.relativeProjCover.f j.target
  have hi' : l ≫ pullback.fst p q ≫ F = pi ≫ F :=
    (Category.assoc ..).symm.trans (congrArg (· ≫ F) hfst)
  have hj' : l ≫ pullback.snd p q ≫ G = pj ≫ G :=
    (Category.assoc ..).symm.trans (congrArg (· ≫ G) hsnd)
  exact (@Scheme.Hom.isoOpensRange_hom_ι_assoc _ _ l hLift _ _).trans (hi'.trans
    ((chartMap_comp_cover A f (homOfLE vi) (homOfLE ui)).trans
      ((chartMap_comp_cover A f (homOfLE vj) (homOfLE uj)).symm.trans
        (hj'.symm.trans (@Scheme.Hom.isoOpensRange_hom_ι_assoc _ _ l hLift _ _).symm))))

/-- The comparison from the relative projective spectrum of the pulled-back graded algebra
to the original projective spectrum. On affine charts it is given by pullback of sections. -/
def relativeProjBaseChange : (B).relativeProj ⟶ A.obj.relativeProj :=
  (projCover A f).glueMorphisms
    (fun i ↦ relativeProjBaseChangeChartMap A f i.le ≫ A.obj.relativeProjCover.f i.target)
    (chartMap_glue A f)

/-- On an affine source open lying over an affine target open, the base-change comparison
is the map of projective spectra induced by pullback of graded sections. -/
@[reassoc]
theorem relativeProjCover_f_relativeProjBaseChange (V : X.AffineZariskiSite)
    (U : Y.AffineZariskiSite) (h : V.toOpens ≤ f ⁻¹ᵁ U.toOpens) :
    (B).relativeProjCover.f V ≫ A.relativeProjBaseChange f =
      A.relativeProjBaseChangeChartMap f h ≫ A.obj.relativeProjCover.f U :=
  (projCover A f).ι_glueMorphisms _ _ ⟨V, U, h⟩

/-- Maps from the base-changed relative projective spectrum agree if they agree
on the affine source charts lying over affine target opens. -/
theorem relativeProjBaseChange_hom_ext {Z : Scheme.{u}} (g h : (B).relativeProj ⟶ Z)
    (he : ∀ (V : X.AffineZariskiSite) (U : Y.AffineZariskiSite),
      V.toOpens ≤ f ⁻¹ᵁ U.toOpens →
        (B).relativeProjCover.f V ≫ g = (B).relativeProjCover.f V ≫ h) : g = h :=
  (projCover A f).hom_ext g h fun i ↦ he i.source i.target i.le

private theorem chart_isPullback (i : BaseChangeChart f) :
    IsPullback
      (Proj.toSpecCoeff (CommMon.gradedSectionsGrading B i.source.toOpens) ≫
        i.source.property.isoSpec.inv)
      ((B).relativeProjCover.f i.source ≫ A.relativeProjBaseChange f)
      (i.source.toOpens.ι ≫ f) A.obj.relativeProjToBase := by
  -- Paste the affine base-change square with the target chart square.
  have h := (A.isPullback_proj_pullbackGradedSections f i.le
    i.target.property i.source.property).flip
  have hU : IsPullback (A.obj.relativeProjCover.f i.target)
      (Proj.toSpecCoeff (CommMon.gradedSectionsGrading A.obj i.target.toOpens))
      A.obj.relativeProjToBase i.target.property.fromSpec := by
    exact ((A.obj.isPullback_relativeProjCover i.target).flip).of_iso
      (Iso.refl _) (Iso.refl _) i.target.property.isoSpec (Iso.refl _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      (by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        exact (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      (by simp only [Iso.refl_hom, Category.comp_id, IsAffineOpen.isoSpec_hom_fromSpec])
  have h' := h.paste_vert hU.flip
  exact h'.of_iso (Iso.refl _) i.source.property.isoSpec.symm (Iso.refl _) (Iso.refl _)
    (by simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp])
    ((Category.comp_id _).trans
      ((A.relativeProjCover_f_relativeProjBaseChange f i.source i.target i.le).symm.trans
        (Category.id_comp _).symm))
    ((Category.comp_id _).trans
      ((IsAffineOpen.SpecMap_appLE_fromSpec f i.target.property i.source.property i.le).trans
        (Category.assoc ..)))
    (by simp)

/-- Relative projective spectrum commutes with pullback along any morphism of schemes. -/
theorem isPullback_relativeProjBaseChange :
    IsPullback (B).relativeProjToBase (A.relativeProjBaseChange f) f A.obj.relativeProjToBase := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (baseCover f) fun i ↦ ?_
  let h := ((B).isPullback_relativeProjCover i.source).flip
  have hf : h.isoPullback.hom ≫ ((baseCover f).pullback₁ (B).relativeProjToBase).f i =
      (B).relativeProjCover.f i.source := h.isoPullback_hom_fst
  exact (chart_isPullback A f i).of_iso h.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.comp_id _).trans h.isoPullback_hom_snd.symm)
    ((Category.comp_id _).trans (((reassoc_of% hf) (A.relativeProjBaseChange f)).symm.trans
      (Category.assoc ..)))
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The base-change comparison lies over the given map of bases. -/
@[reassoc (attr := simp)]
theorem relativeProjBaseChange_toBase :
    A.relativeProjBaseChange f ≫ A.obj.relativeProjToBase = (B).relativeProjToBase ≫ f :=
  (A.isPullback_relativeProjBaseChange f).w.symm

end TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra
