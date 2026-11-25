/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.TwistingSheaf.BaseChange

import QPainleve.AlgebraicGeometry.Modules.Pullback.Sections
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback

/-!
# The base-change isomorphism for relative twisting sheaves

The glued comparison is an isomorphism for algebras generated in degree one. Its
pullback to an affine chart is identified with the affine comparison by the
adjoints of the chart projections. See [Stacks, Lemma 27.16.10][stacks-01O3].

[stacks-01O3]: https://stacks.math.columbia.edu/tag/01O3
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (A : GradedQuasicoherentAlgebra Y) (f : X ⟶ Y) (n : ℤ)

local notation "B" => ObjectProperty.FullSubcategory.obj (Functor.obj (pullback f) A)
local notation "baseChange" => A.relativeProjBaseChange f
local notation "D₁" => CommMon.relativeProjTwistingSheafGlueData B n
local notation "D₂" => A.obj.relativeProjTwistingSheafGlueData n
local notation "j₁[" V "]" => colimit.ι
  (Scheme.Cover.RelativeGluingData.functor (CommMon.relativeProjGluingData B)) V
local notation "j₂[" U "]" => colimit.ι A.obj.relativeProjGluingData.functor U
local notation "chartSquare" i:arg =>
  A.relativeProjCover_f_relativeProjBaseChange f (BaseChangeChart.source i)
    (BaseChangeChart.target i) (BaseChangeChart.le i)

private theorem pullback_twistingSheafMap_comp_chartProjection (i : BaseChangeChart f) :
    let j := j₁[i.source]
    let k := j₂[i.target]
    let c := A.relativeProjBaseChangeChartMap f i.le
    let L := (D₂).glued
    let π₁ := ((pullbackPushforwardAdjunction j).homEquiv _ _).symm ((D₁).π i.source)
    let π₂ := ((pullbackPushforwardAdjunction k).homEquiv _ _).symm ((D₂).π i.target)
    (Scheme.Modules.pullbackComp j baseChange).inv.app L ≫ (Scheme.Modules.pullback j).map
      (A.relativeProjBaseChangeTwistingSheafMap f n) ≫ π₁ =
    (Scheme.Modules.pullbackCongr (chartSquare i)).hom.app L ≫
      (Scheme.Modules.pullbackComp c k).inv.app L ≫ (Scheme.Modules.pullback c).map π₂ ≫
      Proj.pullbackTwistingSheafMap (A.pullbackGradedSectionsGradedHom f i.le)
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom f i.le
          i.target.property i.source.property) n := by
  intro j k c L π₁ π₂
  refine pullback_hom_ext (g := j ≫ baseChange) (M := L) ?_
  intro W s
  let μ := A.relativeProjBaseChangeTwistingSheafMap f n
  let φ := A.pullbackGradedSectionsGradedHom f i.le
  let hφ := A.irrelevant_le_map_pullbackGradedSectionsGradedHom f i.le
    i.target.property i.source.property
  let ν := Proj.pullbackTwistingSheafMap φ hφ n
  let t := μ.app (baseChange ⁻¹ᵁ W) ((baseChange).pullbackSections L W s)
  have hj := (pullbackPushforwardAdjunction_homEquiv_app_apply j π₁ (baseChange ⁻¹ᵁ W) t).symm
  have hk := (pullbackPushforwardAdjunction_homEquiv_app_apply k π₂ W s).symm
  simp only [π₁, π₂, Equiv.apply_symm_apply] at hj hk
  let s₂ := ((D₂).π i.target).app W s
  have hc := Proj.pullbackTwistingSheafMap_app_pullbackSections φ hφ n (k ⁻¹ᵁ W) s₂
  have hsec := congr($(Proj.twistingSheafMap_app φ hφ (n := n) (k ⁻¹ᵁ W)) s₂)
  refine (Scheme.Modules.pullbackComp_inv_comp_app_pullbackSections j baseChange μ π₁ W s).trans ?_
  refine hj.trans ((A.relativeProjBaseChangeTwistingSheafMap_app_pullbackSections
    f n i.source i.target i.le W s).trans ?_)
  have h : j ≫ baseChange = c ≫ k := chartSquare i
  let localMap := (Scheme.Modules.pullbackComp c k).inv.app L ≫
    (Scheme.Modules.pullback c).map π₂ ≫ ν
  have htransport := Scheme.Hom.pullbackCongr_hom_comp_app_pullbackSections h localMap W s
  refine Eq.trans ?_ htransport.symm
  refine congrArg (((D₁).obj i.source).presheaf.map
    (eqToHom (congrArg (· ⁻¹ᵁ W) (chartSquare i))).op) ?_
  exact hsec.trans (hc.symm.trans ((congrArg (fun z ↦ ν.app (c ⁻¹ᵁ (k ⁻¹ᵁ W))
    (c.pullbackSections _ (k ⁻¹ᵁ W) z)) hk.symm).trans
      (Scheme.Modules.pullbackComp_inv_comp_app_pullbackSections c k π₂ ν W s).symm))

private theorem isIso_pullback_chart_relativeProjBaseChangeTwistingSheafMap
    (hA : A.obj.IsGeneratedInDegreeOne) (i : BaseChangeChart f) :
    IsIso ((Scheme.Modules.pullback j₁[i.source]).map
      (A.relativeProjBaseChangeTwistingSheafMap f n)) := by
  let j := j₁[i.source]
  let k := j₂[i.target]
  let c := A.relativeProjBaseChangeChartMap f i.le
  have := (B).isOpenImmersion_colimit_ι_relativeProjGluingData i.source
  have := A.obj.isOpenImmersion_colimit_ι_relativeProjGluingData i.target
  let π₁ := ((pullbackPushforwardAdjunction j).homEquiv _ _).symm ((D₁).π i.source)
  let π₂ := ((pullbackPushforwardAdjunction k).homEquiv _ _).symm ((D₂).π i.target)
  have hπ₁ : IsIso π₁ := isIso_pullbackPushforwardAdjunction_homEquiv_symm_of_bijective
    j _ _ _ fun _ hV ↦ (D₁).bijective_π_app
      ((B).bijective_relativeProjTwistingSheafGlueData_map_app n) hV
  have hπ₂ : IsIso π₂ := isIso_pullbackPushforwardAdjunction_homEquiv_symm_of_bijective
    k _ _ _ fun _ hV ↦ (D₂).bijective_π_app
      (A.obj.bijective_relativeProjTwistingSheafGlueData_map_app n) hV
  let φ := A.pullbackGradedSectionsGradedHom f i.le
  let hφ := A.irrelevant_le_map_pullbackGradedSectionsGradedHom f i.le
    i.target.property i.source.property
  have hIso := Proj.isIso_pullbackTwistingSheafMap φ hφ Subtype.val Subtype.property
    (Proj.iSup_basicOpen_eq_top_of_adjoin_eq_top _
      (CommMon.isGeneratedInDegreeOne_iff.mp hA i.target.toOpens i.target.property)) n
  let L := (D₂).glued
  have hMap := @Functor.map_isIso _ _ _ _ _ _ (Scheme.Modules.pullback c) π₂ hπ₂
  let e₁ := (Scheme.Modules.pullbackComp j baseChange).app L
  let e₂ := (Scheme.Modules.pullbackCongr (chartSquare i)).app L
  let e₃ := (Scheme.Modules.pullbackComp c k).app L
  let μ := (Scheme.Modules.pullback j).map (A.relativeProjBaseChangeTwistingSheafMap f n)
  let ν := Proj.pullbackTwistingSheafMap φ hφ n
  have h : e₁.inv ≫ μ ≫ π₁ = e₂.hom ≫ e₃.inv ≫ (Scheme.Modules.pullback c).map π₂ ≫ ν :=
    pullback_twistingSheafMap_comp_chartProjection A f n i
  have hRight : IsIso (e₂.hom ≫ e₃.inv ≫ (Scheme.Modules.pullback c).map π₂ ≫ ν) :=
    IsIso.comp_isIso' e₂.isIso_hom
      (IsIso.comp_isIso' e₃.isIso_inv (IsIso.comp_isIso' hMap hIso))
  have hComp : IsIso (e₁.inv ≫ μ ≫ π₁) := by
    as_aux_lemma => exact Eq.mpr (congrArg IsIso h) hRight
  have hμ := @IsIso.of_isIso_comp_left _ _ _ _ _ e₁.inv (μ ≫ π₁) e₁.isIso_inv hComp
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ μ π₁ hπ₁ hμ

/-- The canonical base-change comparison on relative twisting sheaves is an isomorphism
for an algebra generated in degree one, for every integer twist. -/
theorem isIso_relativeProjBaseChangeTwistingSheafMap (hA : A.obj.IsGeneratedInDegreeOne) :
    IsIso (A.relativeProjBaseChangeTwistingSheafMap f n) := by
  have (i : BaseChangeChart f) : IsOpenImmersion (j₁[i.source]) :=
    (B).isOpenImmersion_colimit_ι_relativeProjGluingData i.source
  refine (isIso_iff_of_isOpenCover_opensRange (fun i : BaseChangeChart f ↦ j₁[i.source])
    (top_unique ?_) _).mpr (isIso_pullback_chart_relativeProjBaseChangeTwistingSheafMap A f n hA)
  intro x _
  obtain ⟨i, hi⟩ := BaseChangeChart.exists_mem f ((B).relativeProjToBase x)
  exact TopologicalSpace.Opens.mem_iSup.mpr
    ⟨i, ((B).relativeProjToBase_preimage i.source).le hi⟩

end TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra
