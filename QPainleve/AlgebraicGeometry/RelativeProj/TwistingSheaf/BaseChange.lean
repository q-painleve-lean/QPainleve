/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.BaseChange
public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf

import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
import TauCeti.AlgebraicGeometry.Modules.Pushforward.Basic
import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections

/-!
# Twisting sheaves under relative projective base change

The comparison on each pair of affine charts is Tau Ceti's
`AlgebraicGeometry.Proj.pullbackTwistingSheafMap`. Compatibility under simultaneous
refinements glues these maps to a comparison on the relative projective spectrum.
For algebras generated in degree one, the twisting sheaves on each pair of charts
are identified by the affine base-change isomorphisms.
See [Stacks, Lemma 27.16.10](https://stacks.math.columbia.edu/tag/01O3).
-/

public noncomputable section

open _root_.AlgebraicGeometry CategoryTheory Limits Opposite
open Scheme.AffineZariskiSite (toOpensFunctor)

universe u

namespace TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (A : GradedQuasicoherentAlgebra Y) (f : X ⟶ Y)

local notation "B" => ObjectProperty.FullSubcategory.obj (Functor.obj (pullback f) A)
local notation "P[" a "," U "]" =>
  Proj (CommMon.gradedSectionsGrading a (Scheme.AffineZariskiSite.toOpens U))

open Scheme.Modules

variable (n : ℤ)

local notation "D₁" => CommMon.relativeProjTwistingSheafGlueData B n
local notation "D₂" => A.obj.relativeProjTwistingSheafGlueData n
local notation "FunctorScheme" a:arg => Scheme.Cover.RelativeGluingData.functor
  (CommMon.relativeProjGluingData a)
local notation "Q₁" => colimit (FunctorScheme B)
local notation "Q₂" => colimit (FunctorScheme A.obj)
-- The gluing datum is indexed on the colimit presentation of relative Proj.
private def colimitBaseChange : Q₁ ⟶ Q₂ := A.relativeProjBaseChange f

local notation "g" => colimitBaseChange A f
local notation "PUSH" => Scheme.Modules.pushforward (X := Q₁) (Y := Q₂) g
local notation "PULL" => Scheme.Modules.pullback (X := Q₁) (Y := Q₂) g
local notation "ADJ" => Scheme.Modules.pullbackPushforwardAdjunction (X := Q₁) (Y := Q₂) g
local notation "j₁[" V "]" => colimit.ι (FunctorScheme B) V
local notation "j₂[" U "]" => colimit.ι (FunctorScheme A.obj) U

private theorem chartMap_comp_cover_eq (i : BaseChangeChart f) :
    j₁[i.source] ≫ g = relativeProjBaseChangeChartMap A f i.le ≫ j₂[i.target] :=
  A.relativeProjCover_f_relativeProjBaseChange f i.source i.target i.le

private def twistingSheafChartComponent (i : BaseChangeChart f) :
    (D₂).glued ⟶ (PUSH).obj ((pushforward j₁[i.source]).obj ((D₁).obj i.source)) :=
  (D₂).π i.target ≫ (pushforward j₂[i.target]).map
      (Proj.twistingSheafMap (A.pullbackGradedSectionsGradedHom f i.le)
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom f i.le
          i.target.property i.source.property) n) ≫
    (pushforwardComp (relativeProjBaseChangeChartMap A f i.le) j₂[i.target]).hom.app _ ≫
    (pushforwardCongr (chartMap_comp_cover_eq A f i).symm).hom.app _ ≫
    (pushforwardComp j₁[i.source] g).inv.app _

private theorem twistingSheafChartComponent_app (i : BaseChangeChart f) (W : (Q₂).Opens)
    (s : Γ((D₂).glued, W)) :
    (twistingSheafChartComponent A f n i).app W s =
      ((D₁).obj i.source).presheaf.map
        (eqToHom (congrArg (· ⁻¹ᵁ W) (chartMap_comp_cover_eq A f i))).op
        ((Proj.twistingSheafMap (A.pullbackGradedSectionsGradedHom f i.le)
          (A.irrelevant_le_map_pullbackGradedSectionsGradedHom f i.le
            i.target.property i.source.property) n).app _ (((D₂).π i.target).app W s)) :=
  (rfl)

local notation "T[" i "]" => Functor.obj (pushforward j₁[BaseChangeChart.source i])
  (ModulesGlueData.obj D₁ (BaseChangeChart.source i))
local notation "φ[" i "]" => twistingSheafChartComponent A f n i

private theorem twistingSheafChartComponent_transition {i k : BaseChangeChart f}
    (v : k.source ⟶ i.source) (u : k.target ⟶ i.target)
    (W : (Q₂).Opens) (s : Γ((D₂).glued, W)) :
    ((D₁).transition v).app (g ⁻¹ᵁ W) ((twistingSheafChartComponent A f n i).app W s) =
      (twistingSheafChartComponent A f n k).app W s := by
  let V := g ⁻¹ᵁ W
  let t := ((D₂).π i.target).app W s
  let t₁ : Γ(T[i], V) := (φ[i]).app W s
  have hLeft := (D₁).transition_app_apply v V t₁
  have hRight := ((D₂).transition_app_π_app u W s).symm.trans
    ((D₂).transition_app_apply u W t)
  refine hLeft.trans ((congrArg (fun z ↦ ((D₁).obj k.source).presheaf.map
    (eqToHom (congrArg (· ⁻¹ᵁ V) (colimit.w (FunctorScheme B) v)).symm).op
      (((D₁).map v).app (j₁[i.source] ⁻¹ᵁ V) z))
    (twistingSheafChartComponent_app A f n i W s)).trans ?_)
  refine Eq.trans ?_ (twistingSheafChartComponent_app A f n k W s).symm
  refine Eq.trans ?_ (congrArg (fun z ↦ ((D₁).obj k.source).presheaf.map
    (eqToHom (congrArg (· ⁻¹ᵁ W) (chartMap_comp_cover_eq A f k))).op
    ((Proj.twistingSheafMap (A.pullbackGradedSectionsGradedHom f k.le)
      (A.irrelevant_le_map_pullbackGradedSectionsGradedHom f k.le
        k.target.property k.source.property) n).app (j₂[k.target] ⁻¹ᵁ W) z)) hRight).symm
  let U := j₂[i.target] ⁻¹ᵁ W
  let Vᵢ := j₁[i.source] ⁻¹ᵁ V
  let Uₖ := j₂[k.target] ⁻¹ᵁ W
  let Vₖ := j₁[k.source] ⁻¹ᵁ V
  let ev : Vₖ ⟶ (FunctorScheme B).map v ⁻¹ᵁ Vᵢ :=
    eqToHom (congrArg (· ⁻¹ᵁ V) (colimit.w (FunctorScheme B) v)).symm
  let ei : Vᵢ ⟶ A.relativeProjBaseChangeChartMap f i.le ⁻¹ᵁ U :=
    eqToHom (congrArg (· ⁻¹ᵁ W) (chartMap_comp_cover_eq A f i))
  let ek : Vₖ ⟶ A.relativeProjBaseChangeChartMap f k.le ⁻¹ᵁ Uₖ :=
    eqToHom (congrArg (· ⁻¹ᵁ W) (chartMap_comp_cover_eq A f k))
  let eu : Uₖ ⟶ (FunctorScheme A.obj).map u ⁻¹ᵁ U :=
    eqToHom (congrArg (· ⁻¹ᵁ W) (colimit.w (FunctorScheme A.obj) u)).symm
  have h :=
    Proj.res_twistingSheafMap_app_res_of_comp_eq
      (A.pullbackGradedSectionsGradedHom f i.le)
      (A.irrelevant_le_map_pullbackGradedSectionsGradedHom f i.le
        i.target.property i.source.property)
      ((B).restrictGradedSectionsGradedHom ((toOpensFunctor X).map v))
      ((B).irrelevant_le_map_restrictGradedSections_toOpensFunctor v)
      (A.obj.restrictGradedSectionsGradedHom ((toOpensFunctor Y).map u))
      (A.obj.irrelevant_le_map_restrictGradedSections_toOpensFunctor u)
      (A.pullbackGradedSectionsGradedHom f k.le)
      (A.irrelevant_le_map_pullbackGradedSectionsGradedHom f k.le
        k.target.property k.source.property)
      ((restrictGradedSectionsGradedHom_comp_pullbackGradedSectionsGradedHom
        f A i.le ((toOpensFunctor X).map v)).trans
          (pullbackGradedSectionsGradedHom_comp_restrictGradedSectionsGradedHom
            f A ((toOpensFunctor Y).map u) k.le).symm)
      n (U := U) (V := Vᵢ) (V' := Uₖ) (W := Vₖ) ev ei ek eu t
  exact h

local notation "R[" i "]" => @Scheme.Hom.opensRange _ _ (j₁[BaseChangeChart.source i])
  (CommMon.isOpenImmersion_colimit_ι_relativeProjGluingData B (BaseChangeChart.source i))


private theorem le_iSup_chartRange (V : (Q₁).Opens) :
    V ≤ ⨆ i : BaseChangeChart f, V ⊓ R[i] := by
  intro x hx
  obtain ⟨i, hi⟩ := BaseChangeChart.exists_mem f ((B).relativeProjToBase x)
  have hx' : x ∈ R[i] := ((B).relativeProjToBase_preimage i.source).le hi
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hx'⟩

private theorem chartRange_le_of_hom {i k : BaseChangeChart f} (v : k.source ⟶ i.source) :
    R[k] ≤ R[i] := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨(B).relativeProjGluingData.functor.map v y,
    congrArg (fun m : P[B,k.source] ⟶ Q₁ ↦ m y)
      (colimit.w (B).relativeProjGluingData.functor v)⟩

private def GlueRefinement {f : X ⟶ Y} (i j : BaseChangeChart f) :=
  Σ k : BaseChangeChart f, (k.source ⟶ i.source) × (k.source ⟶ j.source) ×
    (k.target ⟶ i.target) × (k.target ⟶ j.target)

private theorem le_iSup_refinementRange (i j : BaseChangeChart f) (V : (Q₁).Opens)
    (hi : V ≤ R[i]) (hj : V ≤ R[j]) :
    V ≤ ⨆ k : GlueRefinement i j, V ⊓ R[k.1] := by
  intro x hx
  have hi' : x ∈ (B).relativeProjToBase ⁻¹ᵁ i.source.toOpens :=
    ((B).relativeProjToBase_preimage i.source).ge (hi hx)
  have hj' : x ∈ (B).relativeProjToBase ⁻¹ᵁ j.source.toOpens :=
    ((B).relativeProjToBase_preimage j.source).ge (hj hx)
  obtain ⟨k, vi, vj, ui, uj, hk⟩ := BaseChangeChart.exists_refinement f i j _ hi' hj'
  exact TopologicalSpace.Opens.mem_iSup.mpr
    ⟨⟨k, homOfLE vi, homOfLE vj, homOfLE ui, homOfLE uj⟩, hx,
      ((B).relativeProjToBase_preimage k.source).le hk⟩

private theorem bijective_chartProjection (i : BaseChangeChart f) {V : (Q₁).Opens}
    (hV : V ≤ R[i]) : Function.Bijective (((D₁).π i.source).app V) :=
  (D₁).bijective_π_app ((B).bijective_relativeProjTwistingSheafGlueData_map_app n) hV

private def twistingSheafChartSection (i : BaseChangeChart f) (W : (Q₂).Opens)
    (s : Γ((D₂).glued, W)) : Γ((D₁).glued, g ⁻¹ᵁ W ⊓ R[i]) :=
  Function.surjInv (bijective_chartProjection A f n i inf_le_right).surjective
    ((T[i]).presheaf.map (homOfLE inf_le_left).op ((φ[i]).app W s))

private theorem twistingSheafChartSection_π (i : BaseChangeChart f) (W : (Q₂).Opens)
    (s : Γ((D₂).glued, W)) :
    ((D₁).π i.source).app (g ⁻¹ᵁ W ⊓ R[i]) (twistingSheafChartSection A f n i W s) =
      (T[i]).presheaf.map (homOfLE inf_le_left).op ((φ[i]).app W s) :=
  Function.surjInv_eq _ _

private theorem twistingSheafChartSection_π_restrict {i k : BaseChangeChart f}
    (v : k.source ⟶ i.source) (u : k.target ⟶ i.target)
    (W : (Q₂).Opens) (s : Γ((D₂).glued, W))
    {V : (Q₁).Opens} (hV : V ≤ g ⁻¹ᵁ W) (hk : V ≤ R[k]) :
    ((D₁).π k.source).app V ((D₁).glued.presheaf.map
      (homOfLE (le_inf hV (hk.trans (chartRange_le_of_hom A f v)))).op
      (twistingSheafChartSection A f n i W s)) =
      (T[k]).presheaf.map (homOfLE hV).op ((φ[k]).app W s) := by
  let a : V ⟶ (g ⁻¹ᵁ W ⊓ R[i]) :=
    homOfLE (le_inf hV (hk.trans (chartRange_le_of_hom A f v)))
  let t := twistingSheafChartSection A f n i W s
  let τ := ((D₁).transition v).app V
  refine ((D₁).transition_app_π_app v V ((D₁).glued.presheaf.map a.op t)).symm.trans ?_
  refine (congrArg τ
    (NatTrans.naturality_apply ((D₁).π i.source).mapPresheaf a.op t)).trans ?_
  refine (congrArg (fun z ↦ τ ((T[i]).presheaf.map a.op z))
    (twistingSheafChartSection_π A f n i W s)).trans ?_
  let W' : (Q₁).Opens := g ⁻¹ᵁ W
  let b : W' ⊓ R[i] ⟶ W' := homOfLE inf_le_left
  let t₁ : Γ(T[i], W') := (φ[i]).app W s
  have hr := ((T[i]).presheaf.map_comp_apply b.op a.op t₁).symm
  refine (congrArg τ hr).trans ?_
  exact ((D₁).transition_app_map_apply v hV t₁).trans
    (congrArg ((T[k]).presheaf.map (homOfLE hV).op)
      (twistingSheafChartComponent_transition A f n v u W s))

private theorem exists_twistingSheafSection (W : (Q₂).Opens)
    (s : Γ((D₂).glued, W)) :
    ∃ t : Γ((D₁).glued, g ⁻¹ᵁ W),
      ∀ i : BaseChangeChart f, ((D₁).π i.source).app (g ⁻¹ᵁ W) t = (φ[i]).app W s := by
  let V (i : BaseChangeChart f) := g ⁻¹ᵁ W ⊓ R[i]
  let t (i : BaseChangeChart f) := twistingSheafChartSection A f n i W s
  have hcompat : TopCat.Presheaf.IsCompatible (D₁).glued.presheaf V t := by
    intro i j
    refine TopCat.Sheaf.eq_of_locally_eq'
      (⟨(D₁).glued.presheaf, (D₁).glued.isSheaf⟩ : TopCat.Sheaf Ab _)
      (fun k : GlueRefinement i j ↦ V i ⊓ V j ⊓ R[k.1])
      (V i ⊓ V j) (fun _ ↦ homOfLE inf_le_left)
      (le_iSup_refinementRange A f i j _ (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right)) _ _ ?_
    intro k
    let F := (D₁).glued.presheaf
    let a : V i ⊓ V j ⊓ R[k.1] ⟶ V i ⊓ V j := homOfLE inf_le_left
    let bi : V i ⊓ V j ⟶ V i := homOfLE inf_le_left
    let bj : V i ⊓ V j ⟶ V j := homOfLE inf_le_right
    refine (F.map_comp_apply bi.op a.op (t i)).symm.trans
      (Eq.trans ?_ (F.map_comp_apply bj.op a.op (t j)))
    apply (bijective_chartProjection A f n k.1 inf_le_right).injective
    have hW : V i ⊓ V j ⊓ R[k.1] ≤ g ⁻¹ᵁ W :=
      inf_le_left.trans (inf_le_left.trans inf_le_left)
    exact (twistingSheafChartSection_π_restrict A f n k.2.1 k.2.2.2.1 W s hW
      inf_le_right).trans
      (twistingSheafChartSection_π_restrict A f n k.2.2.1 k.2.2.2.2 W s hW inf_le_right).symm
  obtain ⟨q, hq, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨(D₁).glued.presheaf, (D₁).glued.isSheaf⟩ : TopCat.Sheaf Ab _) V (g ⁻¹ᵁ W)
    (fun _ ↦ homOfLE inf_le_left) (le_iSup_chartRange A f _) t hcompat
  refine ⟨q, fun i ↦ ?_⟩
  let := (B).isOpenImmersion_colimit_ι_relativeProjGluingData i.source
  have he : j₁[i.source] ⁻¹ᵁ V i = j₁[i.source] ⁻¹ᵁ g ⁻¹ᵁ W := by
    dsimp only [V]
    rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, inf_top_eq]
  apply (ConcreteCategory.bijective_of_isIso
    (((D₁).obj i.source).presheaf.map (eqToHom he).op)).injective
  exact (NatTrans.naturality_apply ((D₁).π i.source).mapPresheaf
    (homOfLE (inf_le_left : V i ≤ g ⁻¹ᵁ W)).op q).symm.trans
      ((congrArg (((D₁).π i.source).app (V i)) (hq i)).trans
        (twistingSheafChartSection_π A f n i W s))

private theorem twistingSheafSection_ext {V : (Q₁).Opens}
    {s t : Γ((D₁).glued, V)}
    (h : ∀ i : BaseChangeChart f, ((D₁).π i.source).app V s = ((D₁).π i.source).app V t) :
    s = t := by
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨(D₁).glued.presheaf, (D₁).glued.isSheaf⟩ : TopCat.Sheaf Ab _)
    (fun i : BaseChangeChart f ↦ V ⊓ R[i]) V (fun _ ↦ homOfLE inf_le_left)
    (le_iSup_chartRange A f V) s t fun i ↦ ?_
  apply (bijective_chartProjection A f n i inf_le_right).injective
  let v : V ⊓ R[i] ⟶ V := homOfLE inf_le_left
  exact (NatTrans.naturality_apply ((D₁).π i.source).mapPresheaf v.op s).trans
    ((congrArg ((T[i]).presheaf.map v.op) (h i)).trans
      (NatTrans.naturality_apply ((D₁).π i.source).mapPresheaf v.op t).symm)

private def twistingSheafApp (W : (Q₂).Opens) (s : Γ((D₂).glued, W)) :
    Γ((D₁).glued, g ⁻¹ᵁ W) :=
  (exists_twistingSheafSection A f n W s).choose

private theorem twistingSheafApp_π (i : BaseChangeChart f) (W : (Q₂).Opens)
    (s : Γ((D₂).glued, W)) :
    ((D₁).π i.source).app (g ⁻¹ᵁ W) (twistingSheafApp A f n W s) = (φ[i]).app W s :=
  (exists_twistingSheafSection A f n W s).choose_spec i

private theorem twistingSheafApp_add (W : (Q₂).Opens) (s t : Γ((D₂).glued, W)) :
    twistingSheafApp A f n W (s + t) =
      twistingSheafApp A f n W s + twistingSheafApp A f n W t := by
  apply twistingSheafSection_ext A f n
  intro i
  refine (twistingSheafApp_π A f n i W (s + t)).trans ?_
  refine (map_add (ConcreteCategory.hom ((φ[i]).app W)) s t).trans ?_
  exact (congrArg₂ (· + ·) (twistingSheafApp_π A f n i W s).symm
    (twistingSheafApp_π A f n i W t).symm).trans
      (map_add (ConcreteCategory.hom (((D₁).π i.source).app _)) _ _).symm

private theorem twistingSheafApp_smul (W : (Q₂).Opens) (r : Γ(Q₂, W)) (s : Γ((D₂).glued, W)) :
    twistingSheafApp A f n W (r • s) = (g).app W r • twistingSheafApp A f n W s := by
  apply twistingSheafSection_ext A f n
  intro i
  refine (twistingSheafApp_π A f n i W (r • s)).trans ?_
  refine ((φ[i]).app_smul r s).trans ?_
  refine (pushforward_obj_smul g (T[i]) r ((φ[i]).app W s)).trans ?_
  exact (congrArg ((g).app W r • ·) (twistingSheafApp_π A f n i W s).symm).trans
    (((D₁).π i.source).app_smul _ _).symm

private theorem twistingSheafApp_map {U V : (Q₂).Opens} (v : V ⟶ U) (s : Γ((D₂).glued, U)) :
    twistingSheafApp A f n V ((D₂).glued.presheaf.map v.op s) =
      (D₁).glued.presheaf.map ((TopologicalSpace.Opens.map (g).base).map v).op
        (twistingSheafApp A f n U s) := by
  let w := ((TopologicalSpace.Opens.map (g).base).map v).op
  apply twistingSheafSection_ext A f n
  intro i
  refine (twistingSheafApp_π A f n i V _).trans ?_
  refine (NatTrans.naturality_apply (φ[i]).mapPresheaf v.op s).trans ?_
  refine (congrArg ((T[i]).presheaf.map w) (twistingSheafApp_π A f n i U s).symm).trans ?_
  exact (NatTrans.naturality_apply ((D₁).π i.source).mapPresheaf w
    (twistingSheafApp A f n U s)).symm

private def twistingSheafPushforwardMap : (D₂).glued ⟶ (PUSH).obj (D₁).glued :=
  ⟨{
    app := fun W ↦ ConcreteCategory.ofHom (C := ModuleCat _)
      (X := (D₂).glued.val.obj W) (Y := ((PUSH).obj (D₁).glued).val.obj W)
      { toFun := twistingSheafApp A f n W.unop
        map_add' := twistingSheafApp_add A f n W.unop
        map_smul' := twistingSheafApp_smul A f n W.unop }
    naturality := fun v ↦ ModuleCat.hom_ext (LinearMap.ext (twistingSheafApp_map A f n v.unop)) }⟩

private def gluedTwistingSheafMap : (PULL).obj (D₂).glued ⟶ (D₁).glued :=
  ((ADJ).homEquiv _ _).symm (twistingSheafPushforwardMap A f n)

/-- The canonical comparison of twisting sheaves along the base-change projection.
On each pair of affine charts it is induced by pullback of graded sections. -/
def relativeProjBaseChangeTwistingSheafMap :
    (Scheme.Modules.pullback (A.relativeProjBaseChange f)).obj
      (A.obj.relativeProjTwistingSheaf n) ⟶ (B).relativeProjTwistingSheaf n :=
  gluedTwistingSheafMap A f n

/-- The comparison of twisting sheaves is computed on pullbacks of sections by
the map of twisting sheaves on each pair of affine charts. -/
theorem relativeProjBaseChangeTwistingSheafMap_app_pullbackSections
    (V : X.AffineZariskiSite) (U : Y.AffineZariskiSite)
    (h : V.toOpens ≤ f ⁻¹ᵁ U.toOpens)
    (W : A.obj.relativeProj.Opens) (s : Γ(A.obj.relativeProjTwistingSheaf n, W)) :
    ((D₁).π V).app (A.relativeProjBaseChange f ⁻¹ᵁ W)
      ((A.relativeProjBaseChangeTwistingSheafMap f n).app _
        ((A.relativeProjBaseChange f).pullbackSections _ W s)) =
      ((D₁).obj V).presheaf.map
        (eqToHom (congrArg (· ⁻¹ᵁ W) (A.relativeProjCover_f_relativeProjBaseChange f V U h))).op
        ((Proj.twistingSheafMap (A.pullbackGradedSectionsGradedHom f h)
          (A.irrelevant_le_map_pullbackGradedSectionsGradedHom f h U.property V.property)
          n).app (j₂[U] ⁻¹ᵁ W) (((D₂).π U).app W s)) := by
  let i : BaseChangeChart f := ⟨V, U, h⟩
  let μ := gluedTwistingSheafMap A f n
  have hsec : μ.app (g ⁻¹ᵁ W) ((g).pullbackSections ((D₂).glued) W s) =
      twistingSheafApp A f n W s := by
    refine (pullbackPushforwardAdjunction_homEquiv_app_apply g μ W s).symm.trans ?_
    exact congrArg (fun q ↦ q.app W s)
      (Equiv.apply_symm_apply ((ADJ).homEquiv _ _) (twistingSheafPushforwardMap A f n))
  exact (congrArg (((D₁).π V).app (g ⁻¹ᵁ W)) hsec).trans
    ((twistingSheafApp_π A f n i W s).trans (twistingSheafChartComponent_app A f n i W s))

/-- On any affine chart of the base change of a degree-one generated relative projective
spectrum, the pullback of the original twisting sheaf is the restriction of the new twisting
sheaf, for every integer twist. -/
def relativeProjBaseChangeChartPullbackTwistingSheafIso (i : BaseChangeChart f)
    (hA : A.obj.IsGeneratedInDegreeOne) :
    (Scheme.Modules.pullback ((B).relativeProjCover.f i.source ≫ A.relativeProjBaseChange f)).obj
      (A.obj.relativeProjTwistingSheaf n) ≅
    (Scheme.Modules.pullback ((B).relativeProjCover.f i.source)).obj
      ((B).relativeProjTwistingSheaf n) := by
  let c := A.relativeProjBaseChangeChartMap f i.le
  let j := A.obj.relativeProjCover.f i.target
  let h := A.relativeProjCover_f_relativeProjBaseChange f i.source i.target i.le
  let l := Proj.pullbackTwistingSheafIso (A.pullbackGradedSectionsGradedHom f i.le)
    (A.irrelevant_le_map_pullbackGradedSectionsGradedHom f i.le
      i.target.property i.source.property) Subtype.val Subtype.property
    (Proj.iSup_basicOpen_eq_top_of_adjoin_eq_top _
      (CommMon.isGeneratedInDegreeOne_iff.mp hA i.target.toOpens i.target.property)) n
  let j' := (B).relativeProjCover.f i.source
  let e := (Scheme.Modules.restrictFunctorIsoPullback j).symm.app
    (A.obj.relativeProjTwistingSheaf n) ≪≫ A.obj.restrictRelativeProjTwistingSheafIso n i.target
  let e' := (Scheme.Modules.restrictFunctorIsoPullback j').symm.app
    ((B).relativeProjTwistingSheaf n) ≪≫ (B).restrictRelativeProjTwistingSheafIso n i.source
  exact (Scheme.Modules.pullbackCongr h).app _ ≪≫
    (Scheme.Modules.pullbackComp c j).symm.app _ ≪≫
    (Scheme.Modules.pullback c).mapIso e ≪≫ l ≪≫ e'.symm

end TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra
