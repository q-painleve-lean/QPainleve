/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.Evaluation
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.MorphismExt

import QPainleve.AlgebraicGeometry.Modules.Pullback.Composites
import TauCeti.AlgebraicGeometry.Sites.SmallAffineZariski

/-!
# Extensionality of morphisms to relative projective spectra

For a graded sheaf of algebras generated in degree one, maps to its relative
projective spectrum over a fixed base map are determined by the induced maps
on the first twisting sheaves. This applies on affine charts by the ordinary
projective-spectrum criterion. See the
[Stacks Project, Lemma 27.16.11](https://stacks.math.columbia.edu/tag/01O4).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TauCeti TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace CategoryTheory.CommMon

variable {X Y : Scheme.{u}} (A : CommMon (GradedObject ℕ X.Modules))
  [∀ n, (A.X n).IsQuasicoherent]

local notation "p" => (A.relativeProjToBase)
local notation "T" => A.relativeProjTwistingSheaf 1
local notation "a₁" => (A.X 1)
local notation "σ" => A.relativeProjToTwistingSheaf (Nat.cast_one : ((1 : ℕ) : ℤ) = 1)

variable {f : Y ⟶ X} (g : Y ⟶ A.relativeProj) (hg : g ≫ A.relativeProjToBase = f)

include hg

/-- The pullback of degree-one evaluation along a morphism to relative Proj,
viewed as a map from the pullback of the degree-one component along its base map. -/
def relativeProjEvaluationAlong :
    (pullback f).obj a₁ ⟶ (pullback g).obj T :=
  (pullbackCongr hg).inv.app a₁ ≫ (pullbackComp g p).inv.app a₁ ≫
    (pullback g).map A.relativeProjEvaluation

/-- Evaluation along a map uses the pullback comparison over the specified
base morphism and the pullback of the original evaluation. -/
theorem relativeProjEvaluationAlong_def :
    A.relativeProjEvaluationAlong g hg =
      (pullbackCongr hg).inv.app a₁ ≫ (pullbackComp g p).inv.app a₁ ≫
        (pullback g).map A.relativeProjEvaluation :=
  (rfl)

/-- Evaluation along a morphism sends a local degree-one section to the pullback of
its associated twisting section. -/
theorem relativeProjEvaluationAlong_app (U : X.Opens) (W : Y.Opens)
    (hW : W ≤ f ⁻¹ᵁ U) (s : Γ(a₁, U)) :
    (A.relativeProjEvaluationAlong g hg).app W (f.pullbackSectionsLE a₁ U W hW s) =
      g.pullbackSectionsLE T (p ⁻¹ᵁ U) W
        (by simpa only [← hg, Scheme.Hom.comp_preimage] using hW) ((σ).app U s) := by
  subst f
  simp only [relativeProjEvaluationAlong, pullbackCongr, eqToIso_refl, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Hom.comp_app, ConcreteCategory.comp_apply]
  erw [Scheme.Hom.pullbackSectionsLE_comp p a₁ U g (p ⁻¹ᵁ U) le_rfl
      (by simpa only [Scheme.Hom.comp_preimage] using hW),
    Scheme.Hom.pullbackSectionsLE_self, Scheme.Hom.pullbackSectionsLE_naturality]
  congr 1
  rw [← pullbackPushforwardAdjunction_homEquiv_app_apply, A.homEquiv_relativeProjEvaluation]

/-- Pulling back evaluation along a composite agrees with pulling back in two steps,
under the canonical pullback composition isomorphisms. -/
theorem relativeProjEvaluationAlong_comp {Z : Scheme.{u}} (i : Z ⟶ Y)
    {f' : Z ⟶ X} (hi : i ≫ f = f') :
    A.relativeProjEvaluationAlong (i ≫ g) (((Category.assoc i g p).trans
      (congrArg (i ≫ ·) hg)).trans hi) ≫ (pullbackComp i g).inv.app T =
      (pullbackCongr hi).inv.app a₁ ≫ (pullbackComp i f).inv.app a₁ ≫
        (pullback i).map (A.relativeProjEvaluationAlong g hg) := by
  subst f'
  subst f
  simp only [relativeProjEvaluationAlong, pullbackCongr, eqToIso_refl, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Category.assoc, Functor.map_comp]
  have hn := ((pullbackComp i g).inv.naturality A.relativeProjEvaluation).symm
  rw [Functor.comp_map] at hn
  rw [← hn, pullbackComp_inv_app_comp_pullback_map_pullbackComp_inv_app_assoc]
  rfl

omit hg in
private def chartTwistIso (U : X.AffineZariskiSite) :
    (pullback (A.relativeProjCover.f U)).obj T ≅ Proj.twistingSheaf
      (A.gradedSectionsGrading U.toOpens) 1 := by
  -- Use the adjoint of the gluing projection to read the degree-one sections on this chart.
  let j := A.relativeProjCover.f U
  let M := Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) 1
  let π : T ⟶ (pushforward j).obj M := (A.relativeProjTwistingSheafGlueData 1).π U
  let e := ((pullbackPushforwardAdjunction j).homEquiv T M).symm π
  have : IsIso e := isIso_pullbackPushforwardAdjunction_homEquiv_symm_of_bijective
    j T M π (fun V hV ↦ (A.relativeProjTwistingSheafGlueData 1).bijective_π_app
      (A.bijective_relativeProjTwistingSheafGlueData_map_app 1) hV)
  exact asIso e

omit hg in
private theorem top_le_chart_preimage (U : X.AffineZariskiSite) :
    ⊤ ≤ (A.relativeProjCover.f U) ⁻¹ᵁ (p ⁻¹ᵁ U.toOpens) :=
  (A.relativeProjToBase_preimage U).symm ▸
    (A.relativeProjCover.f U).preimage_opensRange.ge

omit hg in
private theorem chartTwistIso_app (U : X.AffineZariskiSite) (s : Γ(a₁, U.toOpens)) :
    let j := A.relativeProjCover.f U
    let V := p ⁻¹ᵁ U.toOpens
    (A.chartTwistIso U).hom.app ⊤
        (j.pullbackSectionsLE T V ⊤ (A.top_le_chart_preimage U) ((σ).app U.toOpens s)) =
      Proj.toTwistingSheaf (A.gradedSectionsGrading U.toOpens) Nat.cast_one ⊤
        ⟨DirectSum.of _ 1 s, A.of_mem_gradedSectionsGrading 1 s⟩ := by
  intro j V
  have hπ : (pullbackPushforwardAdjunction j).homEquiv _ _ (A.chartTwistIso U).hom =
      (A.relativeProjTwistingSheafGlueData 1).π U :=
    Equiv.apply_symm_apply _ _
  have h := A.π_app_relativeProjToTwistingSheaf_app Nat.cast_one U s
  let t : Γ(T, V) := (σ).app U.toOpens s
  have ht := pullbackPushforwardAdjunction_homEquiv_app_apply j (A.chartTwistIso U).hom V t
  rw [hπ] at ht
  have hres := ((A.chartTwistIso U).hom).mapPresheaf.naturality_apply
    (homOfLE (A.top_le_chart_preimage U)).op
    (j.pullbackSections T V ((σ).app U.toOpens s))
  have hstart := congrArg ((A.chartTwistIso U).hom.app ⊤)
    (j.pullbackSectionsLE_apply T V ⊤ (A.top_le_chart_preimage U) t)
  exact hstart.trans (hres.trans ((congrArg _ (ht.symm.trans h)).trans
    (Proj.res_toTwistingSheaf Nat.cast_one _ _)))

section Charts

variable (U : X.AffineZariskiSite)
local notation "P" => Proj (A.gradedSectionsGrading U.toOpens)
local notation "chartι" => (A.relativeProjCover.f U : P ⟶ A.relativeProj)
local notation "L" => Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) 1

omit hg in
private def chartPullbackIso {V : Y.Opens} (b : V.toScheme ⟶ P)
    (hb : b ≫ chartι = V.ι ≫ g) :
    (pullback V.ι).obj ((pullback g).obj T) ≅ (pullback b).obj L := by
  let e : (pullback V.ι).obj ((pullback g).obj T) ≅
      (pullback b).obj ((pullback chartι).obj T) :=
    pullbackCompIsoOfEq (f := V.ι) (g := g) (i := b) (j := chartι) hb.symm T
  exact e.trans ((pullback b).mapIso (A.chartTwistIso U))

private theorem chartPullbackIso_app {V : Y.Opens} (b : V.toScheme ⟶ P)
    (hb : b ≫ chartι = V.ι ≫ g) (hV : V ≤ f ⁻¹ᵁ U.toOpens) (s : Γ(a₁, U.toOpens)) :
    let x := f.pullbackSectionsLE a₁ U.toOpens V hV s
    (A.chartPullbackIso g U b hb).hom.app ⊤
      (V.ι.pullbackSectionsLE ((pullback g).obj T) V ⊤ (by simp)
        ((A.relativeProjEvaluationAlong g hg).app V x)) =
      b.pullbackSectionsLE L ⊤ ⊤ b.preimage_top.ge
        (Proj.toTwistingSheaf (A.gradedSectionsGrading U.toOpens) Nat.cast_one ⊤
          ⟨DirectSum.of _ 1 s, A.of_mem_gradedSectionsGrading 1 s⟩) := by
  intro x
  let pullSection := V.ι.pullbackSectionsLE ((pullback g).obj T) V ⊤ V.ι_preimage_self.ge
  let twist := A.chartTwistIso U
  let compare := pullbackCompIsoOfEq (f := V.ι) (g := g) (i := b) (j := chartι) hb.symm T
  let finish := ((pullback b).map twist.hom).app ⊤
  have hgV : V ≤ g ⁻¹ᵁ (p ⁻¹ᵁ U.toOpens) := by
    simpa only [← hg, Scheme.Hom.comp_preimage] using hV
  let t : Γ(T, p ⁻¹ᵁ U.toOpens) := (σ).app U.toOpens s
  have heval : (A.relativeProjEvaluationAlong g hg).app V x =
      g.pullbackSectionsLE T (p ⁻¹ᵁ U.toOpens) V hgV t :=
    A.relativeProjEvaluationAlong_app g hg U.toOpens V hV s
  have hcomp := pullbackCompIsoOfEq_hom_app_pullbackSectionsLE
    (f := V.ι) (g := g) (i := b) (j := chartι) hb.symm T
    hgV (A.top_le_chart_preimage U) V.ι_preimage_self.ge b.preimage_top.ge t
  have hfinish := b.pullbackSectionsLE_naturality _ ⊤ ⊤ b.preimage_top.ge twist.hom
    ((chartι).pullbackSectionsLE T (p ⁻¹ᵁ U.toOpens) ⊤ (A.top_le_chart_preimage U) t)
  have h := (congrArg (fun z ↦ finish (compare.hom.app ⊤ (pullSection z))) heval).trans
    ((congrArg finish hcomp).trans (hfinish.trans
      (congrArg (b.pullbackSectionsLE L ⊤ ⊤ b.preimage_top.ge) (A.chartTwistIso_app U s))))
  have hc : (A.chartPullbackIso g U b hb).hom.app ⊤ = compare.hom.app ⊤ ≫ finish :=
    Hom.comp_app _ _
  exact (congrArg (fun k ↦ k (pullSection ((A.relativeProjEvaluationAlong g hg).app V x)))
    hc).trans h

end Charts

/-- Two morphisms over the same base map are equal if an isomorphism of their
pulled-back first twists intertwines the degree-one evaluations. -/
theorem relativeProj_hom_ext_of_evaluation (hgen : A.IsGeneratedInDegreeOne)
    {h : Y ⟶ A.relativeProj} (hh : h ≫ p = f)
    (e : (pullback g).obj T ≅ (pullback h).obj T)
    (he : A.relativeProjEvaluationAlong g hg ≫ e.hom = A.relativeProjEvaluationAlong h hh) :
    g = h := by
  let V (U : X.AffineZariskiSite) := f ⁻¹ᵁ U.toOpens
  have hcover : IsOpenCover V := (Scheme.AffineZariskiSite.isOpenCover_toOpens X).comap f.base.hom'
  refine (Y.openCoverOfIsOpenCover V hcover).hom_ext _ _ fun U ↦ ?_
  let j := A.relativeProjCover.f U
  let v := (V U).ι
  let q := (f ∣_ U.toOpens)
  let H := A.isPullback_relativeProjCover U
  have hbase : q ≫ U.toOpens.ι = v ≫ f := morphismRestrict_ι f _
  let g' := H.lift q (v ≫ g) (by rw [hbase, Category.assoc, hg])
  let h' := H.lift q (v ≫ h) (by rw [hbase, Category.assoc, hh])
  have hg' : g' ≫ j = v ≫ g := H.lift_snd ..
  have hh' : h' ≫ j = v ≫ h := H.lift_snd ..
  suffices H' : g' = h' by exact hg'.symm.trans (H' ▸ hh')
  let i := A.chartPullbackIso g U g' hg'
  let k := A.chartPullbackIso h U h' hh'
  let i' := (pullback v).mapIso e
  apply Proj.hom_ext_of_pullback_toTwistingSheaf
    (CommMon.isGeneratedInDegreeOne_iff.mp hgen U.toOpens U.property)
    (i.symm ≪≫ i' ≪≫ k)
  intro a
  obtain ⟨s, hs⟩ := DirectSum.mem_summand.mp a.property
  have ha : a = ⟨DirectSum.of _ 1 s, A.of_mem_gradedSectionsGrading 1 s⟩ :=
    Subtype.ext hs.symm
  -- Work with the three chart comparisons as isomorphisms of modules on the source open.
  let x := f.pullbackSectionsLE a₁ U.toOpens (V U) le_rfl s
  let I := v.pullbackSectionsLE ((pullback g).obj T) (V U) ⊤ (V U).ι_preimage_self.ge
  let K := v.pullbackSectionsLE ((pullback h).obj T) (V U) ⊤ (V U).ι_preimage_self.ge
  have hgh : e.hom.app (V U) ((A.relativeProjEvaluationAlong g hg).app (V U) x) =
      (A.relativeProjEvaluationAlong h hh).app (V U) x :=
    congr($(he).app (V U) x)
  have hx : i'.hom.app ⊤ (I ((A.relativeProjEvaluationAlong g hg).app (V U) x)) =
      K ((A.relativeProjEvaluationAlong h hh).app (V U) x) :=
    (v.pullbackSectionsLE_naturality _ _ _ _ e.hom _).trans (congrArg K hgh)
  have hI := A.chartPullbackIso_app g hg U g' hg' le_rfl s
  have hK := A.chartPullbackIso_app h hh U h' hh' le_rfl s
  have hi : i.inv.app ⊤ (i.hom.app ⊤ (I ((A.relativeProjEvaluationAlong g hg).app (V U) x))) =
      I ((A.relativeProjEvaluationAlong g hg).app (V U) x) :=
    congr($(i.hom_inv_id).app ⊤ (I ((A.relativeProjEvaluationAlong g hg).app (V U) x)))
  have hfinal := (congrArg (fun z ↦ k.hom.app ⊤ (i'.hom.app ⊤ (i.inv.app ⊤ z))) hI.symm).trans
    ((congrArg (fun z ↦ k.hom.app ⊤ (i'.hom.app ⊤ z)) hi).trans
      ((congrArg (k.hom.app ⊤) hx).trans hK))
  simpa only [ha, Iso.trans_hom, Iso.symm_hom, Hom.comp_app, ConcreteCategory.comp_apply]
    using hfinal

end CategoryTheory.CommMon
