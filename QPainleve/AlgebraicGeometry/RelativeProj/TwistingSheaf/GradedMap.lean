/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.Evaluation
public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf.Map

import TauCeti.AlgebraicGeometry.Modules.Pushforward.Basic

/-!
# Naturality of relative projective evaluation

A graded algebra morphism compatible with the irrelevant ideals gives a
pullback on relative Proj that sends the twisting section of a homogeneous
element to the twisting section of its image. In degree one this compares
the tautological evaluations on the two projective spectra.

See [Stacks Project, Lemma 27.16.11](https://stacks.math.columbia.edu/tag/01O4).
-/

public section

open AlgebraicGeometry CategoryTheory Limits Opposite
open TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace CategoryTheory.CommMon

variable {X : Scheme.{u}} {A B : CommMon (GradedObject ℕ X.Modules)}
  [∀ n, (A.X n).IsQuasicoherent] [∀ n, (B.X n).IsQuasicoherent] (φ : B ⟶ A)
  (hφ : ∀ U : X.Opens, IsAffineOpen U →
    HomogeneousIdeal.irrelevant (A.gradedSectionsGrading U) ≤
      (HomogeneousIdeal.irrelevant (B.gradedSectionsGrading U)).map
        (gradedSectionsGradedHom φ U))

local notation "g" => relativeProjMap φ hφ
local notation "q" => B.relativeProjToBase
local notation "p" => A.relativeProjToBase
local notation "over_eq" => relativeProjMap_relativeProjToBase φ hφ
local notation "T[" A "," n "]" => relativeProjTwistingSheaf A n
local notation "σ[" A "," h "]" => relativeProjToTwistingSheaf A h
local notation "τ[" n "]" =>
  Adjunction.homEquiv (pullbackPushforwardAdjunction (relativeProjMap φ hφ)) _ _
    (relativeProjTwistingSheafMap φ hφ n)
local macro "π[" A:term "," n:term "," U:term "]" : term =>
  `((relativeProjTwistingSheafGlueData $A $n).π $U)
local macro "j[" A:term "," U:term "]" : term =>
  `(colimit.ι (relativeProjGluingData $A).functor $U)

private theorem relativeProjToTwistingSheaf_naturality_affine {d : ℕ} {n : ℤ} (hd : (d : ℤ) = n)
    (U : X.AffineZariskiSite) (s : Γ(B.X d, U.toOpens)) :
    (((pushforward q).map τ[n] ≫ (pushforwardComp g q).hom.app T[A,n] ≫
      (pushforwardCongr over_eq).hom.app T[A,n]).app U.toOpens)
      ((σ[B,hd]).app U.toOpens s) =
    (σ[A,hd]).app U.toOpens ((φ.hom.hom d).app U.toOpens s) := by
  let W := p ⁻¹ᵁ U.toOpens
  let W' := q ⁻¹ᵁ U.toOpens
  have hle : W ≤ (j[A,U]).opensRange := (A.relativeProjToBase_preimage U).le
  apply ((A.relativeProjTwistingSheafGlueData n).bijective_π_app
    (A.bijective_relativeProjTwistingSheafGlueData_map_app n) hle).injective
  rw [pushforward_composite_app]
  let hW : W = g ⁻¹ᵁ W' :=
    (congrArg (fun f ↦ f ⁻¹ᵁ U.toOpens) over_eq).symm.trans (Scheme.Hom.comp_preimage _ _ _)
  have hnat := (π[A,n,U]).naturality_apply (eqToHom hW)
    ((τ[n]).app W' ((σ[B,hd]).app U.toOpens s))
  refine hnat.trans ?_
  let t := (σ[B,hd]).app U.toOpens s
  let H := relativeProjTwistingSheafMapChart φ hφ n U
  have hchart :
      (π[A,n,U]).app (g ⁻¹ᵁ W') ((τ[n]).app W' t) =
        H.app W' ((π[B,n,U]).app W' t) :=
    congr($(homEquiv_relativeProjTwistingSheafMap_comp_π φ hφ n U).app W' t)
  let restrict := (((pushforward (j[A,U])).obj
    ((A.relativeProjTwistingSheafGlueData n).obj U)).presheaf.map (eqToHom hW).op)
  refine (congrArg (fun x ↦ restrict x) hchart).trans ?_
  have hB := B.π_app_relativeProjToTwistingSheaf_app hd U s
  have hA := A.π_app_relativeProjToTwistingSheaf_app hd U ((φ.hom.hom d).app U.toOpens s)
  refine (congrArg (fun x ↦ restrict (H.app W' x)) hB).trans (_root_.Eq.trans ?_ hA.symm)
  let chartMap := gradedSectionsGradedHom φ U.toOpens
  let x : B.gradedSectionsGrading U.toOpens d :=
    ⟨DirectSum.of _ d s, B.of_mem_gradedSectionsGrading d s⟩
  let V := (j[B,U]) ⁻¹ᵁ W'
  have hψ := relativeProjTwistingSheafMapChart_app_apply φ hφ n U W'
    (Proj.toTwistingSheaf _ hd V x)
  refine (congrArg (fun y ↦ restrict y) hψ).trans ?_
  have himage := Proj.twistingSheafMap_app_toTwistingSheaf chartMap (hφ U.toOpens U.property)
    (n := n) V hd x
  -- Both remaining maps restrict the section of the mapped homogeneous element.
  let k₁ := eqToHom (congrArg (· ⁻¹ᵁ W') (ι_relativeProjMap φ hφ U))
  let k₂ := homOfLE ((j[A,U]).preimage_mono hW.le)
  let y : A.gradedSectionsGrading U.toOpens d := ⟨chartMap x, Graded.map_mem chartMap x.property⟩
  have hres := Proj.res_toTwistingSheaf (𝒜 := A.gradedSectionsGrading U.toOpens) hd k₁ y
  have hres' := Proj.res_toTwistingSheaf (𝒜 := A.gradedSectionsGrading U.toOpens) hd k₂ y
  refine (congrArg (fun z ↦ restrict
    ((Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n).presheaf.map k₁.op z))
    himage).trans ((congrArg (fun z ↦ restrict z) hres).trans (hres'.trans ?_))
  have hy : y = ⟨DirectSum.of _ d ((φ.hom.hom d).app U.toOpens s),
      A.of_mem_gradedSectionsGrading d _⟩ := Subtype.ext (by simp [y, chartMap, x])
  exact congrArg (Proj.toTwistingSheaf _ hd ((j[A,U]) ⁻¹ᵁ W)) hy

/-- The degree-`d` map to the pushforward of the twist is natural under graded
algebra maps which induce a morphism of relative projective spectra. -/
theorem relativeProjToTwistingSheaf_naturality {d : ℕ} {n : ℤ} (hd : (d : ℤ) = n) :
    σ[B,hd] ≫ (pushforward q).map τ[n] ≫ (pushforwardComp g q).hom.app T[A,n] ≫
      (pushforwardCongr over_eq).hom.app T[A,n] =
    φ.hom.hom d ≫ σ[A,hd] := by
  let l : B.X d ⟶ (pushforward p).obj T[A,n] :=
    σ[B,hd] ≫ (pushforward q).map τ[n] ≫ (pushforwardComp g q).hom.app T[A,n] ≫
      (pushforwardCongr over_eq).hom.app T[A,n]
  let r : B.X d ⟶ (pushforward p).obj T[A,n] := φ.hom.hom d ≫ σ[A,hd]
  suffices l = r from this
  refine Scheme.Modules.hom_ext _ _ fun V ↦ ConcreteCategory.hom_ext _ _ fun s ↦ ?_
  refine Scheme.Modules.sections_ext_of_isAffineOpen fun U hU hUV ↦ ?_
  have h := relativeProjToTwistingSheaf_naturality_affine φ hφ hd ⟨U, hU⟩
    ((B.X d).presheaf.map (homOfLE hUV).op s)
  have hl : l.app U ((B.X d).presheaf.map (homOfLE hUV).op s) =
      r.app U ((B.X d).presheaf.map (homOfLE hUV).op s) := by
    dsimp only [l, r]
    erw [Hom.comp_app, ConcreteCategory.comp_apply, Hom.comp_app, ConcreteCategory.comp_apply]
    exact h
  exact (l.naturality_apply (homOfLE hUV) s).symm.trans
    (hl.trans (r.naturality_apply (homOfLE hUV) s))

/-- Pulling back the tautological evaluation along a relative Proj map and
comparing the twisting sheaves gives evaluation after the degree-one map. -/
theorem relativeProjEvaluation_naturality :
    (pullbackCongr over_eq).inv.app (B.X 1) ≫ (pullbackComp g q).inv.app (B.X 1) ≫
      (Scheme.Modules.pullback g).map B.relativeProjEvaluation ≫
        relativeProjTwistingSheafMap φ hφ 1 =
    (Scheme.Modules.pullback p).map (φ.hom.hom 1) ≫ A.relativeProjEvaluation := by
  apply ((pullbackPushforwardAdjunction p).homEquiv _ _).injective
  rw [homEquiv_pullbackComp_congr g q p over_eq]
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply]
  let a := pullbackPushforwardAdjunction g
  let b := pullbackPushforwardAdjunction q
  let c := pullbackPushforwardAdjunction p
  let f : B.X 1 ⟶ A.X 1 := φ.hom.hom 1
  let t := relativeProjTwistingSheafMap φ hφ 1
  have h₁ := a.homEquiv_naturality_left B.relativeProjEvaluation t
  have h₂ := b.homEquiv_naturality_right B.relativeProjEvaluation (τ[1])
  have h₃ := c.homEquiv_naturality_left f A.relativeProjEvaluation
  rw [h₁, h₂]
  refine Eq.trans ?_ h₃.symm
  dsimp only [b, c]
  erw [B.homEquiv_relativeProjEvaluation, A.homEquiv_relativeProjEvaluation, Category.assoc]
  exact relativeProjToTwistingSheaf_naturality φ hφ (d := 1) (n := 1) rfl

end CategoryTheory.CommMon
