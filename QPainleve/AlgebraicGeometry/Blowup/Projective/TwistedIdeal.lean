/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Projective.Graph
public import TauCeti.AlgebraicGeometry.IdealSheaf.Module
public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
import QPainleve.AlgebraicGeometry.LineBundle.Frame
import QPainleve.AlgebraicGeometry.Modules.Generators
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.GlobalSections
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Projective presentations from a twisted center ideal

Global generators of an ideal sheaf tensored with a line bundle define a projective
presentation of the blowup. In each frame of the line bundle the generators become
an indexed family of ordinary ideal generators. Changes of frame act by a common
unit, so the affine Rees presentations agree off the center and hence on their
scheme-theoretically dense overlaps.

See [The Stacks Project, Section 31.33](https://stacks.math.columbia.edu/tag/01OF).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)
  {R : Type u} [CommRing R] (f : X ⟶ Spec (.of R)) {ι : Type u}

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R
local notation "ℙ" => Proj 𝒜

private theorem comp_blowupChartToProjectiveSpace_eq_eval {T : Scheme.{u}} [IsAffine T]
    {U : X.Opens} (hU : IsAffineOpen U)
    (a : ι → I.ideal ⟨U, hU⟩)
    (ha : Ideal.span (Set.range fun j ↦ (a j : Γ(X, U))) = I.ideal ⟨U, hU⟩)
    (t : T ⟶ Proj (reesAlgebra.grade (I.ideal ⟨U, hU⟩))) (p : T ⟶ X)
    (hp : t ≫ I.blowupChart hU ≫ I.blowupToBase = p)
    (h : (⊤ : T.Opens) ≤ p ⁻¹ᵁ U) (hI : I.comap p = ⊤) :
    let b := (p.appLE U ⊤ h).hom
    let v := MvPolynomial.eval₂Hom (Spec.preimage (T.isoSpec.inv ≫ p ≫ f)).hom
      (fun j ↦ b (a j))
    ∃ hv : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map v = ⊤,
      t ≫ I.blowupChartToProjectiveSpace f hU a ha = Proj.fromOfGlobalSections 𝒜 v hv := by
  let b := (p.appLE U ⊤ h).hom
  have hspec : Spec.map (CommRingCat.ofHom b) ≫ hU.fromSpec = T.isoSpec.inv ≫ p := by
    have hs := IsAffineOpen.SpecMap_appLE_fromSpec p hU (isAffineOpen_top T) h
    rw [IsAffineOpen.fromSpec_top] at hs
    exact hs
  have ht : t ≫ Proj.toSpecCoeff (reesAlgebra.grade (I.ideal ⟨U, hU⟩)) =
      T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom b) := by
    apply (cancel_mono hU.fromSpec).mp
    rw [Category.assoc, ← I.blowupChart_blowupToBase, hp, Category.assoc, hspec,
      ← T.isoSpec_hom, Iso.hom_inv_id_assoc]
  have hc : b.comp (Spec.preimage (hU.fromSpec ≫ f)).hom =
      (Spec.preimage (T.isoSpec.inv ≫ p ≫ f)).hom := by
    have eq : Spec.preimage (hU.fromSpec ≫ f) ≫ p.appLE U ⊤ h =
        Spec.preimage (T.isoSpec.inv ≫ p ≫ f) := by
      apply Spec.map_injective
      calc
        Spec.map (Spec.preimage (hU.fromSpec ≫ f) ≫ p.appLE U ⊤ h) =
            Spec.map (p.appLE U ⊤ h) ≫ hU.fromSpec ≫ f := by
          rw [Spec.map_comp, Spec.map_preimage]
        _ = T.isoSpec.inv ≫ p ≫ f := by
          rw [← Category.assoc]
          exact congrArg (· ≫ f) hspec
        _ = Spec.map (Spec.preimage (T.isoSpec.inv ≫ p ≫ f)) := (Spec.map_preimage _).symm
    exact congrArg CommRingCat.Hom.hom eq
  have hb : (I.ideal ⟨U, hU⟩).map b = ⊤ := by
    dsimp only [b]
    rw [← I.ideal_comap_of_le p ⟨U, hU⟩ ⟨⊤, isAffineOpen_top T⟩ h, hI,
      ideal_top, Pi.top_apply]
  obtain ⟨hv, he⟩ := I.comp_blowupChartToProjectiveSpace_eq_fromOfGlobalSections
    f hU a ha b hb t ht
  dsimp only
  rw [← hc]
  exact ⟨hv, he⟩

private theorem frameCoordinates_span {L : X.Modules} [L.IsQuasicoherent]
    (G : (I.sheaf ⊗ L).GeneratingSections) {U : X.Opens} (hU : IsAffineOpen U)
    (e : Γ(L, U)) (a : G.I → Γ(I.sheaf, U))
    (hb : Function.Bijective (Scheme.Modules.tmulRight I.sheaf e))
    (ha : ∀ i, Scheme.Modules.tmulRight I.sheaf e (a i) =
      (I.sheaf ⊗ L).presheaf.map U.leTop.op ((I.sheaf ⊗ L).sectionsEquivTop (G.s i))) :
    Ideal.span (α := Γ(X, U)) (Set.range fun i ↦ I.sheafι.app U (a i)) = I.ideal ⟨U, hU⟩ := by
  have hspan := G.span_restrict_eq_top_of_isAffineOpen hU
  simp_rw [← ha] at hspan
  have htop : Submodule.span Γ(X, U) (Set.range a) = ⊤ := by
    apply Submodule.map_injective_of_injective hb.injective
    rw [Submodule.map_span, ← Set.range_comp, Function.comp_def, hspan,
      Submodule.map_top, LinearMap.range_eq_top.mpr hb.surjective]
  apply SetLike.coe_injective
  let ιU : Γ(I.sheaf, U) →ₗ[Γ(X, U)] Γ(X, U) :=
    ((Scheme.Modules.sectionsFunctor U).map I.sheafι).hom
  have h := congrArg (Submodule.map ιU) htop
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top] at h
  exact (congrArg SetLike.coe h).trans
    ((I.range_sheafι_app U).trans (congrArg SetLike.coe (I.sections_eq_ideal ⟨U, hU⟩)))

private theorem map_frameCoordinates_eq_unit_smul {L : X.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L]
    {U V : X.Opens} (e : Γ(L, U)) (e' : Γ(L, V))
    (he : U ≤ L.nonvanishingLocus e) (he' : V ≤ L.nonvanishingLocus e')
    (a : ι → Γ(I.sheaf, U)) (a' : ι → Γ(I.sheaf, V))
    (s : ι → Γ(I.sheaf ⊗ L, ⊤))
    (ha : ∀ i, Scheme.Modules.tmulRight I.sheaf e (a i) =
      (I.sheaf ⊗ L).presheaf.map U.leTop.op (s i))
    (ha' : ∀ i, Scheme.Modules.tmulRight I.sheaf e' (a' i) =
      (I.sheaf ⊗ L).presheaf.map V.leTop.op (s i)) :
    let i : U ⊓ V ⟶ U := homOfLE inf_le_left
    let j : U ⊓ V ⟶ V := homOfLE inf_le_right
    ∃ c : Γ(X, U ⊓ V)ˣ, ∀ k,
      X.presheaf.map i.op (I.sheafι.app U (a k)) =
        c * X.presheaf.map j.op (I.sheafι.app V (a' k)) := by
  intro i j
  let u := L.presheaf.map i.op e
  let v := L.presheaf.map j.op e'
  have hu : U ⊓ V ≤ L.nonvanishingLocus u := by
    rw [Scheme.Modules.nonvanishingLocus_map]
    exact le_inf le_rfl (inf_le_left.trans he)
  have hv : U ⊓ V ≤ L.nonvanishingLocus v := by
    rw [Scheme.Modules.nonvanishingLocus_map]
    exact le_inf le_rfl (inf_le_right.trans he')
  obtain ⟨c, hc⟩ := L.isUnit_sectionRatio v u hv hu
  have heq : (c : Γ(X, U ⊓ V)) • u = v := by
    rw [hc, Scheme.Modules.sectionRatio_smul]
  refine ⟨c, fun k ↦ ?_⟩
  have hres (W : X.Opens) (d : U ⊓ V ⟶ W) :
      (I.sheaf ⊗ L).presheaf.map d.op
        ((I.sheaf ⊗ L).presheaf.map W.leTop.op (s k)) =
      (I.sheaf ⊗ L).presheaf.map (U ⊓ V).leTop.op (s k) := by
    simp only [← Functor.map_comp_apply, ← op_comp]
    rfl
  have h₁ := congrArg ((I.sheaf ⊗ L).presheaf.map i.op ·) (ha k)
  have h₂ := congrArg ((I.sheaf ⊗ L).presheaf.map j.op ·) (ha' k)
  rw [Scheme.Modules.map_tmulRight, hres U i] at h₁
  rw [Scheme.Modules.map_tmulRight, hres V j] at h₂
  have ha'' : Scheme.Modules.tmulRight I.sheaf u (I.sheaf.presheaf.map i.op (a k)) =
      Scheme.Modules.tmulRight I.sheaf v (I.sheaf.presheaf.map j.op (a' k)) :=
    h₁.trans h₂.symm
  rw [← heq, Scheme.Modules.tmulRight_smul, ← LinearMap.map_smul] at ha''
  have hb := Scheme.Modules.bijective_tmulRight_of_le_nonvanishingLocus I.sheaf u hu
  have h' := hb.injective ha''
  rw [← I.sheafι_app_map, ← I.sheafι_app_map, h']
  exact Scheme.Modules.Hom.app_smul I.sheafι _ _

private theorem comp_blowupChartsToProjectiveSpace_eq_of_rescaling {T : Scheme.{u}} [IsAffine T]
    {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (a : ι → I.ideal ⟨U, hU⟩) (a' : ι → I.ideal ⟨V, hV⟩)
    (ha : Ideal.span (Set.range fun k ↦ (a k : Γ(X, U))) = I.ideal ⟨U, hU⟩)
    (ha' : Ideal.span (Set.range fun k ↦ (a' k : Γ(X, V))) = I.ideal ⟨V, hV⟩)
    (t : T ⟶ Proj (reesAlgebra.grade (I.ideal ⟨U, hU⟩)))
    (t' : T ⟶ Proj (reesAlgebra.grade (I.ideal ⟨V, hV⟩))) (p : T ⟶ X)
    (hp : t ≫ I.blowupChart hU ≫ I.blowupToBase = p)
    (hp' : t' ≫ I.blowupChart hV ≫ I.blowupToBase = p)
    (hI : I.comap p = ⊤) (c : Γ(X, U ⊓ V)ˣ) (hc : ∀ k,
      X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op (a k : Γ(X, U)) =
        c * X.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op (a' k : Γ(X, V))) :
    t ≫ I.blowupChartToProjectiveSpace f hU a ha =
      t' ≫ I.blowupChartToProjectiveSpace f hV a' ha' := by
  have hpre {W : X.Opens} (hW : IsAffineOpen W)
      (z : T ⟶ Proj (reesAlgebra.grade (I.ideal ⟨W, hW⟩))) :
      (⊤ : T.Opens) ≤ (z ≫ I.blowupChart hW ≫ I.blowupToBase) ⁻¹ᵁ W := by
    rw [Scheme.Hom.comp_preimage z, Scheme.Hom.comp_preimage (I.blowupChart hW),
      ← I.opensRange_blowupChart hW, Scheme.Hom.preimage_opensRange]
    simp
  have hU' : (⊤ : T.Opens) ≤ p ⁻¹ᵁ U := hp ▸ hpre hU t
  have hV' : (⊤ : T.Opens) ≤ p ⁻¹ᵁ V := hp' ▸ hpre hV t'
  obtain ⟨h₁, H₁⟩ := I.comp_blowupChartToProjectiveSpace_eq_eval f hU a ha t p hp hU' hI
  obtain ⟨h₂, H₂⟩ := I.comp_blowupChartToProjectiveSpace_eq_eval f hV a' ha' t' p hp' hV' hI
  refine H₁.trans (Eq.trans ?_ H₂.symm)
  have hW : (⊤ : T.Opens) ≤ p ⁻¹ᵁ (U ⊓ V) := fun x hx ↦ ⟨hU' hx, hV' hx⟩
  let b := p.appLE (U ⊓ V) ⊤ hW
  symm
  apply Proj.fromOfGlobalSections_eq_of_X_unit_rescaling _ _ (c.map b.hom.toMonoidHom)
  · exact RingHom.ext fun r ↦ by simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
  · intro i
    simp only [MvPolynomial.eval₂Hom_X', Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass]
    have hleft := p.map_appLE hW (homOfLE inf_le_left : U ⊓ V ⟶ U).op
    have hright := p.map_appLE hW (homOfLE inf_le_right : U ⊓ V ⟶ V).op
    have ht := congrArg b (hc i)
    rw [map_mul, ← CommRingCat.comp_apply, hleft, ← CommRingCat.comp_apply, hright] at ht
    exact ht

private theorem compatible_blowupChartToProjectiveSpace_of_rescaling {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (a : ι → I.ideal ⟨U, hU⟩) (a' : ι → I.ideal ⟨V, hV⟩)
    (ha : Ideal.span (Set.range fun k ↦ (a k : Γ(X, U))) = I.ideal ⟨U, hU⟩)
    (ha' : Ideal.span (Set.range fun k ↦ (a' k : Γ(X, V))) = I.ideal ⟨V, hV⟩)
    (c : Γ(X, U ⊓ V)ˣ) (hc : ∀ k,
      X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op (a k : Γ(X, U)) =
        c * X.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op (a' k : Γ(X, V))) :
    pullback.fst (I.blowupChart hU) (I.blowupChart hV) ≫
      I.blowupChartToProjectiveSpace f hU a ha =
    pullback.snd (I.blowupChart hU) (I.blowupChart hV) ≫
      I.blowupChartToProjectiveSpace f hV a' ha' := by
  refine I.eq_on_blowupChart_overlap f hU hV
    (I.blowupChartToProjectiveSpace_toSpecCoeff f hU a ha)
    (I.blowupChartToProjectiveSpace_toSpecCoeff f hV a' ha') ?_
  let cU := I.blowupChart hU
  let cV := I.blowupChart hV
  let k := pullback.fst cU cV ≫ cU
  let e := Scheme.Opens.ι (I.comap I.blowupToBase).support.compl
  let 𝒰 := (pullback e k).affineCover
  refine 𝒰.hom_ext _ _ fun j ↦ ?_
  let T := 𝒰.X j
  let l := 𝒰.f j
  let t := l ≫ pullback.snd e k ≫ pullback.fst cU cV
  let t' := l ≫ pullback.snd e k ≫ pullback.snd cU cV
  let p := (l ≫ pullback.fst e k) ≫ e ≫ I.blowupToBase
  have hp : t ≫ cU ≫ I.blowupToBase = p := by
    simp only [p, t, k, Category.assoc, pullback.condition_assoc]
  have hp' : t' ≫ cV ≫ I.blowupToBase = p := by
    rw [← hp]
    simp only [t, t', Category.assoc, pullback.condition_assoc]
  have h : (I.comap I.blowupToBase).comap e = ⊤ := by
    rw [Scheme.IdealSheafData.comap_eq_top_iff]
    have he := Scheme.Opens.opensRange_ι (I.comap I.blowupToBase).support.compl
    exact (congrArg (e ⁻¹ᵁ ·) he.symm).trans e.preimage_opensRange
  have hI : I.comap p = ⊤ := by
    dsimp only [p]
    rw [I.comap_comp (l ≫ pullback.fst e k), I.comap_comp e, h, comap_top]
  have H := I.comp_blowupChartsToProjectiveSpace_eq_of_rescaling
    f hU hV a a' ha ha' t t' p hp hp' hI c hc
  simpa only [t, t', Category.assoc] using H

/-- Global generators of an ideal sheaf twisted by an invertible sheaf give a morphism
of its blowup to projective space whose graph over the original scheme is closed. -/
theorem exists_blowupToProjectiveSpace_of_generatingSections (L : InvertibleSheaf X)
    (G : (I.sheaf ⊗ L.obj).GeneratingSections) :
    ∃ (m : I.blowup ⟶ Proj (MvPolynomial.homogeneousSubmodule G.I R))
      (hm : m ≫ Proj.toSpecCoeff _ = I.blowupToBase ≫ f),
      IsClosedImmersion (pullback.lift I.blowupToBase m hm.symm) := by
  classical
  have h (x : X) : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∃ e : Γ(L.obj, U), U ≤ L.obj.nonvanishingLocus e := by
    obtain ⟨V, t, hx⟩ := L.obj.exists_mem_trivialization x
    obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hx
    let j : U ⟶ V := homOfLE (show U ≤ V from hUV)
    refine ⟨U, hU, hxU, L.obj.presheaf.map j.op
      (L.obj.trivializationGenerator t), ?_⟩
    rw [Scheme.Modules.nonvanishingLocus_map,
      Scheme.Modules.nonvanishingLocus_trivializationGenerator]
    exact le_inf le_rfl hUV
  choose U hU hx e he using h
  let s (i : G.I) := (I.sheaf ⊗ L.obj).sectionsEquivTop (G.s i)
  have hb (x : X) := Scheme.Modules.bijective_tmulRight_of_le_nonvanishingLocus I.sheaf (e x) (he x)
  choose a ha using fun (x : X) (i : G.I) ↦
    (hb x).surjective ((I.sheaf ⊗ L.obj).presheaf.map (U x).leTop.op (s i))
  let b (x : X) (i : G.I) : I.ideal ⟨U x, hU x⟩ :=
    ⟨I.sheafι.app (U x) (a x i), I.sections_eq_ideal ⟨U x, hU x⟩ ▸
      I.sheafι_app_mem (U x) (a x i)⟩
  have hgen (x : X) : Ideal.span (Set.range fun i ↦ (b x i : Γ(X, U x))) =
      I.ideal ⟨U x, hU x⟩ :=
    I.frameCoordinates_span G (hU x) (e x) (a x) (hb x) (ha x)
  have hcover : ⨆ x : X, U x = ⊤ := top_unique fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩
  obtain ⟨m, hm, hclosed, _⟩ := I.exists_blowupToProjectiveSpace_of_compatible
    f U hU hcover b hgen (fun x y ↦ by
      obtain ⟨c, hc⟩ := I.map_frameCoordinates_eq_unit_smul (e x) (e y) (he x) (he y)
        (a x) (a y) s (ha x) (ha y)
      exact I.compatible_blowupChartToProjectiveSpace_of_rescaling f (hU x) (hU y)
        (b x) (b y) (hgen x) (hgen y) c hc)
  exact ⟨m, hm, hclosed⟩

end AlgebraicGeometry.Scheme.IdealSheafData
