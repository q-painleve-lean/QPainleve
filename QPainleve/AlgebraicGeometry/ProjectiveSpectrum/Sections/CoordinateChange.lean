/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.TwistingSheaf

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Sections
import QPainleve.AlgebraicGeometry.LineBundle.Pullback

/-!
# Changes of homogeneous coordinates for maps from sections

The pullback of the tautological sections characterizes the morphism to polynomial
projective space. This gives the coordinate-change formula on overlaps when gluing
maps into a projective bundle. The characterization uses standard opens and ratios
of sections as in the Stacks Project, [Lemma 27.13.1](https://stacks.math.columbia.edu/tag/01NE).
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace HomogeneousLocalization
open TauCeti.AlgebraicGeometry TauCeti.MvPolynomial

universe u

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R ι : Type u} [CommRing R] {X : Scheme.{u}} {M : X.Modules}
  [SheafOfModules.isInvertible X M]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R
local notation "ℙ" => Proj 𝒜
local notation "T" => Proj.twistingSheaf 𝒜 1
local notation "U[" i "]" => Proj.basicOpen 𝒜 (MvPolynomial.X i)
local notation "B[" i "]" => Away 𝒜 (MvPolynomial.X i)
local notation "coord" => Proj.polynomialCoordinateSection (R := R) (ι := ι)

private theorem coordinate_mem (i : ι) : MvPolynomial.X i ∈ 𝒜 1 :=
  (MvPolynomial.mem_homogeneousSubmodule ..).mpr (MvPolynomial.isHomogeneous_X R i)

private theorem preimage_coordinateOpen_of_pullback (g : X ⟶ ℙ) (s : ι → Γ(M, ⊤))
    (e : (pullback g).obj T ≅ M)
    (hs : ∀ i, e.hom.app ⊤ (g.pullbackSectionsLE T ⊤ ⊤ g.preimage_top.ge (coord i)) = s i)
    (i : ι) :
    g ⁻¹ᵁ U[i] = M.nonvanishingLocus (s i) := by
  rw [← hs i, nonvanishingLocus_hom_app, nonvanishingLocus_pullbackSectionsLE,
    Proj.nonvanishingLocus_polynomialCoordinateSection, top_inf_eq]

omit [SheafOfModules.isInvertible X M] in
private theorem appLE_awayXRatio_smul_of_pullback (g : X ⟶ ℙ) (s : ι → Γ(M, ⊤))
    (e : (pullback g).obj T ≅ M)
    (hs : ∀ i, e.hom.app ⊤ (g.pullbackSectionsLE T ⊤ ⊤ g.preimage_top.ge (coord i)) = s i)
    (i j : ι) {W : X.Opens} (hW : W ≤ g ⁻¹ᵁ U[i]) :
    g.appLE U[i] W hW (Proj.awayToSection 𝒜 (MvPolynomial.X i) (awayXRatio i j)) •
      M.presheaf.map W.leTop.op (s i) = M.presheaf.map W.leTop.op (s j) := by
  have h (k : ι) : e.hom.app W (g.pullbackSectionsLE T U[i] W hW
      ((T).presheaf.map (U[i]).leTop.op (coord k))) = M.presheaf.map W.leTop.op (s k) := by
    rw [g.pullbackSectionsLE_map T ⊤ W (le_top.trans g.preimage_top.ge) (U[i]).leTop hW,
      ← hs k]
    have hr := e.hom.mapPresheaf.naturality_apply W.leTop.op
      (g.pullbackSectionsLE T ⊤ ⊤ g.preimage_top.ge (coord k))
    -- The two restrictions from the inverse image of the top open compose.
    have hrestr : ((pullback g).obj T).presheaf.map W.leTop.op
        (g.pullbackSectionsLE T ⊤ ⊤ g.preimage_top.ge (coord k)) =
        g.pullbackSectionsLE T ⊤ W (le_top.trans g.preimage_top.ge) (coord k) := by
      simp only [Scheme.Hom.pullbackSectionsLE_apply, ← Functor.map_comp_apply, ← op_comp]
      rfl
    simpa only [mapPresheaf_app, Opposite.unop_op, hrestr] using hr
  have hratio := congrArg (e.hom.app W ∘ g.pullbackSectionsLE T U[i] W hW)
    (Proj.res_polynomialCoordinateSection_eq_smul (R := R) i j)
  simpa only [Function.comp_apply, map_smulₛₗ, Hom.app_smul, h] using hratio.symm

private theorem specMap_coordinateChart (g : X ⟶ ℙ) (i : ι) {W : X.Opens}
    (hW : W ≤ g ⁻¹ᵁ U[i]) :
    W.toSpecΓ ≫ Spec.map (Proj.awayToSection 𝒜 (MvPolynomial.X i) ≫ g.appLE U[i] W hW) ≫
      Proj.awayι 𝒜 _ (coordinate_mem i) one_pos = W.ι ≫ g := by
  rw [Spec.map_comp, ← Category.assoc W.toSpecΓ,
    Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, ← Proj.basicOpenToSpec,
    ← Proj.basicOpenIsoSpec_hom 𝒜 _ (coordinate_mem i) one_pos,
    Proj.awayι, Category.assoc, Iso.hom_inv_id_assoc, Scheme.Hom.resLE_comp_ι]

/-- A morphism over the coefficient ring is the projective map defined by the given
sections if an isomorphism from its pulled-back twist identifies the coordinates
with those sections. -/
theorem eq_toProjectiveSpace_of_pullback (f : X ⟶ Spec (.of R)) (s : ι → Γ(M, ⊤))
    (h : (⨆ i, M.nonvanishingLocus (s i)) = ⊤) (g : X ⟶ ℙ) (hg : g ≫ Proj.toSpecCoeff 𝒜 = f)
    (e : (pullback g).obj T ≅ M)
    (hs : ∀ i, e.hom.app ⊤ (g.pullbackSectionsLE T ⊤ ⊤ g.preimage_top.ge (coord i)) = s i) :
    g = M.toProjectiveSpace f s h := by
  let q := M.toProjectiveSpace f s h
  let d := M.pullbackTwistingSheafOneToProjectiveSpace R f s h
  have hqs (i : ι) : d.hom.app ⊤ (q.pullbackSectionsLE T ⊤ ⊤ q.preimage_top.ge (coord i)) = s i :=
    M.pullbackTwistingSheafOneToProjectiveSpace_hom_app R f s h i
  have hq : q ≫ Proj.toSpecCoeff 𝒜 = f := M.toProjectiveSpace_toSpecCoeff f s h
  refine (X.openCoverOfIsOpenCover _ (IsOpenCover.mk h)).hom_ext _ _ fun j ↦ ?_
  let i : ι := j
  let W := M.nonvanishingLocus (s i)
  have hgW : W ≤ g ⁻¹ᵁ U[i] := (preimage_coordinateOpen_of_pullback g s e hs i).ge
  have hqW : W ≤ q ⁻¹ᵁ U[i] := (M.toProjectiveSpace_preimage_basicOpen f s h i).ge
  -- Compare the affine chart maps out of the spectrum of sections on W.
  let p := Spec.map (Proj.awayToSection 𝒜 (MvPolynomial.X i) ≫ g.appLE U[i] W hgW)
  let p' := Spec.map (Proj.awayToSection 𝒜 (MvPolynomial.X i) ≫ q.appLE U[i] W hqW)
  let a := Proj.awayι 𝒜 _ (coordinate_mem i) one_pos
  have hp : W.toSpecΓ ≫ p ≫ a = W.ι ≫ g := specMap_coordinateChart g i hgW
  have hp' : W.toSpecΓ ≫ p' ≫ a = W.ι ≫ q := specMap_coordinateChart q i hqW
  have hover : W.toSpecΓ ≫ (p ≫ a ≫ Proj.toSpecCoeff 𝒜) =
      W.toSpecΓ ≫ (p' ≫ a ≫ Proj.toSpecCoeff 𝒜) := by
    simp only [reassoc_of% hp, reassoc_of% hp', hg, hq]
  have hcoeff : p ≫ a ≫ Proj.toSpecCoeff 𝒜 = p' ≫ a ≫ Proj.toSpecCoeff 𝒜 := by
    apply ext_of_isAffine
    have : IsIso W.toSpecΓ.appTop := by
      rw [Scheme.Opens.toSpecΓ_appTop]
      infer_instance
    apply (cancel_mono W.toSpecΓ.appTop).mp
    simpa only [Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop hover
  have hmaps : p = p' := Proj.eq_of_awayXRatio i p p' hcoeff fun k ↦ by
    simp only [p, p', Spec.preimage_map, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply]
    have hW : W ≤ M.nonvanishingLocus (M.presheaf.map W.leTop.op (s i)) := by
      rw [M.nonvanishingLocus_map, inf_idem]
    exact M.injective_smul_of_le_nonvanishingLocus hW
      ((appLE_awayXRatio_smul_of_pullback g s e hs i k hgW).trans
        (appLE_awayXRatio_smul_of_pullback q s d hqs i k hqW).symm)
  exact hp.symm.trans (hmaps ▸ hp')

section Evaluation

variable (M) (f : X ⟶ Spec (.of R)) (s : ι → Γ(M, ⊤))
  (hs : (⨆ i, M.nonvanishingLocus (s i)) = ⊤)

local notation "g" => M.toProjectiveSpace f s hs

/-- Evaluate a homogeneous linear form by the sections defining a projective map. -/
def evalProjectiveLinearForm : 𝒜 1 →+ Γ(M, ⊤) where
  toFun p := (M.pullbackTwistingSheafOneToProjectiveSpace R f s hs).hom.app ⊤
    ((g).pullbackSectionsLE T ⊤ ⊤ (g).preimage_top.ge
      (Proj.toTwistingSheaf 𝒜 (rfl : (1 : ℤ) = 1) ⊤ p))
  map_zero' := by simp
  map_add' p q := by simp

/-- Evaluation of a variable gives the section assigned to that coordinate. -/
@[simp]
theorem evalProjectiveLinearForm_X (i : ι) :
    M.evalProjectiveLinearForm f s hs
      ⟨MvPolynomial.X i, (MvPolynomial.mem_homogeneousSubmodule ..).mpr
        (MvPolynomial.isHomogeneous_X R i)⟩ = s i := by
  dsimp [evalProjectiveLinearForm]
  rw [← Proj.polynomialCoordinateSection_def]
  exact M.pullbackTwistingSheafOneToProjectiveSpace_hom_app R f s hs i

/-- Evaluation acts on the coefficient of a linear form by pullback along the
given morphism to the spectrum of the coefficient ring. -/
theorem evalProjectiveLinearForm_smul (r : R) (p : 𝒜 1) :
    M.evalProjectiveLinearForm f s hs (r • p) =
      f.appTop ((Scheme.ΓSpecIso (.of R)).inv r) • M.evalProjectiveLinearForm f s hs p := by
  dsimp [evalProjectiveLinearForm]
  simp only [Proj.toTwistingSheaf_top_smul_toSpecCoeff, map_smulₛₗ, Hom.app_smul]
  have htop : (g).appLE ⊤ ⊤ (g).preimage_top.ge = (g).appTop := (g).appLE_eq_app
  have hc : (g).appLE ⊤ ⊤ (g).preimage_top.ge
      ((Proj.toSpecCoeff 𝒜).appTop ((Scheme.ΓSpecIso (.of R)).inv r)) =
      f.appTop ((Scheme.ΓSpecIso (.of R)).inv r) := by
    rw [htop, ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
      toProjectiveSpace_toSpecCoeff]
  rw [hc]

end Evaluation

section GradedMap

variable {S κ : Type u} [CommRing S]

local notation "ℬ" => MvPolynomial.homogeneousSubmodule κ S

/-- Postcomposing a map defined by covering sections with a graded projective map
gives the map defined by evaluating the substituted linear forms. These evaluated
sections cover the source. The coefficient rings can differ, as they do for
restrictions between affine trivializations of a bundle. -/
theorem toProjectiveSpace_comp_graded_map
    (f : X ⟶ Spec (.of S)) (s : κ → Γ(M, ⊤)) (hs : (⨆ k, M.nonvanishingLocus (s k)) = ⊤)
    (F : 𝒜 →+*ᵍ ℬ)
    (hF : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map F)
    (f' : X ⟶ Spec (.of R))
    (hf' : M.toProjectiveSpace f s hs ≫ Proj.map F hF ≫ Proj.toSpecCoeff 𝒜 = f') :
    let t (i : ι) := M.evalProjectiveLinearForm f s hs
      ⟨F (MvPolynomial.X i), F.map_mem ((MvPolynomial.mem_homogeneousSubmodule ..).mpr
        (MvPolynomial.isHomogeneous_X R i))⟩
    ∃ ht : (⨆ i, M.nonvanishingLocus (t i)) = ⊤,
      M.toProjectiveSpace f s hs ≫ Proj.map F hF = M.toProjectiveSpace f' t ht := by
  intro t
  let g := M.toProjectiveSpace f s hs
  let p := Proj.map F hF
  let D := M.pullbackTwistingSheafOneToProjectiveSpace S f s hs
  have hcover : (⨆ i : ι, U[i]) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _ (MvPolynomial.irrelevant_eq_span_X ι R).le
  let E := Proj.pullbackTwistingSheafIso F hF _ coordinate_mem hcover 1
  let e : (pullback (g ≫ p)).obj T ≅ M :=
    ((pullbackComp g p).app T).symm ≪≫ (pullback g).mapIso E ≪≫ D
  have hcoord (i : ι) : e.hom.app ⊤
      ((g ≫ p).pullbackSectionsLE T ⊤ ⊤ (g ≫ p).preimage_top.ge (coord i)) = t i := by
    have hE := Proj.pullbackTwistingSheafMap_app_top_toTwistingSheaf
      F hF (rfl : (1 : ℤ) = 1) ⟨MvPolynomial.X i, coordinate_mem i⟩
    simp only [e, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
      Hom.comp_app, ConcreteCategory.comp_apply]
    rw [Scheme.Hom.pullbackSectionsLE_comp p T ⊤ g ⊤ p.preimage_top.ge g.preimage_top.ge,
      Scheme.Hom.pullbackSectionsLE_naturality, Proj.pullbackTwistingSheafIso_hom,
      Proj.polynomialCoordinateSection_def, hE]
    rfl
  have ht : (⨆ i, M.nonvanishingLocus (t i)) = ⊤ := by
    simpa only [preimage_coordinateOpen_of_pullback (g ≫ p) t e hcoord] using
      (g ≫ p).iSup_preimage_eq_top hcover
  exact ⟨ht, eq_toProjectiveSpace_of_pullback f' t ht (g ≫ p)
    (by simpa only [Category.assoc] using hf') e hcoord⟩

end GradedMap

end AlgebraicGeometry.Scheme.Modules
