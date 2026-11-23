/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Global functions on a disjoint open cover

Restriction to a pairwise disjoint open cover identifies the ring of global functions
with the product of the rings of functions on the covering open subschemes. A scheme
whose global sections form a field has singleton image under any map into an affine open.
-/

public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

universe u v

variable {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens)

private theorem bijective_appTop_pi_of_disjoint (hcover : ⨆ i, U i = ⊤)
    (hdisj : Pairwise (Function.onFun Disjoint U)) :
    Function.Bijective (RingHom.pi fun i ↦ (U i).ι.appTop.hom) := by
  have happ (i : ι) : (U i).ι.appTop ≫ (U i).topIso.hom =
      X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op := by
    rw [Opens.ι_appTop, Opens.topIso_hom]
    -- Express sections of the open subscheme as sections on the image of its top open.
    change X.presheaf.map (homOfLE (le_top : (U i).ι ''ᵁ ⊤ ≤ ⊤)).op ≫
      X.presheaf.map (eqToHom (U i).ι_image_top.symm).op =
        X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op
    rw [← Functor.map_comp]
    rfl
  have hglue (f : ∀ i, Γ((U i).toScheme, ⊤)) :
      ∃! s : Γ(X, ⊤), ∀ i, (U i).ι.appTop s = f i := by
    let t (i : ι) := (U i).topIso.hom (f i)
    obtain ⟨s, hs, hu⟩ := X.sheaf.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top)
      hcover.ge t (fun i j ↦ by
        obtain rfl | hij := eq_or_ne i j
        · rfl
        · have : Subsingleton Γ(X, U i ⊓ U j) :=
            CommRingCat.subsingleton_of_isTerminal
              (X.sheaf.isTerminalOfEqEmpty (hdisj hij).eq_bot)
          exact @Subsingleton.elim Γ(X, U i ⊓ U j) this _ _)
    have hchar (r : Γ(X, ⊤)) (i : ι) :
        X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op r = t i ↔
          (U i).ι.appTop r = f i := by
      rw [← happ]
      exact (ConcreteCategory.bijective_of_isIso (U i).topIso.hom).injective.eq_iff
    exact ⟨s, fun i ↦ (hchar s i).mp (hs i), fun r hr ↦ hu r fun i ↦ (hchar r i).mpr (hr i)⟩
  constructor
  · intro s t h
    obtain ⟨r, _, hr⟩ := hglue (fun i ↦ (U i).ι.appTop t)
    exact (hr s (fun i ↦ congrFun h i)).trans (hr t (fun _ ↦ rfl)).symm
  · intro f
    obtain ⟨s, hs, _⟩ := hglue f
    exact ⟨s, funext hs⟩

/-- On a scheme covered by pairwise disjoint open subschemes, global functions are
equivalent to tuples of functions on the opens. -/
def globalSectionsEquivOfDisjointCover (hcover : ⨆ i, U i = ⊤)
    (hdisj : Pairwise (Function.onFun Disjoint U)) :
    Γ(X, ⊤) ≃+* (∀ i, Γ((U i).toScheme, ⊤)) :=
  RingEquiv.ofBijective _ (bijective_appTop_pi_of_disjoint U hcover hdisj)

/-- Each coordinate is restriction along the corresponding open immersion. -/
@[simp]
theorem globalSectionsEquivOfDisjointCover_apply (hcover : ⨆ i, U i = ⊤)
    (hdisj : Pairwise (Function.onFun Disjoint U)) (f : Γ(X, ⊤)) (i : ι) :
    globalSectionsEquivOfDisjointCover U hcover hdisj f i = (U i).ι.appTop f :=
  (rfl)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

/-- A scheme whose ring of global sections is a field has at most one image point
under a morphism landing in an affine open. -/
theorem subsingleton_range_of_isField_globalSections {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsField Γ(X, ⊤)) {U : Y.Opens} (hU : IsAffineOpen U)
    (hf : Set.range f ⊆ U) : (Set.range f).Subsingleton := by
  let r := IsOpenImmersion.lift U.ι f ((Opens.range_ι U).symm ▸ hf)
  have hr : r ≫ U.ι = f := IsOpenImmersion.lift_fac ..
  let : IsAffine U.toScheme := hU
  have hfac : r = X.toSpecΓ ≫ Spec.map r.appTop ≫ U.toScheme.isoSpec.inv := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, ← Scheme.isoSpec_hom,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let : Field Γ(X, ⊤) := hX.toField
  have : Subsingleton (Spec Γ(X, ⊤)) :=
    inferInstanceAs (Subsingleton (Spec (.of Γ(X, ⊤))))
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  have hz : X.toSpecΓ x = X.toSpecΓ y := Subsingleton.elim _ _
  rw [← hr, hfac]
  simp only [Scheme.Hom.comp_apply, hz]

end AlgebraicGeometry.Scheme.Hom
