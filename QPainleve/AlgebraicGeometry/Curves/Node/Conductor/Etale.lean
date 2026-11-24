/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Isomorphism
public import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Etale

import TauCeti.AlgebraicGeometry.Blowup.Pullback

/-!
# Étale base change of the blowup of the singular locus

For a relative curve, blowing up the singular subscheme commutes with étale
base change. For nodal curves this identifies normalization points over any
open subscheme, including the separate branches at a self-node.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R] {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  [Flat (X ↘ Spec (.of R))] [LocallyOfFinitePresentation (X ↘ Spec (.of R))]
  [PureRelativeDimension 1 (X ↘ Spec (.of R))]
  [Flat (Y ↘ Spec (.of R))] [LocallyOfFinitePresentation (Y ↘ Spec (.of R))]
  [PureRelativeDimension 1 (Y ↘ Spec (.of R))]
  (f : X ⟶ Y) [Etale f] [f.IsOver (Spec (.of R))]

/-- Along an étale morphism of relative curves, a point lies in the singular
support if and only if its image does. -/
theorem mem_support_singularLocus_image_iff (x : X) :
    f x ∈ (Y.singularLocus R).support ↔ x ∈ (X.singularLocus R).support := by
  rw [singularLocus_eq_comap_of_etale (R := R) f, IdealSheafData.support_comap]
  rfl

/-- A morphism which is an isomorphism over an open induces a bijection between
the singular points over that open and the singular points in it. -/
theorem bijOn_support_singularLocus_of_isIso_morphismRestrict
    (g : X ⟶ Y) [g.IsOver (Spec (.of R))] (U : Y.Opens) [IsIso (g ∣_ U)] :
    Set.BijOn g
      (((g ⁻¹ᵁ U : X.Opens) : Set X) ∩ (X.singularLocus R).support)
      ((U : Set Y) ∩ (Y.singularLocus R).support) := by
  let V := g ⁻¹ᵁ U
  let j := V.ι
  let i := j ≫ g
  have : IsOpenImmersion i := by
    dsimp only [i, j, V]
    rw [← morphismRestrict_ι]
    infer_instance
  let : V.toScheme.Over (Spec (.of R)) := ⟨j ≫ X ↘ Spec (.of R)⟩
  have : Flat (V.toScheme ↘ Spec (.of R)) :=
    inferInstanceAs (Flat (j ≫ X ↘ Spec (.of R)))
  have : LocallyOfFinitePresentation (V.toScheme ↘ Spec (.of R)) :=
    inferInstanceAs (LocallyOfFinitePresentation (j ≫ X ↘ Spec (.of R)))
  have : PureRelativeDimension 1 (V.toScheme ↘ Spec (.of R)) :=
    inferInstanceAs (PureRelativeDimension 1 (j ≫ X ↘ Spec (.of R)))
  have : j.IsOver (Spec (.of R)) := ⟨rfl⟩
  have : i.IsOver (Spec (.of R)) := inferInstanceAs ((j ≫ g).IsOver _)
  have hsing (x : X) (hx : x ∈ V) :
      g x ∈ (Y.singularLocus R).support ↔ x ∈ (X.singularLocus R).support :=
    (i.mem_support_singularLocus_image_iff (R := R) ⟨x, hx⟩).trans
      (j.mem_support_singularLocus_image_iff (R := R) ⟨x, hx⟩).symm
  have hbij : Function.Bijective (g ∣_ U) :=
    ⟨(g ∣_ U).injective, (g ∣_ U).surjective⟩
  refine ⟨fun x hx ↦ ⟨g.mem_preimage.mp hx.1, (hsing x hx.1).mpr hx.2⟩, ?_, ?_⟩
  · intro x hx y hy hxy
    have he : (g ∣_ U) ⟨x, hx.1⟩ = (g ∣_ U) ⟨y, hy.1⟩ :=
      Subtype.ext ((morphismRestrict_base_coe g U ⟨x, hx.1⟩).trans
        (hxy.trans (morphismRestrict_base_coe g U ⟨y, hy.1⟩).symm))
    exact congrArg Subtype.val (hbij.1 he)
  · intro y hy
    obtain ⟨x, hx⟩ := hbij.2 ⟨y, hy.1⟩
    have he : g x.val = y := (morphismRestrict_base_coe g U x).symm.trans
      (congrArg Subtype.val hx)
    exact ⟨x.val, ⟨x.property, (hsing _ x.property).mp (he.symm ▸ hy.2)⟩, he⟩

/-- The map of singular-locus blowups induced by an étale morphism of relative curves. -/
def singularLocusBlowupMap : (X.singularLocus R).blowup ⟶ (Y.singularLocus R).blowup :=
  eqToHom (congrArg IdealSheafData.blowup (singularLocus_eq_comap_of_etale (R := R) f)) ≫
    (Y.singularLocus R).blowupMap f

/-- The blowup of the singular locus commutes with étale base change. -/
theorem isPullback_singularLocusBlowupMap :
    IsPullback (X.singularLocus R).blowupToBase (f.singularLocusBlowupMap (R := R))
      f (Y.singularLocus R).blowupToBase := by
  refine ((Y.singularLocus R).isPullback_blowupMap_of_flat f).of_iso'
    (eqToIso (congrArg IdealSheafData.blowup (singularLocus_eq_comap_of_etale (R := R) f)))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ (by simp [singularLocusBlowupMap]) (by simp) (by simp)
  have cast_projection {I J : X.IdealSheafData} (h : I = J) :
      eqToHom (congrArg IdealSheafData.blowup h) ≫ J.blowupToBase = I.blowupToBase := by
    subst J
    simp
  simpa only [eqToIso.hom, Iso.refl_hom, Category.comp_id] using
    cast_projection (singularLocus_eq_comap_of_etale (R := R) f)

/-- The map on blowups lies over the original morphism of curves. -/
@[reassoc (attr := simp)]
theorem singularLocusBlowupMap_blowupToBase :
    f.singularLocusBlowupMap (R := R) ≫ (Y.singularLocus R).blowupToBase =
      (X.singularLocus R).blowupToBase ≫ f :=
  (f.isPullback_singularLocusBlowupMap (R := R)).w.symm

instance [IsOpenImmersion f] : IsOpenImmersion (f.singularLocusBlowupMap (R := R)) :=
  MorphismProperty.of_isPullback (f.isPullback_singularLocusBlowupMap (R := R)) inferInstance

@[simp]
theorem singularLocusBlowupMap_iso_hom (e : X ≅ Y) [e.hom.IsOver (Spec (.of R))] :
    e.hom.singularLocusBlowupMap (R := R) = (e.singularLocusBlowupIso (R := R)).hom := by
  apply (Y.singularLocus R).blowup_hom_ext
  · simp
  · rw [singularLocusBlowupMap_blowupToBase, IdealSheafData.comap_comp,
      ← singularLocus_eq_comap_of_etale (R := R) e.hom]
    exact (X.singularLocus R).isEffectiveCartier_comap_blowupToBase

@[simp]
theorem singularLocusBlowupMap_id :
    (𝟙 X : X ⟶ X).singularLocusBlowupMap (R := R) = 𝟙 _ := by
  have : (Iso.refl X).hom.IsOver (Spec (.of R)) := by
    rw [Iso.refl_hom]
    infer_instance
  simpa only [Iso.refl_hom, Iso.singularLocusBlowupIso_refl] using
    (singularLocusBlowupMap_iso_hom (R := R) (Iso.refl X))

variable [Z.Over (Spec (.of R))]
  [Flat (Z ↘ Spec (.of R))] [LocallyOfFinitePresentation (Z ↘ Spec (.of R))]
  [PureRelativeDimension 1 (Z ↘ Spec (.of R))]

@[reassoc]
theorem singularLocusBlowupMap_comp (g : Y ⟶ Z) [Etale g] [g.IsOver (Spec (.of R))] :
    (f ≫ g).singularLocusBlowupMap (R := R) =
      f.singularLocusBlowupMap (R := R) ≫ g.singularLocusBlowupMap (R := R) := by
  apply (Z.singularLocus R).blowup_hom_ext
  · simp
  · rw [singularLocusBlowupMap_blowupToBase, IdealSheafData.comap_comp,
      ← singularLocus_eq_comap_of_etale (R := R) (f ≫ g)]
    exact (X.singularLocus R).isEffectiveCartier_comap_blowupToBase

end AlgebraicGeometry.Scheme.Hom
