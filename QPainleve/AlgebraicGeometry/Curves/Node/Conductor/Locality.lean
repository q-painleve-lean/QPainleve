/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Etale

import TauCeti.AlgebraicGeometry.Pullback.Carrier

/-!
# Comparing fixed branches on an open subscheme

An equivariant morphism which is an isomorphism over an invariant open identifies
the points in the singular-locus blowups over that open. For nodal curves this
transfers fixation of branches along the isomorphism.
-/

public section

open AlgebraicGeometry TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace CategoryTheory.Iso

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  [C.Over (Spec (.of R))] [C'.Over (Spec (.of R))]
  [Flat (C ↘ Spec (.of R))] [LocallyOfFinitePresentation (C ↘ Spec (.of R))]
  [PureRelativeDimension 1 (C ↘ Spec (.of R))]
  [Flat (C' ↘ Spec (.of R))] [LocallyOfFinitePresentation (C' ↘ Spec (.of R))]
  [PureRelativeDimension 1 (C' ↘ Spec (.of R))]
  (a : C ≅ C) (b : C' ≅ C') [a.hom.IsOver (Spec (.of R))] [hbOver : b.hom.IsOver (Spec (.of R))]

local notation "ν" => Scheme.IdealSheafData.blowupToBase (Scheme.singularLocus R C)
local notation "ν'" => Scheme.IdealSheafData.blowupToBase (Scheme.singularLocus R C')

/-- Over an invariant open on which an equivariant morphism is an isomorphism,
fixed points over the singular locus downstairs give fixed points upstairs. -/
theorem singularLocusBlowupIso_fixes_over_of_isIso_restrict
    (f : C' ⟶ C) [f.IsOver (Spec (.of R))] (U : C.Opens) [IsIso (f ∣_ U)]
    (hU : Set.MapsTo a.hom U U) (hf : b.hom ≫ f = f ≫ a.hom)
    (ha : ∀ x : (C.singularLocus R).blowup, ν x ∈ (C.singularLocus R).support →
      (a.singularLocusBlowupIso (R := R)).hom x = x) :
    ∀ y : (C'.singularLocus R).blowup, ν' y ∈ (C'.singularLocus R).support →
      f (ν' y) ∈ U → (b.singularLocusBlowupIso (R := R)).hom y = y := by
  intro y hy hyU
  -- Restrict the source automorphism to the open that embeds in both curves.
  let V := f ⁻¹ᵁ U
  let j := V.ι
  let i := j ≫ f
  have : IsOpenImmersion i := by
    dsimp only [i, j, V]
    rw [← morphismRestrict_ι]
    infer_instance
  let : V.toScheme.Over (Spec (.of R)) := ⟨j ≫ C' ↘ Spec (.of R)⟩
  have : Flat (V.toScheme ↘ Spec (.of R)) :=
    inferInstanceAs (Flat (j ≫ C' ↘ Spec (.of R)))
  have : LocallyOfFinitePresentation (V.toScheme ↘ Spec (.of R)) :=
    inferInstanceAs (LocallyOfFinitePresentation (j ≫ C' ↘ Spec (.of R)))
  have : PureRelativeDimension 1 (V.toScheme ↘ Spec (.of R)) :=
    inferInstanceAs (PureRelativeDimension 1 (j ≫ C' ↘ Spec (.of R)))
  have : j.IsOver (Spec (.of R)) := ⟨rfl⟩
  have : i.IsOver (Spec (.of R)) := inferInstanceAs ((j ≫ f).IsOver _)
  have hbV : Set.range (j ≫ b.hom) ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    have hx : f (j x) ∈ U := f.mem_preimage.mp x.property
    have hw := congrArg (fun g : C' ⟶ C ↦ g (j x)) hf
    simp only [Scheme.Hom.comp_apply] at hw
    exact ⟨⟨b.hom (j x), f.mem_preimage.mpr (hw.symm ▸ hU hx)⟩, rfl⟩
  let g := IsOpenImmersion.lift j (j ≫ b.hom) hbV
  have hg : g ≫ j = j ≫ b.hom := IsOpenImmersion.lift_fac _ _ _
  have : Etale (g ≫ j) := hg ▸ inferInstance
  have : Etale g := Etale.of_comp g j
  have : g.IsOver (Spec (.of R)) := ⟨by
    exact ((reassoc_of% hg) (C' ↘ Spec (.of R))).trans (by rw [hbOver.comp_over]; rfl)⟩
  have hi : g ≫ i = i ≫ a.hom := by
    dsimp only [i]
    rw [← Category.assoc, hg, Category.assoc, hf, Category.assoc]
  -- Compare the two images of the point from the blowup of the common open.
  obtain ⟨z, rfl⟩ : y ∈ Set.range (j.singularLocusBlowupMap (R := R)) := by
    rw [Scheme.Pullback.range_snd_of_isPullback (j.isPullback_singularLocusBlowupMap (R := R))]
    exact ⟨⟨ν' y, f.mem_preimage.mpr hyU⟩, rfl⟩
  have hzi : ν ((i.singularLocusBlowupMap (R := R)) z) ∈ (C.singularLocus R).support := by
    have hz := hy
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.singularLocusBlowupMap_blowupToBase,
      Scheme.Hom.comp_apply] at hz ⊢
    exact (i.mem_support_singularLocus_image_iff _).mpr
      ((j.mem_support_singularLocus_image_iff _).mp hz)
  have equivariant {A : Scheme.{u}} [A.Over (Spec (.of R))]
      [Flat (A ↘ Spec (.of R))] [LocallyOfFinitePresentation (A ↘ Spec (.of R))]
      [PureRelativeDimension 1 (A ↘ Spec (.of R))]
      (m : V.toScheme ⟶ A) [Etale m] [m.IsOver (Spec (.of R))]
      (e : A ≅ A) [e.hom.IsOver (Spec (.of R))] (he : g ≫ m = m ≫ e.hom) :
      m.singularLocusBlowupMap (R := R) ((g.singularLocusBlowupMap (R := R)) z) =
        (e.singularLocusBlowupIso (R := R)).hom ((m.singularLocusBlowupMap (R := R)) z) := by
    have he' : (g ≫ m).singularLocusBlowupMap (R := R) =
        (m ≫ e.hom).singularLocusBlowupMap (R := R) := by congr
    simpa only [Scheme.Hom.singularLocusBlowupMap_comp, Scheme.Hom.singularLocusBlowupMap_iso_hom,
      Scheme.Hom.comp_apply] using congrArg (fun l ↦ l z) he'
  have hz : (g.singularLocusBlowupMap (R := R)) z = z := by
    apply (i.singularLocusBlowupMap (R := R)).injective
    exact (equivariant i a hi).trans (ha _ hzi)
  simpa only [hz] using (equivariant j b hg).symm

end CategoryTheory.Iso
