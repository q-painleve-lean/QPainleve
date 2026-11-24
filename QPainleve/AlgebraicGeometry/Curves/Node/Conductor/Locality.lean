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

private theorem fixes_singularLocusBlowup_over_open_iff
    {V : Scheme.{u}} [V.Over (Spec (.of R))]
    [Flat (V ↘ Spec (.of R))] [LocallyOfFinitePresentation (V ↘ Spec (.of R))]
    [PureRelativeDimension 1 (V ↘ Spec (.of R))]
    (i : V ⟶ C) [IsOpenImmersion i] [i.IsOver (Spec (.of R))]
    (g : V ⟶ V) [Etale g] [g.IsOver (Spec (.of R))]
    (hi : g ≫ i = i ≫ a.hom) (U : C.Opens) (hU : Set.range i = U) :
    (∀ z : (V.singularLocus R).blowup,
      (V.singularLocus R).blowupToBase z ∈ (V.singularLocus R).support →
        (g.singularLocusBlowupMap (R := R)) z = z) ↔
    (∀ x : (C.singularLocus R).blowup, ν x ∈ (C.singularLocus R).support →
      ν x ∈ U → (a.singularLocusBlowupIso (R := R)).hom x = x) := by
  have hcomp : (g ≫ i).singularLocusBlowupMap (R := R) =
      (i ≫ a.hom).singularLocusBlowupMap (R := R) := by congr
  simp only [Scheme.Hom.singularLocusBlowupMap_comp,
    Scheme.Hom.singularLocusBlowupMap_iso_hom] at hcomp
  have hpoint (z : (V.singularLocus R).blowup) :
      (i.singularLocusBlowupMap (R := R)) ((g.singularLocusBlowupMap (R := R)) z) =
        (a.singularLocusBlowupIso (R := R)).hom ((i.singularLocusBlowupMap (R := R)) z) :=
    congrArg (fun m : (V.singularLocus R).blowup ⟶ (C.singularLocus R).blowup ↦ m z) hcomp
  have hsing (z : (V.singularLocus R).blowup) :
      ν ((i.singularLocusBlowupMap (R := R)) z) ∈ (C.singularLocus R).support ↔
        (V.singularLocus R).blowupToBase z ∈ (V.singularLocus R).support := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.singularLocusBlowupMap_blowupToBase,
      Scheme.Hom.comp_apply, i.mem_support_singularLocus_image_iff]
  constructor
  · intro h x hx hxU
    obtain ⟨z, rfl⟩ : x ∈ Set.range (i.singularLocusBlowupMap (R := R)) := by
      rw [Scheme.Pullback.range_snd_of_isPullback (i.isPullback_singularLocusBlowupMap (R := R))]
      exact hU.symm ▸ hxU
    rw [← hpoint, h z ((hsing z).mp hx)]
  · intro h z hz
    apply (i.singularLocusBlowupMap (R := R)).injective
    rw [hpoint]
    apply h _ ((hsing z).mpr hz)
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.singularLocusBlowupMap_blowupToBase,
      Scheme.Hom.comp_apply]
    rw [← SetLike.mem_coe, ← hU]
    exact Set.mem_range_self _

/-- Over an invariant open on which an equivariant morphism is an isomorphism,
fixation of the points over the singular locus is equivalent upstairs and downstairs. -/
theorem singularLocusBlowupIso_fixes_over_isIso_restrict_iff
    (f : C' ⟶ C) [f.IsOver (Spec (.of R))] (U : C.Opens) [IsIso (f ∣_ U)]
    (hU : Set.MapsTo a.hom U U) (hf : b.hom ≫ f = f ≫ a.hom) :
    (∀ y : (C'.singularLocus R).blowup, ν' y ∈ (C'.singularLocus R).support →
      f (ν' y) ∈ U → (b.singularLocusBlowupIso (R := R)).hom y = y) ↔
    (∀ x : (C.singularLocus R).blowup, ν x ∈ (C.singularLocus R).support →
      ν x ∈ U → (a.singularLocusBlowupIso (R := R)).hom x = x) := by
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
  have hjRange : Set.range j = V := V.range_ι
  have hiRange : Set.range i = U := by
    dsimp only [i, j, V]
    rw [← morphismRestrict_ι, Scheme.Hom.comp_base, TopCat.coe_comp,
      (f ∣_ U).surjective.range_comp, U.range_ι]
  exact (fixes_singularLocusBlowup_over_open_iff b j g hg V hjRange).symm.trans
    (fixes_singularLocusBlowup_over_open_iff a i g hi U hiRange)

end CategoryTheory.Iso
