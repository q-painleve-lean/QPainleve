/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Fiber
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import QPainleve.AlgebraicGeometry.IdealSheaf.RegularPair
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Regular
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Regularity of point blowups

Blowing up a closed point of local dimension two on a regular scheme preserves regularity.
The exceptional divisor is regular by the existing projective-line comparison for a regular
pair. The effective Cartier equation lifts regularity to the blowup along that divisor.
Over a perfect field, the blowup of a smooth surface is smooth of relative dimension two.

This uses the description of the exceptional divisor of a quadratic transformation in
[The Stacks Project, Lemma 54.3.1](https://stacks.math.columbia.edu/tag/0AGQ) and Tau Ceti's
`IsEffectiveCartier.isRegularLocalRing_stalk_of_mem_support`.
-/

public section

open CategoryTheory Limits TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {p : X}

local notation "Iₚ" =>
  vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)

private theorem coe_support_point (hp : IsClosed ({p} : Set X)) :
    ((Iₚ).support : Set X) = {p} := by
  rw [coe_support_vanishingIdeal, Closeds.coe_mk]
  exact hp.closure_eq

private theorem isIso_subschemeCover_of_point (hp : IsClosed ({p} : Set X))
    (U : X.affineOpens) (hpU : p ∈ U.val) : IsIso ((Iₚ).subschemeCover.f U) := by
  have : IsOpenImmersion ((Iₚ).subschemeCover.f U) := (Iₚ).subschemeCover.map_prop U
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [(Iₚ).opensRange_subschemeCover_map]
  refine top_unique fun x _ ↦ ?_
  have hx : (Iₚ).subschemeι x ∈ ((Iₚ).support : Set X) :=
    (Iₚ).range_subschemeι ▸ Set.mem_range_self x
  rw [coe_support_point hp, Set.mem_singleton_iff] at hx
  exact (Iₚ).subschemeι.mem_preimage.mpr (hx.symm ▸ hpU)

private theorem exceptional_integral_and_dimension [IsLocallyNoetherian X]
    [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (hp : IsClosed ({p} : Set X)) :
    let E := (Iₚ).comap (Iₚ).blowupToBase
    IsIntegral E.subscheme ∧ IsRegular E.subscheme ∧
      ∀ x : E.subscheme, IsClosed {x} → ringKrullDim (E.subscheme.presheaf.stalk x) = 1 := by
  dsimp only
  obtain ⟨U, hpU, -, a, b, hspan, hab, -⟩ :=
    exists_mem_le_span_pair_vanishingIdeal_closure_singleton hdim (Opens.mem_top p)
  let I := (Iₚ)
  let J := I.ideal U
  let S := Γ(X, U) ⧸ J
  have hJ : J.IsMaximal := by
    have hprime : J = (U.property.primeIdealOf ⟨p, hpU⟩).asIdeal :=
      vanishingIdeal_closure_singleton_ideal p U hpU
    rw [hprime]
    exact U.property.primeIdealOf_isMaximal_of_isClosed ⟨p, hpU⟩ hp
  let _ : Field S := Ideal.Quotient.field J
  let f := I.blowupToBase
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ U.property.fromSpec
  let j := I.subschemeCover.f U
  have hj : IsIso j := isIso_subschemeCover_of_point hp U hpU
  have hq : j ≫ I.subschemeι = q :=
    (I.subschemeCover_map_subschemeι U).trans (I.glueDataObjι_ι U)
  have hlist : Ideal.ofList [a, b] = J :=
    (Ideal.ofList_cons _ _).trans (by simpa only [Ideal.ofList_singleton, ← Ideal.span_insert]
      using hspan)
  let e := (I.isPullback_blowupChart_projectiveLine U.property hab hlist).isoPullback
  let ej := @asIso _ _ _ _ j hj
  have hej : ej.hom = j := asIso_hom j
  have hP : IsPullback (pullback.fst f q) (pullback.snd f q ≫ j) f I.subschemeι :=
    (IsPullback.of_hasPullback f q).of_iso (.refl _) (.refl _) ej (.refl _)
      (by simp) (by simp [hej]) (by simp) (by
        simp only [Iso.refl_hom, Category.comp_id, hej]
        exact hq.symm)
  let iso := I.comapIso f ≪≫ hP.isoPullback.symm ≪≫ e.symm
  have hL : IsRegular (projectiveLine S) := ⟨fun _ ↦ inferInstance⟩
  refine ⟨IsIntegral.of_isIso iso.inv, IsRegular.of_isOpenImmersion iso.hom, fun x hx ↦ ?_⟩
  have hx' : IsClosed {iso.hom x} := by
    simpa using iso.hom.isClosedEmbedding.isClosedMap _ hx
  have hline := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
    (projectiveLine S ↘ Spec (.of S)) 1).mp inferInstance).2 _ hx'
  rw [ringKrullDim_stalk_eq_coheight] at hline ⊢
  exact_mod_cast (coheight_eq_of_isOpenImmersion iso.hom).symm.trans (by exact_mod_cast hline)

/-- The exceptional subscheme of the blowup of a regular closed point of local dimension
two is integral. The affine comparison identifies it with a projective line over the
residue field of the center. -/
theorem isIntegral_exceptional_blowup_closed_point [IsLocallyNoetherian X]
    [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (hp : IsClosed ({p} : Set X)) :
    IsIntegral ((Iₚ).comap (Iₚ).blowupToBase).subscheme :=
  (exceptional_integral_and_dimension hdim hp).1

/-- Over the isomorphism locus of a morphism, a regular two-dimensional stalk on the target
gives an integral exceptional subscheme in the blowup of the corresponding closed point on
the source. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.isIntegral_exceptional_blowup_of_mem_isoLocus
    {Y : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Y)
    [IsRegularLocalRing (Y.presheaf.stalk (f p))]
    (hdim : ringKrullDim (Y.presheaf.stalk (f p)) = 2) (hp : IsClosed ({p} : Set X))
    (h : f p ∈ f.isoLocus) :
    IsIntegral ((Iₚ).comap (Iₚ).blowupToBase).subscheme := by
  have : IsIso (f.stalkMap p) := f.isIso_stalkMap_of_mem_isoLocus h
  let e := (asIso (f.stalkMap p)).commRingCatIsoToRingEquiv
  have : IsRegularLocalRing (X.presheaf.stalk p) := .of_ringEquiv e
  exact isIntegral_exceptional_blowup_closed_point
    ((ringKrullDim_eq_of_ringEquiv e).symm.trans hdim) hp

private theorem mem_preimage_support_compl {I : X.IdealSheafData} {y : I.blowup}
    (hy : y ∉ (I.comap I.blowupToBase).support) :
    y ∈ I.blowupToBase ⁻¹ᵁ I.support.compl := by
  rw [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage] at hy
  exact I.blowupToBase.mem_preimage.mpr hy

/-- The blowup of a regular scheme at a closed point with two-dimensional local ring is regular. -/
theorem isRegular_blowup_closed_point [IsRegular X]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (hp : IsClosed ({p} : Set X)) :
    IsRegular (Iₚ).blowup := by
  let I := (Iₚ)
  let f := I.blowupToBase
  let E := I.comap f
  have : IsLocallyNoetherian I.blowup := LocallyOfFiniteType.isLocallyNoetherian f
  have hE : IsRegular E.subscheme := (exceptional_integral_and_dimension hdim hp).2.1
  refine ⟨fun y ↦ ?_⟩
  by_cases hy : y ∈ E.support
  · exact I.isEffectiveCartier_comap_blowupToBase.isRegularLocalRing_stalk_of_mem_support
      (fun _ ↦ inferInstance) hy
  · let y' : (f ⁻¹ᵁ I.support.compl).toScheme := ⟨y, mem_preimage_support_compl hy⟩
    have : IsRegular (f ⁻¹ᵁ I.support.compl).toScheme :=
      IsRegular.of_isOpenImmersion (f ∣_ I.support.compl)
    exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion (f ⁻¹ᵁ I.support.compl).ι y').mpr
      inferInstance

/-- Over a perfect field, blowing up a closed point of a smooth surface gives a smooth surface
of the same relative dimension. -/
theorem smoothOfRelativeDimension_blowup_closed_point {k : Type u} [Field k] [PerfectField k]
    (g : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 g] (hp : IsClosed ({p} : Set X)) :
    SmoothOfRelativeDimension 2 ((Iₚ).blowupToBase ≫ g) := by
  have : Smooth g := SmoothOfRelativeDimension.smooth 2 g
  have hX := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq g 2).mp inferInstance).2
  have : IsRegular X := IsRegular.of_smooth g
  let I := (Iₚ)
  let f := I.blowupToBase
  let E := I.comap f
  have : IsRegular I.blowup := isRegular_blowup_closed_point (hX p hp) hp
  refine (smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (f ≫ g) 2).mpr
    ⟨(f ≫ g).smooth_of_isRegularLocalRing_stalk, fun y hy ↦ ?_⟩
  by_cases hyE : y ∈ E.support
  · have hyRange : y ∈ (E.support : Set I.blowup) := hyE
    rw [← E.range_subschemeι] at hyRange
    obtain ⟨x, rfl⟩ := hyRange
    have hx : IsClosed ({x} : Set E.subscheme) := by
      have hpull := hy.preimage E.subschemeι.continuous
      rwa [← Set.image_singleton, Set.preimage_image_eq _ E.subschemeι.isClosedEmbedding.injective]
        at hpull
    rw [← I.isEffectiveCartier_comap_blowupToBase.ringKrullDim_stalk_add_one x,
      (exceptional_integral_and_dimension (hX p hp) hp).2.2 x hx]
    norm_num
  · have hfy : IsClosed ({f y} : Set X) := by
      simpa using f.isClosedMap _ hy
    let U : X.Opens := I.support.compl
    let y' : (f ⁻¹ᵁ U).toScheme := ⟨y, mem_preimage_support_compl hyE⟩
    have : IsIso (f ∣_ U) := I.isIso_blowupToBase_restrict_compl_support
    have hcomp : U.ι ((f ∣_ U) y') = f y := by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    have hcoheight : Order.coheight y = Order.coheight (f y) :=
      (coheight_eq_of_isOpenImmersion (f ⁻¹ᵁ U).ι (x := y')).trans
        ((coheight_eq_of_isOpenImmersion (f ∣_ U) (x := y')).symm.trans
          ((coheight_eq_of_isOpenImmersion U.ι).symm.trans (congrArg Order.coheight hcomp)))
    rw [ringKrullDim_stalk_eq_coheight, hcoheight, ← ringKrullDim_stalk_eq_coheight]
    exact hX _ hfy

end AlgebraicGeometry.Scheme.IdealSheafData
