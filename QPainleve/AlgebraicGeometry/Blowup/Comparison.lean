/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Pullback
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic

import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Comparing blowups whose centers agree on an open

If two center ideals agree near the support of one of them, the blowup
of the other factors through its blowup. Over the open where the ideals
agree, both blowups have the same restriction and the factorization
identifies those restrictions.
-/

public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {I J : X.IdealSheafData} {U : X.Opens}

/-- If `I` and `J` agree on an open containing the support of `J`, then the inverse
image of `J` on the blowup of `I` is an effective Cartier divisor. -/
theorem isEffectiveCartier_comap_blowupToBase_of_comap_eq
    (h : I.comap U.ι = J.comap U.ι) (hU : (J.support : Set X) ⊆ U) :
    (J.comap I.blowupToBase).IsEffectiveCartier := by
  apply isEffectiveCartier_of_forall_exists_isOpenImmersion
  intro y
  by_cases hy : I.blowupToBase y ∈ U
  · let f := I.blowupMap U.ι
    refine ⟨_, f, inferInstance, ?_, ?_⟩
    · rwa [← Scheme.Hom.coe_opensRange, SetLike.mem_coe, I.opensRange_blowupMap,
        Scheme.Opens.opensRange_ι, Scheme.Hom.mem_preimage]
    · rw [← comap_comp, I.blowupMap_blowupToBase, comap_comp, ← h]
      exact (I.comap U.ι).isEffectiveCartier_comap_blowupToBase
  · let V : I.blowup.Opens := (J.comap I.blowupToBase).support.compl
    refine ⟨_, V.ι, inferInstance, ?_, ?_⟩
    · rw [Scheme.Opens.range_ι]
      intro hmem
      apply hy (hU _)
      simpa only [support_comap, Closeds.coe_preimage, Set.mem_preimage] using hmem
    · have hv : (J.comap I.blowupToBase).comap V.ι = ⊤ :=
        (comap_eq_top_iff _ _).mpr (by ext x; exact iff_true_intro x.property)
      rw [hv]
      exact isEffectiveCartier_top _

/-- A morphism from the blowup of `I` to the blowup of `J` over the base identifies
their open restrictions wherever the center ideals agree. -/
theorem isPullback_blowupMap_of_comap_eq {g : I.blowup ⟶ J.blowup}
    (hg : g ≫ J.blowupToBase = I.blowupToBase) (h : I.comap U.ι = J.comap U.ι) :
    IsPullback (eqToHom (congrArg blowup h)) (I.blowupMap U.ι) (J.blowupMap U.ι) g := by
  have he (A B : U.toScheme.IdealSheafData) (hAB : A = B) :
      eqToHom (congrArg blowup hAB) ≫ B.blowupToBase = A.blowupToBase := by
    subst B
    simp
  have hw : I.blowupMap U.ι ≫ g = eqToHom (congrArg blowup h) ≫ J.blowupMap U.ι := by
    apply J.blowup_hom_ext
    · simp [Category.assoc, hg, reassoc_of% (he _ _ h)]
    · rw [Category.assoc, hg, I.blowupMap_blowupToBase, comap_comp, ← h]
      exact (I.comap U.ι).isEffectiveCartier_comap_blowupToBase
  apply IsOpenImmersion.isPullback _ _ _ _ hw
  simp only [opensRange_blowupMap, ← Scheme.Hom.comp_preimage, hg]

/-- A comparison of blowups is an isomorphism over the inverse image of any open
on which their centers agree. -/
theorem isIso_morphismRestrict_blowup_of_comap_eq {g : I.blowup ⟶ J.blowup}
    (hg : g ≫ J.blowupToBase = I.blowupToBase) (h : I.comap U.ι = J.comap U.ι) :
    IsIso (g ∣_ (J.blowupToBase ⁻¹ᵁ U)) := by
  let j := J.blowupMap U.ι
  let e := j.isoOpensRange
  have H := isPullback_blowupMap_of_comap_eq hg h
  let f := eqToHom (congrArg blowup h) ≫ e.hom
  have H' : IsPullback f (I.blowupMap U.ι) j.opensRange.ι g :=
    H.of_iso (.refl _) e (.refl _) (.refl _) (by simp [f]) (by simp)
      (by simp [e, j]) (by simp)
  have H'' := isPullback_morphismRestrict g j.opensRange
  have hf : IsIso f := inferInstance
  have hi : IsIso (g ∣_ j.opensRange) := by
    rw [← isIso_comp_left_iff (H'.isoIsPullback _ _ H'').hom, H'.isoIsPullback_hom_fst]
    exact hf
  have hv : j.opensRange = J.blowupToBase ⁻¹ᵁ U :=
    (J.opensRange_blowupMap U.ι).trans (congrArg _ U.opensRange_ι)
  rw [hv] at hi
  exact hi

/-- Over a point where the center ideals agree on a neighborhood, a morphism of the
two blowups over the base induces a bijection of the point fibers. -/
theorem bijOn_fiber_of_comap_eq {g : I.blowup ⟶ J.blowup}
    (hg : g ≫ J.blowupToBase = I.blowupToBase) (h : I.comap U.ι = J.comap U.ι)
    {x : X} (hx : x ∈ U) :
    Set.BijOn g (I.blowupToBase ⁻¹' {x}) (J.blowupToBase ⁻¹' {x}) := by
  let V := J.blowupToBase ⁻¹ᵁ U
  have hIso : IsIso (g ∣_ V) := isIso_morphismRestrict_blowup_of_comap_eq hg h
  have hV : V ≤ g.isoLocus := g.le_isoLocus_iff.mpr hIso
  have hfiber (y : I.blowup) : J.blowupToBase (g y) = I.blowupToBase y :=
    congrArg (fun f : I.blowup ⟶ X ↦ f y) hg
  have hV' {z : J.blowup} (hz : z ∈ J.blowupToBase ⁻¹' ({x} : Set X)) : z ∈ V :=
    J.blowupToBase.mem_preimage.mpr (Set.mem_singleton_iff.mp hz ▸ hx)
  have hmap : Set.MapsTo g (I.blowupToBase ⁻¹' {x}) (J.blowupToBase ⁻¹' {x}) :=
    fun y hy ↦ (hfiber y).trans (Set.mem_singleton_iff.mp hy)
  refine ⟨hmap, g.injOn_preimage_isoLocus.mono (fun y hy ↦ hV (hV' (hmap hy))), ?_⟩
  intro z hz
  obtain ⟨y, hy⟩ := (g ∣_ V).surjective ⟨z, hV' hz⟩
  have heq : g y.val = z :=
    (morphismRestrict_base_coe g V y).symm.trans (congrArg Subtype.val hy)
  exact ⟨y.val, (hfiber y.val).symm.trans (heq ▸ hz), heq⟩

end AlgebraicGeometry.Scheme.IdealSheafData
