/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import TauCeti.AlgebraicGeometry.IdealSheaf.Conductor.Basic

import QPainleve.Topology.Sheaves.Pullback

import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.RingTheory.Ideal.Quotient.Pullback

/-!
# Sections of conductor squares

For a finite scheme-theoretically dominant morphism, the structure ring over
an affine open is the fiber product of the section rings of its inverse image
and its conductor subscheme over their common closed subscheme. These pullbacks
assemble into a pullback of direct images of the structure sheaves.
The affine calculation uses Tau Ceti's quotient pullback and conductor APIs.

See the Stacks Project, Proposition 37.67.3, Tag 0E25, for the corresponding
structure sheaf formula in the construction of scheme pushouts.
-/

public section

open CategoryTheory Limits
open AlgebraicGeometry TopologicalSpace
open TopCat.Presheaf

namespace CategoryTheory.IsPullback

universe u

/-- On any affine open, a conductor square gives a pullback of section rings. -/
theorem isPullback_app_of_ker_eq_conductor {P Y Z X : Scheme.{u}}
    {j : P ⟶ Y} {g : P ⟶ Z} {f : Y ⟶ X} {i : Z ⟶ X}
    [IsFinite f] [IsSchemeTheoreticallyDominant f] [IsClosedImmersion i]
    (h : IsPullback j g f i) (hi : i.ker = f.conductor) (U : X.affineOpens) :
    IsPullback (f.app U.val) (i.app U.val) (j.app (f ⁻¹ᵁ U.val))
      (g.appLE (i ⁻¹ᵁ U.val) (j ⁻¹ᵁ (f ⁻¹ᵁ U.val))
        (by rw [← Scheme.Hom.comp_preimage, h.w, Scheme.Hom.comp_preimage])) := by
  let a := f.app U.val
  let b := i.app U.val
  let c := j.app (f ⁻¹ᵁ U.val)
  let d := g.appLE (i ⁻¹ᵁ U.val) (j ⁻¹ᵁ (f ⁻¹ᵁ U.val))
    (by rw [← Scheme.Hom.comp_preimage, h.w, Scheme.Hom.comp_preimage])
  suffices IsPullback a b c d from this
  have hw : a ≫ c = b ≫ d := by
    let V := j ⁻¹ᵁ (f ⁻¹ᵁ U.val)
    have app_congr {r s : P ⟶ X} (e : r = s) (er : V ≤ r ⁻¹ᵁ U.val)
        (es : V ≤ s ⁻¹ᵁ U.val) : r.appLE U.val V er = s.appLE U.val V es := by
      subst s
      rfl
    calc
      _ = (j ≫ f).appLE U.val V le_rfl :=
        (Scheme.Hom.comp_app j f U.val).symm.trans (Scheme.Hom.appLE_eq_app _).symm
      _ = (g ≫ i).appLE U.val V (by rw [← h.w]; rfl) := app_congr h.w _ _
      _ = _ := Scheme.Hom.comp_appLE g i _ _ _
  -- The conductor is a common ideal of the two affine section rings.
  let I := RingHom.ker b.hom
  let J := RingHom.ker c.hom
  let V : Y.affineOpens := ⟨f ⁻¹ᵁ U.val, U.property.preimage f⟩
  have : IsClosedImmersion j := MorphismProperty.of_isPullback h.flip inferInstance
  have hI : I = letI := a.hom.toAlgebra; TauCeti.Algebra.conductor Γ(X, U) Γ(Y, V) := by
    have he := congrArg (fun I : X.IdealSheafData ↦ I.ideal U) hi
    rw [i.ker_apply, f.conductor_ideal] at he
    exact he
  have hJ : J = I.map a.hom := by
    have hk := congrArg (fun I : Y.IdealSheafData ↦ I.ideal V)
      (Scheme.IdealSheafData.ker_eq_comap_of_isPullback i h)
    rw [j.ker_apply, Scheme.IdealSheafData.ideal_comap_of_le i.ker f U V le_rfl,
      i.ker_apply, ← Scheme.Hom.app_eq_appLE] at hk
    exact hk
  let q := Ideal.quotientMap J a.hom (hJ ▸ Ideal.le_comap_map)
  have hq : IsPullback a (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (Ideal.Quotient.mk J)) (CommRingCat.ofHom q) := by
    apply (RingHom.isPullback_quotient_iff a.hom J (hJ ▸ Ideal.le_comap_map)).mpr
    constructor
    · rw [(RingHom.injective_iff_ker_eq_bot _).mp
        (f.app_injective U.val), bot_inf_eq]
    · let := a.hom.toAlgebra
      rw [hJ, hI, ← TauCeti.Algebra.comap_conductor_range]
      intro b hb
      have hb' := Ideal.map_comap_le (f := a.hom) hb
      obtain ⟨a, ha⟩ := Subring.conductor_subset hb'
      exact ⟨a, Ideal.mem_comap.mpr (ha.symm ▸ hb'), ha⟩
  have hsI : Function.Surjective b := i.app_surjective U.val U.property
  have hsJ : Function.Surjective c := j.app_surjective V.val V.property
  let eI := (RingHom.quotientKerEquivOfSurjective hsI).toCommRingCatIso
  let eJ := (RingHom.quotientKerEquivOfSurjective hsJ).toCommRingCatIso
  let π := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have ha : π ≫ eI.hom = b := CommRingCat.hom_ext
    (RingHom.ext (RingHom.quotientKerEquivOfSurjective_apply_mk hsI))
  have hb : CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ eJ.hom = c :=
    CommRingCat.hom_ext (RingHom.ext (RingHom.quotientKerEquivOfSurjective_apply_mk hsJ))
  refine hq.of_iso (Iso.refl _) (Iso.refl _) eI eJ
    (by simp) (by simpa using ha) (by simpa using hb) ?_
  have : Epi π := ConcreteCategory.epi_of_surjective π Ideal.Quotient.mk_surjective
  rw [← cancel_epi π, ← Category.assoc, ← Category.assoc, hq.w.symm, Category.assoc, ha, hb]
  exact hw

/-- The structure presheaf of the base is the pullback of the direct images from
the finite source and the conductor subscheme over the direct image from their
fiber product. The four presheaves are sheaves, and the formula applies on all opens. -/
theorem isPullback_presheaf_of_ker_eq_conductor {P Y Z X : Scheme.{u}}
    {j : P ⟶ Y} {g : P ⟶ Z} {f : Y ⟶ X} {i : Z ⟶ X}
    [IsFinite f] [IsSchemeTheoreticallyDominant f] [IsClosedImmersion i]
    (h : IsPullback j g f i) (hi : i.ker = f.conductor) :
    IsPullback f.c i.c ((pushforward _ f.base).map j.c)
      (((pushforward _ i.base).map g.c) ≫
        (pushforwardEq (congrArg (fun m : P ⟶ X ↦ m.base) h.w.symm) P.presheaf).hom) := by
  let F := (TopCat.Sheaf.pushforward _ f.base).obj Y.sheaf
  let G := (TopCat.Sheaf.pushforward _ i.base).obj Z.sheaf
  let H := (TopCat.Sheaf.pushforward _ (j ≫ f).base).obj P.sheaf
  let a : X.sheaf ⟶ F := ObjectProperty.homMk f.c
  let b : X.sheaf ⟶ G := ObjectProperty.homMk i.c
  let c : F ⟶ H := ObjectProperty.homMk ((pushforward _ f.base).map j.c)
  let d : G ⟶ H := ObjectProperty.homMk
    (((pushforward _ i.base).map g.c) ≫
      (pushforwardEq (congrArg (fun m : P ⟶ X ↦ m.base) h.w.symm) P.presheaf).hom)
  -- The equality of composites identifies the two preimages of each open in P.
  have hd (U : X.Opens) :
      d.hom.app (Opposite.op U) = g.appLE (i ⁻¹ᵁ U) (j ⁻¹ᵁ (f ⁻¹ᵁ U))
        (by rw [← Scheme.Hom.comp_preimage, h.w, Scheme.Hom.comp_preimage]) := by
    simp only [d, ObjectProperty.homMk_hom, Scheme.Hom.appLE]
    rfl
  have hb : Opens.IsBasis (Set.range (fun U : X.affineOpens ↦ U.val)) := by
    simpa using X.isBasis_affineOpens
  have hU (U : X.affineOpens) :
      IsPullback (a.hom.app (Opposite.op U.val)) (b.hom.app (Opposite.op U.val))
        (c.hom.app (Opposite.op U.val)) (d.hom.app (Opposite.op U.val)) := by
    rw [hd]
    exact h.isPullback_app_of_ker_eq_conductor hi U
  have hsq : CommSq a b c d := ⟨by
    apply (TopCat.Sheaf.forget _ _).map_injective
    apply TopCat.Sheaf.hom_ext (F := X.presheaf) (F' := H) hb
    intro U
    exact (hU U).w⟩
  exact (TopCat.Sheaf.isPullback_of_isPullback_basis hsq hb hU).map
    (sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat)

end CategoryTheory.IsPullback
