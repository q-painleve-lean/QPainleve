/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor

import QPainleve.AlgebraicGeometry.Fiber
import QPainleve.AlgebraicGeometry.Morphisms.Etale.GlobalSections
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
import TauCeti.AlgebraicGeometry.IdealSheaf.Conductor.BaseChange
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
import TauCeti.AlgebraicGeometry.ResidueField
import TauCeti.FieldTheory.IsSepClosed
import TauCeti.RingTheory.Ideal.GoingUp
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.Jacobson.Ideal

/-!
# The branch residues at a node

Over a separably closed field, the scheme-theoretic fiber of the blowup at the
singular subscheme has two reduced points above each node. In the algebra of the
blowup over the local ring, the original local ring consists of the sections with
equal values at the two branches. The residue map onto the pair of fields
reflects units, as needed to glue a line with a specified identification of its
branch fibers.

See the [Stacks Project, Section 53.19](https://stacks.math.columbia.edu/tag/0C46).
-/

open CategoryTheory Limits TopologicalSpace IsLocalRing
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

private theorem singularLocus_stalkIdeal_eq_maximalIdeal
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) {x : X}
    (hx : letI := hnodal.syntomic; x ∈ (X.singularLocus k).support) :
    letI := hnodal.syntomic
    (X.singularLocus k).stalkIdeal x = maximalIdeal (X.presheaf.stalk x) := by
  let := hnodal.syntomic
  let J := X.singularLocus k
  obtain ⟨z, rfl⟩ := J.range_subschemeι.ge hx
  let g := J.subschemeι ≫ (X ↘ Spec (.of k))
  have : Etale g := X.etale_singularLocus_subschemeι_comp hnodal
  have : IsLocallyArtinian J.subscheme := .of_locallyQuasiFinite g
  have : IsRegular J.subscheme := IsRegular.of_smooth g
  have : IsReduced J.subscheme := inferInstance
  obtain ⟨U, hU, hzU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top z)
  have : IsArtinianRing Γ(J.subscheme, U) :=
    IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨U, hU⟩
  let := TopCat.Presheaf.algebra_section_stalk J.subscheme.presheaf ⟨z, hzU⟩
  let := hU.isLocalization_stalk ⟨z, hzU⟩
  have : IsArtinianRing (J.subscheme.presheaf.stalk z) :=
    IsArtinianRing.localization_artinian (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl _
  let h := J.subschemeι.stalkMap z
  have hzero : maximalIdeal (J.subscheme.presheaf.stalk z) = ⊥ :=
    isField_iff_maximalIdeal_eq.mp (IsArtinianRing.isField_of_isReduced_of_isLocalRing _)
  have hmax : RingHom.ker h.hom = maximalIdeal (X.presheaf.stalk (J.subschemeι z)) := by
    rw [RingHom.ker_eq_comap_bot, ← hzero]
    exact IsLocalRing.maximalIdeal_comap h.hom
  simpa only [h, Hom.ker_stalkMap_of_isClosedImmersion, IdealSheafData.ker_subschemeι] using hmax

private theorem singularLocus_comap_fromSpecStalk_eq
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) {x : X}
    (hx : letI := hnodal.syntomic; x ∈ (X.singularLocus k).support) :
    letI := hnodal.syntomic
    (X.singularLocus k).comap (X.fromSpecStalk x) =
      (Spec.map (X.residue x)).ker := by
  let := hnodal.syntomic
  let J := X.singularLocus k
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let V : X.affineOpens := ⟨U, hU⟩
  have hm : (J.ideal V).map (X.presheaf.germ V.val x hxU).hom =
      maximalIdeal (X.presheaf.stalk x) :=
    (J.stalkIdeal_eq_map V x hxU).symm.trans (singularLocus_stalkIdeal_eq_maximalIdeal hnodal hx)
  have hk : RingHom.ker (X.residue x).hom = maximalIdeal (X.presheaf.stalk x) :=
    ker_residue
  have hg := J.comap_SpecMap_fromSpec_eq_ofIdealTop hU (X.presheaf.germ U x hxU)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk, hg,
    Hom.ker_Spec_map]
  exact congrArg (fun I : Ideal (X.presheaf.stalk x) ↦ IdealSheafData.ofIdealTop
    (I.map (ΓSpecIso (X.presheaf.stalk x)).inv.hom)) (hm.trans hk.symm)

private theorem etale_fiberToSpecResidueField_blowupToBase_singularLocus
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) {x : X}
    (hx : letI := hnodal.syntomic; x ∈ (X.singularLocus k).support) :
    letI := hnodal.syntomic
    Etale ((X.singularLocus k).blowupToBase.fiberToSpecResidueField x) := by
  let := hnodal.syntomic
  let J := X.singularLocus k
  obtain ⟨z, rfl⟩ := J.range_subschemeι.ge hx
  have : Etale (X.branchSchemeToSingularLocus k) :=
    X.etale_branchSchemeToSingularLocus hnodal
  have : IsIso ((X.singularLocus k).subschemeι.residueFieldMap z) := inferInstance
  obtain ⟨e⟩ := (X.isPullback_branchScheme k).flip.nonempty_iso_fiberToSpecResidueField z
  have : Etale ((X.branchSchemeToSingularLocus k).fiberToSpecResidueField z) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have hb : Etale ((X.branchSchemeToSingularLocus k).fiberToSpecResidueField z ≫
      Spec.map ((X.singularLocus k).subschemeι.residueFieldMap z)) := inferInstance
  have hf : Etale (e.hom.left ≫ (X.singularLocus k).blowupToBase.fiberToSpecResidueField
      ((X.singularLocus k).subschemeι z)) := (Over.w e.hom).symm ▸ hb
  exact (MorphismProperty.cancel_left_of_respectsIso @Etale _ _).mp hf

private theorem conductor_eq_ker_residue_of_node
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) {x : X}
    (hx : letI := hnodal.syntomic; x ∈ (X.singularLocus k).support) :
    letI := hnodal.syntomic
    letI := X.isFinite_blowupToBase_singularLocus hnodal
    (pullback.snd (X.singularLocus k).blowupToBase (X.fromSpecStalk x)).conductor =
      (Spec.map (X.residue x)).ker := by
  let := hnodal.syntomic
  let := X.isFinite_blowupToBase_singularLocus hnodal
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  have hf : Flat (X.fromSpecStalk x) := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk]
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
    let := hU.isLocalization_stalk ⟨x, hxU⟩
    have hg : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
      rw [Flat.SpecMap_iff, ← X.presheaf.stalk_open_algebraMap ⟨x, hxU⟩,
        RingHom.flat_algebraMap_iff]
      exact IsLocalization.flat _ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    have : IsOpenImmersion hU.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec hU
    exact Flat.comp _ _
  have hc := Hom.conductor_eq_comap_of_isPullback
    (IsPullback.of_hasPullback (X.singularLocus k).blowupToBase (X.fromSpecStalk x))
  rw [conductor_blowupToBase_singularLocus hnodal] at hc
  exact hc.trans (singularLocus_comap_fromSpecStalk_eq hnodal hx)

private theorem isSepClosed_residueField_of_node [IsSepClosed k]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) {x : X}
    (hx : letI := hnodal.syntomic; x ∈ (X.singularLocus k).support) :
    IsSepClosed (X.residueField x) := by
  let := hnodal.syntomic
  let n := (X.singularLocus k).subschemeι
  obtain ⟨z, rfl⟩ := (IdealSheafData.range_subschemeι (X.singularLocus k)).ge hx
  have : Etale (n ≫ (X ↘ Spec (.of k))) := X.etale_singularLocus_subschemeι_comp hnodal
  have : IsSepClosed ((X.singularLocus k).subscheme.residueField z) :=
    Scheme.Hom.isSepClosed_residueField_of_formallyUnramified (n ≫ (X ↘ Spec (.of k))) z
  have : IsIso (n.residueFieldMap z) := inferInstance
  exact IsSepClosed.of_ringEquiv (asIso (n.residueFieldMap z)).commRingCatIsoToRingEquiv.symm

private theorem exists_branchFiber_sectionsEquiv [IsSepClosed k]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) {x : X}
    (hx : letI := hnodal.syntomic; x ∈ (X.singularLocus k).support) :
    letI := hnodal.syntomic
    let f := (X.singularLocus k).blowupToBase
    let K := X.residueField x
    let b := (ΓSpecIso K).inv ≫ (f.fiberToSpecResidueField x).appTop
    ∃ (o : Fin 2 ≃ f.fiber x) (e : Γ(f.fiber x, ⊤) ≃+* (K × K)),
      (∀ a : K, e (b a) = (a, a)) ∧
      ∀ t : Γ(f.fiber x, ⊤),
        ((e t).1 = 0 ↔ (f.fiber x).Γevaluation (o 0) t = 0) ∧
        ((e t).2 = 0 ↔ (f.fiber x).Γevaluation (o 1) t = 0) := by
  let := hnodal.syntomic
  let := X.isFinite_blowupToBase_singularLocus hnodal
  let f := (X.singularLocus k).blowupToBase
  let K := X.residueField x
  let F := f.fiber x
  let g := f.fiberToSpecResidueField x
  let b := (ΓSpecIso K).inv ≫ g.appTop
  have : Etale g := etale_fiberToSpecResidueField_blowupToBase_singularLocus hnodal hx
  have : IsFinite g := inferInstanceAs (IsFinite (pullback.snd f (X.fromSpecResidueField x)))
  have : IsSepClosed K := isSepClosed_residueField_of_node hnodal hx
  have hcard : Nat.card F = 2 := (Nat.card_congr (f.fiberHomeo x).toEquiv).trans
    (X.natCard_preimage_blowupToBase_singularLocus_eq_two_of_mem_support hnodal hx)
  have : Finite F := Nat.finite_of_card_ne_zero (hcard.trans_ne two_ne_zero)
  let o := (Finite.equivFinOfCardEq hcard).symm
  let d := g.finiteEtaleGlobalSectionsEquiv (k := K)
  let e := d.trans
    ((RingEquiv.piCongrLeft' (fun _ ↦ K) o.symm).trans (RingEquiv.piFinTwo (fun _ ↦ K)))
  have he (t : Γ(F, ⊤)) :
      e t = (d t (o 0), d t (o 1)) := by
    rfl
  refine ⟨o, e, fun a ↦ ?_, fun t ↦ ?_⟩
  · rw [he]
    exact Prod.ext (g.finiteEtaleGlobalSectionsEquiv_algebraMap (k := K) a (o 0))
      (g.finiteEtaleGlobalSectionsEquiv_algebraMap (k := K) a (o 1))
  · rw [he]
    exact ⟨g.finiteEtaleGlobalSectionsEquiv_apply_eq_zero_iff (k := K) t (o 0),
      g.finiteEtaleGlobalSectionsEquiv_apply_eq_zero_iff (k := K) t (o 1)⟩

private theorem ker_branchRestriction_eq_and_subset_range
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) {x : X}
    (hx : letI := hnodal.syntomic; x ∈ (X.singularLocus k).support) :
    letI := hnodal.syntomic
    let f := (X.singularLocus k).blowupToBase
    let Y := pullback f (X.fromSpecStalk x)
    let p : Y ⟶ Spec (X.presheaf.stalk x) := pullback.snd _ _
    let a := ((ΓSpecIso (X.presheaf.stalk x)).inv ≫ p.appTop).hom
    ∀ (j : f.fiber x ⟶ Y),
      IsPullback j (f.fiberToSpecResidueField x) p (Spec.map (X.residue x)) →
        RingHom.ker j.appTop.hom = (maximalIdeal (X.presheaf.stalk x)).map a ∧
        (RingHom.ker j.appTop.hom : Set Γ(Y, ⊤)) ⊆ a.range := by
  let := hnodal.syntomic
  let := X.isFinite_blowupToBase_singularLocus hnodal
  let f := (X.singularLocus k).blowupToBase
  let R := X.presheaf.stalk x
  let Y := pullback f (X.fromSpecStalk x)
  let p : Y ⟶ Spec R := pullback.snd _ _
  let i := Spec.map (X.residue x)
  let a := ((ΓSpecIso R).inv ≫ p.appTop).hom
  dsimp only
  intro j H
  have : IsFinite p := inferInstanceAs (IsFinite (pullback.snd f (X.fromSpecStalk x)))
  have : IsAffine Y := isAffine_of_isAffineHom p
  have hk : j.ker = i.ker.comap p := by
    rw [← IdealSheafData.ker_fst_of_isClosedImmersion i p, ← H.isoPullback_hom_fst,
      Hom.ker_comp_of_isIso]
  have hi : i.ker = IdealSheafData.ofIdealTop ((maximalIdeal R).map (ΓSpecIso R).inv.hom) := by
    rw [Hom.ker_Spec_map]
    exact congrArg (fun I : Ideal R ↦ IdealSheafData.ofIdealTop (I.map (ΓSpecIso R).inv.hom))
      ker_residue
  have hm : RingHom.ker j.appTop.hom = (maximalIdeal R).map a := by
    apply (IdealSheafData.equivOfIsAffine (X := Y)).symm.injective
    calc
      IdealSheafData.ofIdealTop (RingHom.ker j.appTop.hom) = j.ker :=
        (ker_of_isAffine j).symm
      _ = IdealSheafData.ofIdealTop ((maximalIdeal R).map a) := by
        dsimp only [a]
        rw [hk, hi, IdealSheafData.comap_ofIdealTop, Ideal.map_map, CommRingCat.hom_comp]
  refine ⟨hm, ?_⟩
  let g := p.appTop.hom
  let := g.toAlgebra
  have hc : TauCeti.Algebra.conductor Γ(Spec R, ⊤) Γ(Y, ⊤) =
      (maximalIdeal R).map (ΓSpecIso R).inv.hom := by
    apply IdealSheafData.equivOfIsAffine.symm.injective
    exact p.conductor_of_isAffine.symm.trans ((conductor_eq_ker_residue_of_node hnodal hx).trans hi)
  have hmap : (maximalIdeal R).map a ≤ g.range.conductor := by
    dsimp only [a]
    rw [CommRingCat.hom_comp, ← Ideal.map_map]
    apply Ideal.map_le_iff_le_comap.mpr
    exact hc ▸ (TauCeti.Algebra.comap_conductor_range
      (A := Γ(Spec R, ⊤)) (B := Γ(Y, ⊤))).ge
  have hrange : (g.range : Set Γ(Y, ⊤)) = a.range := by
    simpa only [RingHom.coe_range, a, CommRingCat.hom_comp, RingHom.coe_comp] using
      ((ConcreteCategory.bijective_of_isIso (ΓSpecIso R).inv).surjective.range_comp g).symm
  rw [hm, ← hrange]
  exact fun _ hb ↦ Subring.conductor_subset (hmap hb)

/-- At a node over a separably closed field, the two branch values of a section on the
blowup over the local spectrum can be prescribed independently. The value map reflects units.
The kernel of the value map is the extension of the maximal ideal of the local ring.
The local ring embeds as the equalizer of the two values, and its residue map is the diagonal
inside the two branch residue fields. -/
public theorem exists_branchResidue_eqLocus [IsSepClosed k]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) {x : X}
    (hx : letI := hnodal.syntomic; x ∈ (X.singularLocus k).support) :
    letI := hnodal.syntomic
    let f := (X.singularLocus k).blowupToBase
    let p := pullback.snd f (X.fromSpecStalk x)
    let R := X.presheaf.stalk x
    let K := X.residueField x
    let a := ((ΓSpecIso R).inv ≫ p.appTop).hom
    ∃ (j : f.fiber x ⟶ pullback f (X.fromSpecStalk x)) (o : Fin 2 ≃ f.fiber x)
      (e : Γ(f.fiber x, ⊤) ≃+* (K × K)),
      IsPullback j (f.fiberToSpecResidueField x) p (Spec.map (X.residue x)) ∧
      (∀ t : Γ(f.fiber x, ⊤),
        ((e t).1 = 0 ↔ (f.fiber x).Γevaluation (o 0) t = 0) ∧
        ((e t).2 = 0 ↔ (f.fiber x).Γevaluation (o 1) t = 0)) ∧
      let q := e.toRingHom.comp j.appTop.hom
      Function.Surjective q ∧ IsLocalHom q ∧ RingHom.ker q = (maximalIdeal R).map a ∧
      (∀ r : R, q (a r) = (X.residue x r, X.residue x r)) ∧
      Function.Injective a ∧ a.range =
        ((RingHom.fst K K).comp q).eqLocus ((RingHom.snd K K).comp q) := by
  let := hnodal.syntomic
  let := X.isFinite_blowupToBase_singularLocus hnodal
  let := X.surjective_blowupToBase_singularLocus hnodal
  let f := (X.singularLocus k).blowupToBase
  let Y := pullback f (X.fromSpecStalk x)
  let p : Y ⟶ Spec (X.presheaf.stalk x) := pullback.snd _ _
  let R := X.presheaf.stalk x
  let K := X.residueField x
  let s := f.fiberToSpecResidueField x
  let a := ((ΓSpecIso R).inv ≫ p.appTop).hom
  let i := Spec.map (X.residue x)
  let j := pullback.lift (f.fiberι x) (s ≫ i)
    (by rw [f.fiber_fac, fromSpecResidueField, Category.assoc])
  have H : IsPullback j s p i := by
    refine IsPullback.of_right (h₁₂ := pullback.fst _ _) ?_ (by simp [j, p])
      (IsPullback.of_hasPullback f (X.fromSpecStalk x))
    simpa only [j, pullback.lift_fst, s, Hom.fiber, Hom.fiberι, Hom.fiberToSpecResidueField,
      i, fromSpecResidueField] using (IsPullback.of_hasPullback f (X.fromSpecResidueField x))
  obtain ⟨o, e, he, hvanish⟩ := exists_branchFiber_sectionsEquiv hnodal hx
  let q := e.toRingHom.comp j.appTop.hom
  have : IsClosedImmersion j := MorphismProperty.of_isPullback H.flip inferInstance
  have : IsFinite p := inferInstanceAs (IsFinite (pullback.snd f (X.fromSpecStalk x)))
  have : IsAffine Y := isAffine_of_isAffineHom p
  have hsurj : Function.Surjective q :=
    e.surjective.comp (j.app_surjective ⊤ (isAffineOpen_top Y))
  have hker_eq : RingHom.ker q = RingHom.ker j.appTop.hom :=
    RingHom.ker_comp_of_injective _ (f := e.toRingHom) e.injective
  obtain ⟨hmap, hsubset⟩ := ker_branchRestriction_eq_and_subset_range hnodal hx j H
  have hker : RingHom.ker q = (maximalIdeal R).map a := hker_eq.trans hmap
  have hlocal : IsLocalHom q := by
    apply (RingHom.isLocalHom_iff_ker_le_jacobson hsurj).mpr
    rw [hker, ← Ideal.jacobson_bot]
    let := a.toAlgebra
    have hf : a.Finite := p.finite_appTop.comp
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (ΓSpecIso R).inv).surjective)
    let := RingHom.finite_algebraMap.mp hf
    exact Ideal.map_le_jacobson_of_isIntegral bot_le
      ((Ideal.jacobson_bot.trans (ringJacobson_eq_maximalIdeal R)).ge)
  have hdiag (r : R) : q (a r) = (X.residue x r, X.residue x r) := by
    have h := congrArg Scheme.Hom.appTop H.w
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
    have hh : (ΓSpecIso R).inv ≫ p.appTop ≫ j.appTop =
        X.residue x ≫ (ΓSpecIso K).inv ≫ s.appTop := by
      rw [h, ← ΓSpecIso_inv_naturality_assoc]
    exact (congrArg e (congrArg (fun g : R ⟶ Γ(f.fiber x, ⊤) ↦ g r) hh)).trans (he _)
  have hsub : (RingHom.ker q : Set Γ(Y, ⊤)) ⊆ a.range := hker_eq.symm ▸ hsubset
  have : Surjective p := inferInstanceAs (Surjective (pullback.snd f (X.fromSpecStalk x)))
  have : IsReduced X := hnodal.isReduced
  have : IsReduced (Spec R) := inferInstance
  have : IsSchemeTheoreticallyDominant p := .of_isDominant p
  have hinj : Function.Injective a :=
    (p.app_injective ⊤).comp (ConcreteCategory.bijective_of_isIso (ΓSpecIso R).inv).injective
  have hrange : a.range = ((RingHom.fst K K).comp q).eqLocus ((RingHom.snd K K).comp q) := by
    ext b
    simp only [RingHom.mem_eqLocus, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_snd]
    constructor
    · rintro ⟨r, rfl⟩
      rw [hdiag]
    · intro hb
      obtain ⟨r, hr⟩ := X.residue_surjective x (q b).1
      have hqb : b - a r ∈ RingHom.ker q := by
        rw [RingHom.mem_ker, map_sub, hdiag, hr, sub_eq_zero]
        exact Prod.ext rfl hb.symm
      obtain ⟨c, hc⟩ := hsub hqb
      exact ⟨c + r, by rw [map_add, hc, sub_add_cancel]⟩
  exact ⟨j, o, e, H, hvanish, hsurj, hlocal, hker, hdiag, hinj, hrange⟩

end AlgebraicGeometry.Scheme
