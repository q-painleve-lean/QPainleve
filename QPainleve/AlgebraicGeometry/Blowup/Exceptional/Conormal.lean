/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Fiber
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.TwistingSheaf
import QPainleve.AlgebraicGeometry.Blowup.RegularPair
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.IdealSheaf.Pullback
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Conormal bundle of a point blowup

At a regular closed point of local dimension two, the exceptional fiber is the projective
line over the residue field, with conormal bundle `𝒪(1)`. The flat comparison with the
blowup of the local ring transports the Rees twist to the actual exceptional divisor.

## References

* [The Stacks Project, Lemma 54.3.1](https://stacks.math.columbia.edu/tag/0AGQ).
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open TauCeti.AlgebraicGeometry QPainleve reesAlgebra

universe u

namespace AlgebraicGeometry.Scheme

open IdealSheafData

variable {X : Scheme.{u}}

private abbrev pointIdeal (p : X) : X.IdealSheafData :=
  vanishingIdeal ⟨closure {p}, isClosed_closure⟩

private theorem exists_isPullback_localBlowup (p : X) :
    let J := pointIdeal p
    ∃ g : Proj (grade (IsLocalRing.maximalIdeal (X.presheaf.stalk p))) ⟶ J.blowup,
      IsPullback g (Proj.toSpecCoeff _) J.blowupToBase (X.fromSpecStalk p) ∧ Flat g := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  let R := X.presheaf.stalk p
  let I := (pointIdeal p).ideal ⟨U, hU⟩
  let : Algebra Γ(X, U) R := (X.presheaf.germ U p hpU).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨p, hpU⟩
  have : Module.Flat Γ(X, U) R :=
    IsLocalization.flat R (hU.primeIdealOf ⟨p, hpU⟩).asIdeal.primeCompl
  have hI : I.map (algebraMap Γ(X, U) R) = IsLocalRing.maximalIdeal R := by
    simpa only [I, R, RingHom.algebraMap_toAlgebra, TopCat.Presheaf.stalkSpecializes_refl,
      CommRingCat.hom_id, Ideal.comap_id] using
      map_ideal_vanishingIdeal_closure_singleton_of_specializes
        (U := ⟨U, hU⟩) hpU (specializes_refl p)
  have h : ∃ g : Proj (grade (I.map (algebraMap Γ(X, U) R))) ⟶ Proj (grade I),
      IsPullback g (Proj.toSpecCoeff _) (Proj.toSpecCoeff (grade I))
        (Spec.map (X.presheaf.germ U p hpU)) :=
    ⟨_, isPullback_affineBlowup_of_flat I R⟩
  rw [hI] at h
  obtain ⟨g, hg⟩ := h
  have hStalk : X.fromSpecStalk p = Spec.map (X.presheaf.germ U p hpU) ≫ hU.fromSpec :=
    (hU.fromSpecStalk_eq_fromSpecStalk hpU).symm
  have : Flat (Spec.map (X.presheaf.germ U p hpU)) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : IsOpenImmersion (IsAffineOpen.fromSpec hU) := IsAffineOpen.isOpenImmersion_fromSpec hU
  have : Flat (X.fromSpecStalk p) := hStalk ▸ inferInstance
  have hs := hg.paste_horiz ((pointIdeal p).isPullback_blowupChart_fromSpec hU).flip
  rw [← hStalk] at hs
  exact ⟨_, hs, MorphismProperty.of_isPullback hs.flip ‹Flat (X.fromSpecStalk p)›⟩

private theorem exists_isPullback_blowupExceptional (p : X) (hp : IsClosed {p}) :
    let J := pointIdeal p
    let E := J.comap J.blowupToBase
    ∃ t : E.subscheme ⟶ Spec (X.residueField p),
      IsPullback E.subschemeι t J.blowupToBase (X.fromSpecResidueField p) := by
  dsimp only
  let J := pointIdeal p
  let π := J.blowupToBase
  let r := X.fromSpecResidueField p
  have : IsClosedImmersion r := isClosed_singleton_iff_isClosedImmersion.mp hp
  -- The residue-field immersion has the reduced induced structure at the closed point.
  have hred : IsReduced r.ker.subscheme := isReduced_of_isOpenImmersion (inv r.toImage)
  have hsupport : r.ker.support = (⟨closure {p}, isClosed_closure⟩ : Closeds X) := by
    apply SetLike.coe_injective
    rw [r.support_ker, X.range_fromSpecResidueField]
    rfl
  have hr : J = r.ker :=
    (congrArg vanishingIdeal hsupport.symm).trans
      (vanishingIdeal_support.trans (r.ker.isReduced_subscheme_iff_radical_eq.mp hred))
  let i := IsClosedImmersion.lift J.subschemeι r (J.ker_subschemeι.trans hr).le
  have hi : i ≫ J.subschemeι = r := IsClosedImmersion.lift_fac ..
  have : IsIso i := IsClosedImmersion.isIso_of_ker_eq r J.subschemeι i hi
    (J.ker_subschemeι.trans hr).symm
  let t := (J.comapIso π).hom ≫ pullback.snd _ _ ≫ inv i
  have hE : IsPullback (J.comap π).subschemeι t π r := by
    refine (IsPullback.of_hasPullback π J.subschemeι).of_iso'
      (J.comapIso π) (.refl _) (asIso i) (.refl _) ?_ ?_ (by simp) ?_
    · simp
    · simp only [t, Category.assoc, asIso_hom, IsIso.inv_hom_id, Category.comp_id]
    · simpa only [asIso_hom, Iso.refl_hom, Category.comp_id] using hi
  exact ⟨t, hE⟩

/-- The exceptional divisor of a blowup at a regular closed point of local dimension two
is the projective line over the residue field, and its conormal line bundle is `𝒪(1)`.
The square with the blowup morphism and the closed point is cartesian. -/
theorem exists_iso_projectiveLine_blowupExceptional_conormal (p : X) (hp : IsClosed {p})
    [IsRegularLocalRing (X.presheaf.stalk p)] (hdim : ringKrullDim (X.presheaf.stalk p) = 2) :
    let J := vanishingIdeal (⟨closure {p}, isClosed_closure⟩ : Closeds X)
    let E := J.comap J.blowupToBase
    ∃ e : projectiveLine (X.residueField p) ≅ E.subscheme,
      IsPullback (e.hom ≫ E.subschemeι) (projectiveLine (X.residueField p) ↘
        Spec (.of (X.residueField p))) J.blowupToBase (X.fromSpecResidueField p) ∧
      Nonempty ((Scheme.Modules.pullback (e.hom ≫ E.subschemeι)).obj E.sheaf ≅
        Proj.twistingSheaf
          (TauCeti.SymmetricAlgebra.homogeneousSubmodule (X.residueField p)
            (Fin 2 → X.residueField p)) 1) := by
  dsimp only
  let J := pointIdeal p
  let π := J.blowupToBase
  let E := J.comap π
  let R := X.presheaf.stalk p
  let I := IsLocalRing.maximalIdeal R
  let π' := Proj.toSpecCoeff (grade I)
  let E' := affineBlowupExceptionalIdeal R I
  let r := X.fromSpecResidueField p
  let f := X.fromSpecStalk p
  let q := Spec.map (X.residue p)
  let s : projectiveLine (X.residueField p) ⟶ Spec (X.residueField p) :=
    projectiveLine (X.residueField p) ↘ Spec (.of (X.residueField p))
  have hq : q ≫ f = r := (rfl)
  obtain ⟨a, b, hspan, hab, _, _⟩ := exists_affineBlowupChartOfSpanPair_cover (A := R) hdim
  have hI : Ideal.ofList [a, b] = I := by simpa [Ideal.span_insert] using hspan
  let e' := (affineBlowupExceptionalIsoProjectiveLine hab hI).symm
  let l := e'.hom ≫ E'.subschemeι
  have hL : IsPullback l s π' q := isPullback_affineBlowupExceptionalIsoProjectiveLine hab hI
  obtain ⟨g, hg, hflat⟩ := exists_isPullback_localBlowup p
  have hg' : IsPullback g π' π f := hg
  have hF : IsPullback (l ≫ g) s π r := hq ▸ hL.paste_horiz hg'
  obtain ⟨t, hE⟩ := exists_isPullback_blowupExceptional p hp
  let e := hF.isoIsPullback _ _ hE
  have he : e.hom ≫ E.subschemeι = l ≫ g := hF.isoIsPullback_hom_fst _ _ hE
  have ht : e.hom ≫ t = s := hF.isoIsPullback_hom_snd _ _ hE
  refine ⟨e, he.symm ▸ hF, ⟨?_⟩⟩
  -- The stalk map is a monomorphism, so pasting with it preserves the local fiber square.
  have hq' : IsPullback q (𝟙 _) f r :=
    IsPullback.of_vert_isIso_mono ⟨by simp [hq]⟩
  have hOuter : IsPullback l (e.hom ≫ t) (g ≫ π) r := by
    rw [ht, hg'.w]
    have hs : s ≫ 𝟙 (Spec (X.residueField p)) = s := Category.comp_id s
    exact hs ▸ hL.paste_vert hq'
  have hCart := hOuter.of_bot he.symm hE
  have hker : E.comap g = E' := by
    rw [← E.ker_subschemeι, ← ker_eq_comap_of_isPullback E.subschemeι hCart,
      Scheme.Hom.ker_comp_of_isIso, ker_subschemeι]
  letI := hflat
  exact (Modules.pullbackCongr he).app E.sheaf ≪≫
    (Modules.pullbackComp l g).symm.app E.sheaf ≪≫
    (Modules.pullback l).mapIso (asIso (E.pullbackSheafHom g) ≪≫
      eqToIso (congrArg IdealSheafData.sheaf hker) ≪≫
      affineBlowupExceptionalIdealIsoTwistingSheaf R I) ≪≫
    affineBlowupExceptionalProjectiveLinePullbackTwistingSheafIso hab hI 1

/-- The exceptional divisor of the blowup at a regular closed point of local dimension two
is an exceptional curve of the first kind. -/
theorem isExceptionalCurveOfFirstKind_blowup_closed_point (p : X) (hp : IsClosed {p})
    [IsRegularLocalRing (X.presheaf.stalk p)] (hdim : ringKrullDim (X.presheaf.stalk p) = 2) :
    let J := vanishingIdeal (⟨closure {p}, isClosed_closure⟩ : Closeds X)
    (J.comap J.blowupToBase).IsExceptionalCurveOfFirstKind := by
  obtain ⟨e, _, ⟨h⟩⟩ := exists_iso_projectiveLine_blowupExceptional_conormal p hp hdim
  refine ⟨(pointIdeal p).isEffectiveCartier_comap_blowupToBase,
    X.residueField p, inferInstance, e, ⟨?_⟩⟩
  simpa only [InvertibleSheaf.pullback_obj_obj, IsEffectiveCartier.toInvertibleSheaf_obj] using h

end AlgebraicGeometry.Scheme
