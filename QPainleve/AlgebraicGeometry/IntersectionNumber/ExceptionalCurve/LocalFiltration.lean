/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.GradedSections
public import QPainleve.AlgebraicGeometry.IdealSheaf.Completion
public import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop

import QPainleve.RingTheory.AdicCompletion.IdealFiltration
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
import TauCeti.RingTheory.AdicCompletion.Algebra

/-!
# Ideal powers of a local exceptional contraction

For a proper exceptional contraction to a Noetherian local spectrum, pullback
identifies the powers of the maximal ideal with the ideals of functions that
vanish on the corresponding thickenings of the exceptional fiber. This identifies
each positive maximal-ideal quotient of the base or its completion with the ring of functions
on its thickened fiber.

This is the ideal-filtration comparison in
[Stacks Project, Lemma 54.16.3](https://stacks.math.columbia.edu/tag/0C2K).
-/

public noncomputable section

open CategoryTheory Limits IsLocalRing
open TauCeti.AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of R)) {E : X.IdealSheafData}

local notation "𝔪" => maximalIdeal R
local notation "R̂" => AdicCompletion 𝔪 R
local notation "𝔫" => ofIdealTop (Ideal.map
  (CommRingCat.Hom.hom (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of R)))) (maximalIdeal R))

private abbrev quotientSpec (n : ℕ) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ n)))

private abbrev fiberSectionsMap (n : ℕ) :=
  ((Scheme.ΓSpecIso _).inv ≫ (pullback.snd f (quotientSpec (R := R) n)).appTop).hom

private abbrev baseSectionsMap :=
  (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop

private theorem comap_sections_one (hE : E.IsExceptionalCurveOfFirstKind)
    (hI : (𝔫).comap f = E) :
    ((E ^ 1).sections ⊤).comap (baseSectionsMap f).hom = 𝔪 := by
  symm
  apply (maximalIdeal.isMaximal R).eq_of_le
  · rw [pow_one, ne_eq, Ideal.eq_top_iff_one]
    intro h
    have hz : E.subschemeι.appTop 1 = 0 := by
      have ht : E.subschemeι.appTop ((baseSectionsMap f) 1) = 0 :=
        (E.mem_sections_iff).mp h
      simpa only [map_one] using ht
    obtain ⟨k, _, e, _⟩ := hE.exists_iso
    let x := e.hom (projectiveLine.infinity k)
    have he := congrArg (E.subscheme.presheaf.Γgerm x) hz
    exact one_ne_zero (by simpa only [map_one, map_zero] using he)
  · rw [← f.ker_fiberSectionsMap_comp_quotient hI 1, ← RingHom.comap_ker]
    have h : RingHom.ker (Ideal.Quotient.mk (𝔪 ^ 1)) = 𝔪 := Ideal.mk_ker.trans (pow_one _)
    exact h.symm.le.trans (Ideal.comap_mono bot_le)

private theorem sections_pow_sup_of_exceptional_contraction [IsNoetherianRing R]
    [IsProper f] [IsIso f.appTop] (hE : E.IsExceptionalCurveOfFirstKind)
    (hI : (𝔫).comap f = E) (hU : (𝔫).support.compl ≤ f.isoLocus) (n : ℕ) :
    𝔪 ^ n ⊔ ((E ^ (n + 1)).sections ⊤).comap (baseSectionsMap f).hom =
      ((E ^ n).sections ⊤).comap (baseSectionsMap f).hom := by
  let α := (asIso (baseSectionsMap f)).commRingCatIsoToRingEquiv
  let J (i : ℕ) := ((E ^ i).sections ⊤).comap (baseSectionsMap f).hom
  have hJ (i : ℕ) : J i = ((E ^ i).sections ⊤).map α.symm :=
    (Ideal.map_symm α).symm
  have hmul (i : ℕ) : J i * J 1 ⊔ J (i + 1 + 1) = J (i + 1) := by
    rw [hJ, hJ 1, hJ, hJ, ← Ideal.map_mul, ← Ideal.map_sup,
      hE.sections_mul_sup_of_exceptional_contraction f hI hU i 1]
  have h₁ : J 1 = 𝔪 := comap_sections_one f hE hI
  suffices ∀ i : ℕ, 𝔪 ^ i ⊔ J (i + 1) = J i from this n
  intro i
  induction i with
  | zero =>
    have htop : (⊤ : X.IdealSheafData).sections (⊤ : X.Opens) = ⊤ := by
      rw [Ideal.eq_top_iff_one, mem_sections_iff]
      let Z := (⊤ : X.IdealSheafData).subscheme
      have : IsEmpty Z := inferInstanceAs (IsEmpty (⊤ : X.IdealSheafData).subscheme)
      have : IsEmpty (⊤ : Z.Opens) := ⟨fun x ↦ isEmptyElim x.val⟩
      exact section_ext_of_isEmpty (M := Scheme.Modules.unit Z) (U := ⊤) _ _
    simp only [J, pow_zero, one_eq_top, htop, Ideal.comap_top, Ideal.one_eq_top, top_sup_eq]
  | succ i ih =>
    have hle : J (i + 1) * 𝔪 ≤ J (i + 1 + 1) :=
      h₁ ▸ le_sup_left.trans_eq (hmul (i + 1))
    calc
      𝔪 ^ (i + 1) ⊔ J (i + 1 + 1) =
          (𝔪 ^ i ⊔ J (i + 1)) * 𝔪 ⊔ J (i + 1 + 1) := by
        rw [Ideal.sup_mul, pow_succ, sup_assoc, sup_eq_right.mpr hle]
      _ = J (i + 1) := by rw [ih, ← h₁, hmul]

/-- The functions vanishing on each exceptional thickening of a local contraction
pull back from exactly the corresponding power of the maximal ideal. -/
theorem comap_sections_pow_of_exceptional_contraction [IsNoetherianRing R]
    [IsProper f] [IsIso f.appTop]
    (hE : E.IsExceptionalCurveOfFirstKind) (hI : (𝔫).comap f = E)
    (hU : (𝔫).support.compl ≤ f.isoLocus) (n : ℕ) :
    ((E ^ n).sections ⊤).comap
      ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom = 𝔪 ^ n := by
  let J (i : ℕ) := ((E ^ i).sections ⊤).comap (baseSectionsMap f).hom
  refine Ideal.eq_pow_of_sup_succ_of_adicCompletion 𝔪 J
    (sections_pow_sup_of_exceptional_contraction f hE hI hU) (fun a ha ↦ ?_) n
  have : IsSchemeTheoreticallyDominant f :=
    (isSchemeTheoreticallyDominant_iff_appTop_injective f).mpr
      (ConcreteCategory.bijective_of_isIso f.appTop).injective
  apply f.injective_completionToFiberThickeningLimit
  apply Concrete.limit_ext
  intro j
  obtain ⟨j⟩ := j
  have he := ConcreteCategory.congr_hom (f.completionToFiberThickeningLimit_π j) a
  have hle : (J (j + 1)).map (Ideal.Quotient.mk (𝔪 ^ (j + 1))) ≤
      RingHom.ker (fiberSectionsMap f (j + 1)) := by
    rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker,
      f.ker_fiberSectionsMap_comp_quotient hI]
  have hz : f.completionToFiberThickening j a = 0 := by
    rw [f.completionToFiberThickening_apply]
    exact hle (ha (j + 1))
  rw [map_zero, map_zero]
  exact he.trans hz

private theorem injective_fiberSectionsMap [IsNoetherianRing R]
    [IsProper f] [IsIso f.appTop]
    (hE : E.IsExceptionalCurveOfFirstKind) (hI : (𝔫).comap f = E)
    (hU : (𝔫).support.compl ≤ f.isoLocus) (n : ℕ) :
    Function.Injective (fiberSectionsMap f (n + 1)) := by
  refine (injective_iff_map_eq_zero (fiberSectionsMap f (n + 1))).mpr ?_
  intro a ha
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hr : r ∈ RingHom.ker ((fiberSectionsMap f (n + 1)).comp
      (Ideal.Quotient.mk (𝔪 ^ (n + 1)))) := ha
  rw [f.ker_fiberSectionsMap_comp_quotient hI,
    comap_sections_pow_of_exceptional_contraction f hE hI hU] at hr
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hr

private theorem surjective_fiberSectionsMap [IsNoetherianRing R] [IsProper f] [IsIso f.appTop]
    (hE : E.IsExceptionalCurveOfFirstKind) (hI : (𝔫).comap f = E)
    (hU : (𝔫).support.compl ≤ f.isoLocus) (n : ℕ) :
    Function.Surjective (fiberSectionsMap f n) := by
  let a := pullback.fst f (quotientSpec (R := R) n)
  let i := (E ^ n).subschemeι
  have : IsClosedImmersion (quotientSpec (R := R) n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion a := inferInstanceAs (IsClosedImmersion (pullback.fst f _))
  have h : i.ker = a.ker :=
    (ker_subschemeι _).trans (f.ker_fst_fiberThickening hI n).symm
  let b := IsClosedImmersion.lift i a h.le
  have : IsIso b := IsClosedImmersion.isIso_lift i a h
  have : IsIso b.appTop := Scheme.Γ.map_isIso b.op
  have hfac : b ≫ i = a := IsClosedImmersion.lift_fac _ _ _
  have ha : Function.Surjective a.appTop := by
    rw [← hfac, Scheme.Hom.comp_appTop]
    exact (ConcreteCategory.bijective_of_isIso b.appTop).surjective.comp
      (hE.surjective_appTop_subschemeι_pow_of_contraction f hI hU n)
  suffices Function.Surjective ((fiberSectionsMap f n).comp (Ideal.Quotient.mk (𝔪 ^ n))) from
    Function.Surjective.of_comp this
  rw [f.fiberSectionsMap_comp_quotient]
  exact ha.comp (ConcreteCategory.bijective_of_isIso (baseSectionsMap f)).surjective

/-- Pullback identifies the `(n + 1)`st quotient of the local base of a proper
exceptional contraction with the functions on the corresponding infinitesimal fiber. -/
def fiberThickeningRingEquiv [IsNoetherianRing R]
    [IsProper f] [IsIso f.appTop]
    (hE : E.IsExceptionalCurveOfFirstKind) (hI : (𝔫).comap f = E)
    (hU : (𝔫).support.compl ≤ f.isoLocus) (n : ℕ) :
    R ⧸ (𝔪 ^ (n + 1)) ≃+*
      Γ(pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 1))))), ⊤) :=
  RingEquiv.ofBijective (fiberSectionsMap f (n + 1))
    ⟨injective_fiberSectionsMap f hE hI hU n, surjective_fiberSectionsMap f hE hI hU (n + 1)⟩

/-- The ring equivalence on infinitesimal fibers evaluates by pulling back from the base. -/
@[simp]
theorem fiberThickeningRingEquiv_apply [IsNoetherianRing R]
    [IsProper f] [IsIso f.appTop]
    (hE : E.IsExceptionalCurveOfFirstKind) (hI : (𝔫).comap f = E)
    (hU : (𝔫).support.compl ≤ f.isoLocus) (n : ℕ) (r : R ⧸ (𝔪 ^ (n + 1))) :
    fiberThickeningRingEquiv f hE hI hU n r =
      (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 1)))))).appTop
        ((Scheme.ΓSpecIso _).inv r) :=
  (rfl)

variable [IsNoetherianRing R] [IsProper f] [IsIso f.appTop]

/-- The kernel of the map from the completed local base ring to functions on the
`(n + 1)`st thickening of the exceptional fiber is the `(n + 1)`st power of the
maximal ideal of the completion. -/
theorem ker_completionToFiberThickening (hE : E.IsExceptionalCurveOfFirstKind)
    (hI : (𝔫).comap f = E) (hU : (𝔫).support.compl ≤ f.isoLocus) (n : ℕ) :
    RingHom.ker (f.completionToFiberThickening n) = maximalIdeal R̂ ^ (n + 1) := by
  rw [f.ker_completionToFiberThickening_eq_map hI n,
    hE.comap_sections_pow_of_exceptional_contraction f hI hU, Ideal.map_pow,
    ← AdicCompletion.maximalIdeal_eq_map]

/-- The functions on the `(n + 1)`st thickening of the exceptional fiber are the
`(n + 1)`st truncation of the completed local base ring. The equivalence is induced by
pullback from the base. -/
def completionQuotientEquivFiberThickening (hE : E.IsExceptionalCurveOfFirstKind)
    (hI : (𝔫).comap f = E) (hU : (𝔫).support.compl ≤ f.isoLocus) (n : ℕ) :
    (R̂ ⧸ maximalIdeal R̂ ^ (n + 1)) ≃+*
      Γ(pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 1))))), ⊤) :=
  let e := Ideal.quotEquivOfEq
    (show maximalIdeal R̂ ^ (n + 1) = (𝔪 ^ (n + 1)).map (algebraMap R R̂) from
      by rw [Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map])
  (e.trans (AdicCompletion.quotientMapPowAlgEquiv
    (Ideal.fg_of_isNoetherianRing 𝔪) (n + 1)).toRingEquiv).trans
      (fiberThickeningRingEquiv f hE hI hU n)

/-- The finite-level equivalence sends the class of a completed element to its pullback
on the infinitesimal fiber. -/
@[simp]
theorem completionQuotientEquivFiberThickening_mk (hE : E.IsExceptionalCurveOfFirstKind)
    (hI : (𝔫).comap f = E) (hU : (𝔫).support.compl ≤ f.isoLocus) (n : ℕ) (r : R̂) :
    hE.completionQuotientEquivFiberThickening f hI hU n (Ideal.Quotient.mk _ r) =
      f.completionToFiberThickening n r := by
  simp only [completionQuotientEquivFiberThickening, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    AlgEquiv.coe_toRingEquiv, AdicCompletion.quotientMapPowAlgEquiv_mk,
    fiberThickeningRingEquiv_apply, Scheme.Hom.completionToFiberThickening_apply]

/-- Under the finite-level equivalences, the quotient transition is restriction
along the inclusion of infinitesimal fibers. -/
theorem completionQuotientEquivFiberThickening_factor (hE : E.IsExceptionalCurveOfFirstKind)
    (hI : (𝔫).comap f = E) (hU : (𝔫).support.compl ≤ f.isoLocus) (n : ℕ)
    (q : R̂ ⧸ maximalIdeal R̂ ^ (n + 2)) :
    hE.completionQuotientEquivFiberThickening f hI hU n
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) q) =
      (f.fiberThickeningι n).appTop
        (hE.completionQuotientEquivFiberThickening f hI hU (n + 1) q) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Ideal.Quotient.factor_mk, completionQuotientEquivFiberThickening_mk,
    completionQuotientEquivFiberThickening_mk]
  exact (ConcreteCategory.congr_hom (f.completionToFiberThickening_naturality n) r).symm

end AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
