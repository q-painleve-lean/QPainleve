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

/-!
# Ideal powers of a local exceptional contraction

For a proper exceptional contraction to a Noetherian local spectrum, pullback
identifies the powers of the maximal ideal with the ideals of functions that
vanish on the corresponding thickenings of the exceptional fiber. This identifies
each positive maximal-ideal quotient with the ring of functions on its thickened fiber.

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
local notation "𝔫" => ofIdealTop (Ideal.map
  (CommRingCat.Hom.hom (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of R)))) (maximalIdeal R))

private abbrev quotientSpec (n : ℕ) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ n)))

private abbrev fiberSectionsMap (n : ℕ) :=
  ((Scheme.ΓSpecIso _).inv ≫ (pullback.snd f (quotientSpec (R := R) n)).appTop).hom

private abbrev baseSectionsMap :=
  (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop

private theorem ker_fiberThickening_fst (hE : (𝔫).comap f = E) (n : ℕ) :
    (pullback.fst f (quotientSpec (R := R) n)).ker = E ^ n := by
  have : IsClosedImmersion (quotientSpec (R := R) n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  rw [quotientSpec, ker_fst_of_isClosedImmersion, Scheme.Hom.ker_Spec_map,
    CommRingCat.hom_ofHom, Ideal.mk_ker, Ideal.map_pow, ofIdealTop_pow, comap_pow, hE]

private theorem fiberSectionsMap_comp_quotient (n : ℕ) :
    (fiberSectionsMap f n).comp (Ideal.Quotient.mk (𝔪 ^ n)) =
      (baseSectionsMap f ≫ (pullback.fst f (quotientSpec (R := R) n)).appTop).hom := by
  let q := CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ n))
  let a := pullback.fst f (Spec.map q)
  let b := pullback.snd f (Spec.map q)
  have hcomm : baseSectionsMap f ≫ a.appTop = q ≫ (Scheme.ΓSpecIso _).inv ≫ b.appTop := by
    -- Apply global sections to the Cartesian square and use the affine section isomorphisms.
    simp only [baseSectionsMap, Category.assoc, ← Scheme.Hom.comp_appTop]
    rw [show a ≫ f = b ≫ Spec.map q from pullback.condition, Scheme.Hom.comp_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc]
  exact congrArg CommRingCat.Hom.hom hcomm.symm

private theorem ker_fiberSectionsMap_comp_quotient (hE : (𝔫).comap f = E) (n : ℕ) :
    RingHom.ker ((fiberSectionsMap f n).comp (Ideal.Quotient.mk (𝔪 ^ n))) =
      ((E ^ n).sections ⊤).comap (baseSectionsMap f).hom := by
  let a := pullback.fst f (quotientSpec (R := R) n)
  have : IsClosedImmersion (quotientSpec (R := R) n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion a := inferInstanceAs (IsClosedImmersion (pullback.fst f _))
  ext r
  rw [fiberSectionsMap_comp_quotient, RingHom.mem_ker, Ideal.mem_comap,
    ← ker_fiberThickening_fst f hE n, a.mem_ker_sections_iff]
  rfl

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
  · rw [← ker_fiberSectionsMap_comp_quotient f hI 1, ← RingHom.comap_ker]
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
      ker_fiberSectionsMap_comp_quotient f hI]
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
  rw [ker_fiberSectionsMap_comp_quotient f hI,
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
    (ker_subschemeι _).trans (ker_fiberThickening_fst f hI n).symm
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
  rw [fiberSectionsMap_comp_quotient]
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

end AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
