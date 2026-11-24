/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Cohomology
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop
import QPainleve.RingTheory.AdicCompletion.Lifting
import TauCeti.RingTheory.Length

/-!
# Compatible lifts for an exceptional contraction

A compatible family of regular functions on the infinitesimal thickenings
of the scheme-theoretic exceptional fiber lifts to a single element of the
completed local base ring. The finite-level lifts come from the cohomology
of the exceptional ideal powers.

## References

* The Stacks Project, [Lemma 54.16.4](https://stacks.math.columbia.edu/tag/0C2L).
-/

public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {X : Scheme.{u}} {E : X.IdealSheafData}

local notation "𝔪" => maximalIdeal R
local notation "𝔐" => ofIdealTop (Ideal.map
  (CommRingCat.Hom.hom (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of R)))) (maximalIdeal R))
local notation "powLE" => pow_le_pow_right_of_le_one' (a := E)
  (le_of_le_of_eq le_top (Eq.symm (one_eq_top (X := X))))

private theorem pow_le_ker_appTop_thickening (f : X ⟶ Spec (.of R))
    (hI : (𝔐).comap f ≤ E) (n : ℕ) :
    𝔪 ^ n ≤ RingHom.ker ((Scheme.ΓSpecIso (.of R)).inv ≫
      ((E ^ n).subschemeι ≫ f).appTop).hom := by
  rw [CommRingCat.hom_comp, ← RingHom.comap_ker, ← Ideal.map_le_iff_le_comap,
    ← ofIdealTop_le_ker_iff, Ideal.map_pow, ofIdealTop_pow]
  exact pow_le_map_pow hI n

variable [IsNoetherianRing R]

/-- Every compatible family on the thickenings of the scheme-theoretic exceptional
fiber of a proper contraction over a Noetherian local spectrum lifts to the completed
base ring. Pulling back any representative of a truncation of the lift gives the
prescribed section on that thickening. -/
theorem exists_completion_lift_of_fiber_thickenings (hE : E.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Spec (.of R)) [IsProper f] (hI : (𝔐).comap f = E)
    (hU : (𝔐).support.compl ≤ f.isoLocus) [IsIso (f.app ⊤)]
    (s : ∀ n : ℕ, Γ((E ^ (n + 1)).subscheme, ⊤))
    (hs : ∀ n : ℕ, (inclusion (powLE (Nat.le_succ (n + 1)))).appTop (s (n + 1)) = s n) :
    ∃ x : AdicCompletion 𝔪 R, ∀ (n : ℕ) (r : R),
      AdicCompletion.evalₐ 𝔪 (n + 1) x = Ideal.Quotient.mk _ r →
        ((E ^ (n + 1)).subschemeι ≫ f).appTop ((Scheme.ΓSpecIso (.of R)).inv r) = s n := by
  let j (n : ℕ) := (E ^ (n + 1)).subschemeι ≫ f
  let a (n : ℕ) := ((Scheme.ΓSpecIso (.of R)).inv ≫ (j n).appTop).hom
  let q (n : ℕ) := Ideal.Quotient.lift (𝔪 ^ (n + 1)) (a n)
    (pow_le_ker_appTop_thickening f hI.le (n + 1))
  let i (n : ℕ) := inclusion (powLE (Nat.le_succ (n + 1)))
  let t (n : ℕ) := (i n).appTop.hom
  have hq (n : ℕ) : Function.Surjective (q n) := by
    let g := subschemeMap (E ^ (n + 1)) (𝔐 ^ (n + 1)) f (pow_le_map_pow hI.le (n + 1))
    have hg : Function.Surjective g.appTop :=
      hE.surjective_appTop_subschemeMap_pow_of_contraction f hI hU
        (isAffineOpen_top _) le_top n
    have hsurj := IsClosedImmersion.isAffine_surjective_of_isAffine (𝔐 ^ (n + 1)).subschemeι
    have hj : Function.Surjective (j n).appTop := by
      dsimp only [j]
      rw [← subschemeMap_subschemeι _ _ f (pow_le_map_pow hI.le (n + 1)), Scheme.Hom.comp_appTop]
      exact hg.comp hsurj.2
    intro y
    have hΓ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).2
    obtain ⟨r, hr⟩ := hj.comp hΓ y
    exact ⟨Ideal.Quotient.mk _ r, hr⟩
  have ht (n : ℕ) : (t n).comp (q (n + 1)) = (q n).comp
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) := by
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun r ↦ ?_
    have hj : i n ≫ j (n + 1) = j n := by simp [i, j, ← Category.assoc]
    have hj' := congrArg Scheme.Hom.appTop hj
    rw [Scheme.Hom.comp_appTop] at hj'
    simp only [q, RingHom.comp_apply, Ideal.Quotient.factor_mk]
    exact ConcreteCategory.congr_hom hj' ((Scheme.ΓSpecIso (.of R)).inv r)
  let (n : ℕ) : IsArtinian R (R ⧸ 𝔪 ^ (n + 1)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (TauCeti.isFiniteLength_quotient_maximalIdeal_pow (n + 1))).2
  obtain ⟨x, hx⟩ := AdicCompletion.exists_evalₐ_eq_of_compatible_quotients 𝔪 q t hq ht s hs
  refine ⟨x, fun n r hr ↦ ?_⟩
  exact ((congrArg (q n) hr).symm.trans (hx n) :
    q n (Ideal.Quotient.mk _ r) = s n)

end AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
