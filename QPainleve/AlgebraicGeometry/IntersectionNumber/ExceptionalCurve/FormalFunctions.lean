/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Cohomology
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop

import QPainleve.RingTheory.AdicCompletion.CompatibleLifts
import TauCeti.RingTheory.Length

/-!
# Compatible functions on an exceptional fiber

For an exceptional curve of the first kind contracted over a local affine base,
a compatible family of regular functions on its finite thickenings lifts to a
single element of the completed base ring. The section comparison uses the
actual powers of the exceptional ideal, which are pullbacks of the powers of the
maximal ideal of the base.

## References

* The Stacks Project, [Theorem 30.20.5](https://stacks.math.columbia.edu/tag/02OC) and
  [Lemma 54.16.4](https://stacks.math.columbia.edu/tag/0C2L).
-/

public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}} {E : X.IdealSheafData} [IsLocalRing Γ(Y, ⊤)]

local notation "R" => Y.presheaf.obj (Opposite.op ⊤)
local notation "𝔪" => maximalIdeal R
local notation "I" => ofIdealTop 𝔪
local notation "powLE" => pow_le_pow_right_of_le_one' (a := E)
  (le_of_le_of_eq le_top (Eq.symm (one_eq_top (X := X))))

variable [IsAffine Y] [IsLocallyNoetherian Y]

private theorem IsExceptionalCurveOfFirstKind.surjective_appTop_comp_thickening
    (hE : E.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) [IsProper f] [IsIso f.appTop] (hI : (I).comap f = E)
    (hU : (I).support.compl ≤ f.isoLocus) (n : ℕ) :
    Function.Surjective ((E ^ (n + 1)).subschemeι ≫ f).appTop := by
  let j := subschemeMap (E ^ (n + 1)) (I ^ (n + 1)) f (pow_le_map_pow hI.le (n + 1))
  have hj : j ≫ (I ^ (n + 1)).subschemeι = (E ^ (n + 1)).subschemeι ≫ f :=
    subschemeMap_subschemeι _ _ _ _
  have : IsIso (f.app ⊤) := ‹IsIso f.appTop›
  have hs : Function.Surjective j.appTop :=
    hE.surjective_appTop_subschemeMap_pow_of_contraction f hI hU
      (isAffineOpen_top Y) (Set.subset_univ _) n
  rw [← hj, Scheme.Hom.comp_appTop]
  exact hs.comp ((I ^ (n + 1)).subschemeι_app_surjective ⟨⊤, isAffineOpen_top Y⟩)

/-- In an exceptional-curve contraction over an affine Noetherian local base, every compatible
family of functions on the positive thickenings of the exceptional curve lifts to the completed
base ring. At each level, pulling back any representative of the corresponding truncation gives
the prescribed function. The pullback on global functions of the ambient schemes is assumed to
be an isomorphism, as in a contraction onto its normal model. -/
theorem IsExceptionalCurveOfFirstKind.exists_completion_lift_of_exceptional_thickenings
    (hE : E.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) [IsProper f] [IsIso f.appTop] (hI : (I).comap f = E)
    (hU : (I).support.compl ≤ f.isoLocus)
    (b : ∀ n : ℕ, Γ((E ^ (n + 1)).subscheme, ⊤))
    (hb : ∀ n : ℕ, (inclusion (powLE (Nat.le_succ (n + 1)))).appTop (b (n + 1)) = b n) :
    ∃ a : AdicCompletion 𝔪 R, ∀ (n : ℕ) (r : R),
      AdicCompletion.evalₐ 𝔪 (n + 1) a = Ideal.Quotient.mk _ r →
        ((E ^ (n + 1)).subschemeι ≫ f).appTop r = b n := by
  let t (n : ℕ) := (inclusion (powLE (Nat.le_succ (n + 1)))).appTop.hom
  let g (n : ℕ) := Ideal.Quotient.lift (𝔪 ^ (n + 1))
    ((E ^ (n + 1)).subschemeι ≫ f).appTop.hom (by
      -- The thickening is cut out by the pullback of the same power of the center ideal.
      apply (ofIdealTop_le_ker_iff _ _).mp
      rw [ofIdealTop_pow]
      exact le_map_iff_comap_le.mpr (by rw [comap_pow, hI]))
  have hg (n : ℕ) : Function.Surjective (g n) := by
    intro z
    obtain ⟨r, hr⟩ := hE.surjective_appTop_comp_thickening f hI hU n z
    exact ⟨Ideal.Quotient.mk _ r, hr⟩
  have htg (n : ℕ) (r : R) :
      t n (g (n + 1) (Ideal.Quotient.mk _ r)) = g n (Ideal.Quotient.mk _ r) := by
    have hc := congrArg Scheme.Hom.appTop
      (inclusion_subschemeι_assoc (powLE (Nat.le_succ (n + 1))) f)
    rw [Scheme.Hom.comp_appTop] at hc
    exact ConcreteCategory.congr_hom hc r
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  let (n : ℕ) : IsArtinian R (R ⧸ 𝔪 ^ (n + 1)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (TauCeti.isFiniteLength_quotient_maximalIdeal_pow (n + 1))).2
  obtain ⟨a, ha⟩ := AdicCompletion.exists_evalₐ_lift_of_surjective 𝔪 t g htg hg b hb
  refine ⟨a, fun n r hr ↦ ?_⟩
  have hmk : g n (Ideal.Quotient.mk _ r) = ((E ^ (n + 1)).subschemeι ≫ f).appTop r := rfl
  rw [← hmk, ← hr]
  exact ha n

end AlgebraicGeometry.Scheme.IdealSheafData
