/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IdealSheaf.Quotient
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Cohomology
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Finite thickenings of an exceptional curve

For an exceptional curve of the first kind, the successive layers of the
filtration by powers of its ideal are positive twists on the projective line.
Taking sections of these layers gives the surjective restriction maps used in
the construction of the completed local ring of the contraction.

## References

* The Stacks Project, [Lemma 54.16.3](https://stacks.math.columbia.edu/tag/0C2K).
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open LineBundleClass

variable {X : Scheme.{u}} {E : X.IdealSheafData}

local notation "powLE" => pow_le_pow_right_of_le_one' (a := E)
  (le_of_le_of_eq le_top (Eq.symm (one_eq_top (X := X))))

/-- A nonnegative Cartier twist on an exceptional curve has surjective restriction
between any two of its finite thickenings. The map is the restriction of
`𝒪_X(-dE)` from `nE` to `mE`, expressed on the ambient scheme by the tensor
quotients. -/
theorem IsExceptionalCurveOfFirstKind.surjective_exceptionalThickening_restriction
    (hE : E.IsExceptionalCurveOfFirstKind) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective
      (((isEffectiveCartier_pow hE.isEffectiveCartier d).toInvertibleSheaf.obj ◁
        pushforwardSubschemeMap (powLE hmn)).app ⊤) := by
  let M := (isEffectiveCartier_pow hE.isEffectiveCartier d).toInvertibleSheaf
  induction hmn with
  | refl => simpa using (Function.surjective_id (α := Γ(M.obj ⊗ (E ^ m).pushforwardSubscheme, ⊤)))
  | @step n hmn ih =>
    have hstep : Function.Surjective
        ((M.obj ◁ pushforwardSubschemeMap (powLE (Nat.le_succ n))).app ⊤) := by
      let h := powLE (Nat.le_succ n)
      let N := (isEffectiveCartier_pow hE.isEffectiveCartier n).toInvertibleSheaf
      let e₀ := (tensorLeft M.obj).mapIso (hE.isEffectiveCartier.thickeningLayerIso n) ≪≫
        (α_ M.obj N.obj E.pushforwardSubscheme).symm ≪≫
          (tensorRight E.pushforwardSubscheme).mapIso (M.tensorProductObjIso N).symm
      obtain ⟨κ, _, e, he⟩ := hE.exists_iso
      let i := e.hom ≫ E.subschemeι
      have hi : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (e.hom ≫ E.subschemeι))
      let C := LineBundleClass.mk hE.isEffectiveCartier.toInvertibleSheaf
      have hd : intersectionNumber κ i C = 1 := by
        dsimp only [C]
        rw [intersectionNumber_mk]
        exact (projectiveLine.nonempty_iso_twistingSheaf_iff κ _ 1).mp he
      have hdeg : -1 ≤ intersectionNumber κ i (LineBundleClass.mk (M.tensorProduct N)) := by
        have hdM : LineBundleClass.mk M = C ^ d := mk_toInvertibleSheaf_pow hE.isEffectiveCartier d
        have hdN : LineBundleClass.mk N = C ^ n := mk_toInvertibleSheaf_pow hE.isEffectiveCartier n
        rw [mk_tensorProduct, intersectionNumber_mul_of_isIntegral, hdM, hdN,
          intersectionNumber_pow_of_isIntegral, intersectionNumber_pow_of_isIntegral, hd]
        omega
      have hv := subsingleton_cohomology_one_tensor_pushforwardSubscheme_of_projectiveLine _ e hdeg
      have hz : Subsingleton (Cohomology (M.obj ⊗ cokernel (sheafHomOfLE h)) 1) :=
        @Function.Injective.subsingleton _ _ _
          ((cohomologyFunctor _ 1).mapIso e₀).addCommGroupIsoToAddEquiv.injective hv
      have hexact := shortExact_quotientToPushforwardSubscheme h
      exact sections_surjective (Scheme.Modules.shortExact_map_tensorLeft M.obj hexact) hz
    have hc : (M.obj ◁ pushforwardSubschemeMap (powLE (Nat.le_succ n))) ≫
        (M.obj ◁ pushforwardSubschemeMap (powLE hmn)) =
        M.obj ◁ pushforwardSubschemeMap (powLE (Nat.le.step hmn)) := by
      rw [← whiskerLeft_comp, pushforwardSubschemeMap_comp]
    intro y
    obtain ⟨x, hx⟩ := (ih.comp hstep) y
    exact ⟨x, (ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.app (⊤ : X.Opens)) hc) x).symm.trans hx⟩

/-- Regular functions restrict surjectively from a larger finite thickening of an
exceptional curve of the first kind to a smaller one. -/
theorem IsExceptionalCurveOfFirstKind.surjective_appTop_inclusion_pow
    (hE : E.IsExceptionalCurveOfFirstKind) {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective (inclusion (powLE hmn)).appTop := by
  let g := pushforwardSubschemeMap (powLE hmn)
  let M := (isEffectiveCartier_pow hE.isEffectiveCartier 0).toInvertibleSheaf
  have hM : LineBundleClass.mk M = 1 :=
    (mk_toInvertibleSheaf_pow hE.isEffectiveCartier 0).trans (pow_zero _)
  obtain ⟨e⟩ := mk_eq_one_iff.mp hM
  let u (N : X.Modules) : M.obj ⊗ N ≅ N := (tensorRight N).mapIso e ≪≫ λ_ N
  have hcomp : M.obj ◁ g ≫ (u _).hom = (u _).hom ≫ g := by
    simp only [u, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    exact (whisker_exchange_assoc e.hom g _).trans
      (congrArg (e.hom ▷ _ ≫ ·) (leftUnitor_naturality g))
  have hs := hE.surjective_exceptionalThickening_restriction 0 hmn
  have h₂ := (ConcreteCategory.bijective_of_isIso ((u (E ^ m).pushforwardSubscheme).hom.app ⊤)).2
  have hg : Function.Surjective (g.app ⊤) := by
    intro y
    obtain ⟨x, hx⟩ := h₂.comp hs y
    refine ⟨(u (E ^ n).pushforwardSubscheme).hom.app ⊤ x, ?_⟩
    have hh := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.app (⊤ : X.Opens)) hcomp) x
    exact hh.symm.trans hx
  intro z
  obtain ⟨s, hs⟩ := hg z
  refine ⟨s, ?_⟩
  have h := pushforwardSubschemeMap_app (powLE hmn) ⊤ s
  have htop := Scheme.Hom.appLE_eq_app (f := inclusion (powLE hmn))
    (U := (⊤ : (E ^ n).subscheme.Opens))
  exact (ConcreteCategory.congr_hom htop s).symm.trans (h.symm.trans hs)

end AlgebraicGeometry.Scheme.IdealSheafData
