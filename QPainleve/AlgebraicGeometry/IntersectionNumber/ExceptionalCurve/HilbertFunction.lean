/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Thickening
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Cohomology
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TwistingSheaf
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
import TauCeti.AlgebraicGeometry.LineBundle.BaseChange
import TauCeti.AlgebraicGeometry.Modules.Sections

/-!
# Hilbert function of an exceptional curve's thickenings

The successive layers of the thickenings of an exceptional curve of the first
kind contribute `n + 1` sections in order `n`. Thus the ring of regular functions
on `nE` has dimension `(n + 1).choose 2` over the field of the exceptional line.
These are the dimensions of the corresponding truncations of the completed
local ring in a Castelnuovo contraction.

## References

* The Stacks Project, [Lemma 54.16.3](https://stacks.math.columbia.edu/tag/0C2K).
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory
open Opposite (op)
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

open LineBundleClass

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {E : X.IdealSheafData} (hE : E.IsExceptionalCurveOfFirstKind)
  (e : projectiveLine k ≅ E.subscheme) [e.hom.IsOver (Spec (.of k))]

local notation "powLE" => pow_le_pow_right_of_le_one' (a := E)
  (le_of_le_of_eq le_top (Eq.symm (one_eq_top (X := X))))
local notation "𝒪" => Proj.twistingSheaf (SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k))

include hE in
private theorem intersectionNumber_cartier_pow (n : ℕ) :
    intersectionNumber k (e.hom ≫ E.subschemeι)
      (LineBundleClass.mk (isEffectiveCartier_pow hE.isEffectiveCartier n).toInvertibleSheaf) =
        n := by
  have hconormal : intersectionNumber k (e.hom ≫ E.subschemeι)
      (LineBundleClass.mk hE.isEffectiveCartier.toInvertibleSheaf) = 1 := by
    rw [intersectionNumber_def, ← pullback_comp,
      eulerDegree_pullback_of_isIso e.hom (comp_over e.hom (Spec (.of k))),
      ← intersectionNumber_def,
      hE.intersectionNumber_mk_toInvertibleSheaf k,
      ← e.hom.finrank_cohomology_trivial_of_isIso k 0,
      projectiveLine.finrank_cohomology_zero_trivial, Nat.cast_one]
  rw [mk_toInvertibleSheaf_pow hE.isEffectiveCartier, intersectionNumber_pow_of_isIntegral,
    hconormal, mul_one]

include hE in
/-- The `n`th Cartier layer of an exceptional curve over `k` has the cohomology
of `𝒪(n)` on the projective line over `k`. -/
def cohomologyThickeningLayerEquiv (n q : ℕ) :
    Cohomology (cokernel (sheafHomOfLE (powLE (Nat.le_succ n)))) q ≃ₗ[k]
      Cohomology (𝒪 n) q := by
  let M := (isEffectiveCartier_pow hE.isEffectiveCartier n).toInvertibleSheaf
  let c := E.cohomologyTensorPushforwardSubschemeEquivTwistingSheaf e M q
  have hM : intersectionNumber k (e.hom ≫ E.subschemeι) (LineBundleClass.mk M) = n :=
    intersectionNumber_cartier_pow hE e n
  exact (cohomologyBaseLinearEquivOfIso k (hE.isEffectiveCartier.thickeningLayerIso n) q).trans
    (c.trans (LinearEquiv.cast (M := fun d : ℤ ↦ Cohomology (𝒪 d) q) hM))

include hE e in
private theorem finite_finrank_cohomology_zero_pow (n : ℕ) :
    FiniteDimensional k (Cohomology (E ^ n).pushforwardSubscheme 0) ∧
      Module.finrank k (Cohomology (E ^ n).pushforwardSubscheme 0) = (n + 1).choose 2 := by
  induction n with
  | zero =>
      rw [pow_zero, one_eq_top]
      let A : X.IdealSheafData := ⊤
      let c := A.subschemeι.cohomologyPushforwardBaseLinearEquiv k
        (Scheme.Modules.unit A.subscheme) 0
      let d := cohomologyZeroBaseLinearEquiv k A.subscheme (Scheme.Modules.unit A.subscheme)
      have : IsEmpty A.subscheme := inferInstanceAs (IsEmpty (⊤ : X.IdealSheafData).subscheme)
      have : IsEmpty (⊤ : A.subscheme.Opens) := ⟨fun x ↦ isEmptyElim x.val⟩
      have h : Subsingleton (Cohomology A.pushforwardSubscheme 0) :=
        ⟨fun s t ↦ (c.trans d).injective (section_ext_of_isEmpty _ _)⟩
      exact ⟨inferInstanceAs (FiniteDimensional k (Cohomology A.pushforwardSubscheme 0)), by
        rw [Module.finrank_zero_of_subsingleton (M := Cohomology A.pushforwardSubscheme 0)]
        decide⟩
  | succ n ih =>
      let S := ShortComplex.mk _ _
        (quotientToPushforwardSubscheme_pushforwardSubschemeMap (powLE (Nat.le_succ n)))
      have hS : S.ShortExact := shortExact_quotientToPushforwardSubscheme _
      let c := hE.cohomologyThickeningLayerEquiv e n 0
      have h₃ : FiniteDimensional k (Cohomology S.X₃ 0) := ih.1
      have h₁ : FiniteDimensional k (Cohomology S.X₁ 0) := Module.Finite.equiv c.symm
      have h₂ := finiteDimensional_cohomology_X₂ k X hS 0
      let f := cohomologyMapBaseLinear k X S.f 0
      let g := cohomologyMapBaseLinear k X S.g 0
      have hf : Function.Injective f := by
        have := hS.mono_f
        simpa only [f, coe_cohomologyMapBaseLinear] using cohomologyMap_injective S.f
      have hg' : Function.Surjective (cohomologyMap S.g 0) := by
        intro y
        obtain ⟨x, hx⟩ := hE.surjective_pushforwardSubschemeMap_app_top_pow (Nat.le_succ n)
          (cohomologyZeroEquiv S.X₃ y)
        refine ⟨(cohomologyZeroEquiv S.X₂).symm x, (cohomologyZeroEquiv S.X₃).injective ?_⟩
        rw [cohomologyZeroEquiv_cohomologyMap, AddEquiv.apply_symm_apply]
        exact hx
      have hg : Function.Surjective g := by
        simpa only [g, coe_cohomologyMapBaseLinear] using hg'
      have hfg : Function.Exact f g := by
        simpa only [f, g, coe_cohomologyMapBaseLinear] using exact_cohomologyMap_cohomologyMap hS 0
      have hr := g.finrank_range_add_finrank_ker
      rw [LinearMap.range_eq_top.mpr hg, finrank_top, hfg.linearMap_ker_eq,
        LinearMap.finrank_range_of_inj hf, c.finrank_eq,
        projectiveLine.finrank_cohomology_zero_twistingSheaf] at hr
      have hdim : Module.finrank k (Cohomology S.X₃ 0) = (n + 1).choose 2 := ih.2
      rw [hdim, ← Int.natCast_succ, Int.toNat_natCast] at hr
      have hchoose : (n + 1).choose 2 + n.succ = (n + 1 + 1).choose 2 := by
        rw [Nat.choose_succ_succ' (n + 1) 1, Nat.choose_one_right]
        exact Nat.add_comm _ _
      exact ⟨h₂, hr.symm.trans hchoose⟩

include hE e in
private theorem finite_finrank_globalSections_pow (n : ℕ) :
    let Y := (E ^ n).subscheme
    letI : Algebra k Γ(Y, ⊤) := ((Y.baseRingToStructurePresheaf k).app (op ⊤)).hom.toAlgebra
    Module.Finite k Γ(Y, ⊤) ∧ Module.finrank k Γ(Y, ⊤) = (n + 1).choose 2 := by
  let Y := (E ^ n).subscheme
  let _ : Algebra k Γ(Y, ⊤) := ((Y.baseRingToStructurePresheaf k).app (op ⊤)).hom.toAlgebra
  let M := Scheme.Modules.unit Y
  let c := ((E ^ n).subschemeι.cohomologyPushforwardBaseLinearEquiv k M 0).trans
    ((cohomologyZeroBaseLinearEquiv k Y M).trans (structureSheafSectionsBaseLinearEquiv k Y))
  obtain ⟨hfinite, hrank⟩ := finite_finrank_cohomology_zero_pow hE e n
  exact ⟨Module.Finite.equiv c, c.finrank_eq.symm.trans hrank⟩

include hE e in
/-- The ring of regular functions on the `n`th thickening is finite over `k`. -/
theorem finite_globalSections_thickening (n : ℕ) :
    let Y := (E ^ n).subscheme
    letI : Algebra k Γ(Y, ⊤) := ((Y.baseRingToStructurePresheaf k).app (op ⊤)).hom.toAlgebra
    Module.Finite k Γ(Y, ⊤) :=
  (finite_finrank_globalSections_pow hE e n).1

include hE e in
/-- The ring of regular functions on the `n`th thickening of an exceptional
curve over `k` has dimension `(n + 1).choose 2`. -/
theorem finrank_globalSections_thickening (n : ℕ) :
    let Y := (E ^ n).subscheme
    letI : Algebra k Γ(Y, ⊤) := ((Y.baseRingToStructurePresheaf k).app (op ⊤)).hom.toAlgebra
    Module.finrank k Γ(Y, ⊤) = (n + 1).choose 2 :=
  (finite_finrank_globalSections_pow hE e n).2

end AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
