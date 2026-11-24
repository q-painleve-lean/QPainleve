/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
public import TauCeti.Algebra.Module.Primitive

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Chow.Nef.Boundary
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import QPainleve.SignedClusterModularGroup.Period

/-!
# Root-avoiding boundary characters on rational surfaces

A primitive nef boundary class of square zero on a smooth projective rational complex
surface is a primitive radical vector in the boundary orthogonal lattice. This gives
an injective character taking value `1/2` on the boundary class and avoiding one on all
translates of roots by that class.
-/

public section

open AlgebraicGeometry TauCeti TauCeti.AlgebraicGeometry LineBundleClass
open LinearMap

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {X : Scheme} [X.Over (Spec (.of ℂ))] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))]
  [rational : Scheme.IsRationalOver (X ↘ Spec (.of ℂ))]
  {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)

local notation "s" => (X ↘ Spec (CommRingCat.of ℂ))
local notation "δ" => (Additive.ofMul (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹)

local instance : IsIntegral X :=
  let : Smooth s := SmoothOfRelativeDimension.smooth 2 s
  rational.isIntegral_of_smooth

local notation "K" => D.boundaryOrthogonal ℂ
local notation "B" => Chow.intersectionBilinForm ℂ X

/-- The boundary orthogonal of a smooth projective rational complex surface with a
primitive nef square-zero effective Cartier divisor admits an injective character with
value `1/2` on the divisor class. All translates of square `-2` classes by the divisor
class have character value different from one. -/
theorem exists_root_avoiding_boundary_character (hprim : IsPrimitive δ)
    (hnef : (δ).toMul.IsNef ℂ s) (hsq : B δ δ = 0) :
    ∃ (d : K) (a : Multiplicative K →* ℂˣ), d.val = δ ∧ Function.Injective a ∧
      (a (Multiplicative.ofAdd d) : ℂ) = (2 : ℂ)⁻¹ ∧
      ∀ x : K, B x.val x.val = -2 → ∀ m : ℤ, a (Multiplicative.ofAdd (x + m • d)) ≠ 1 := by
  let : Module.Free ℤ (Additive (LineBundleClass X)) := X.free_picard_of_isRationalOver ℂ
  let : Module.Finite ℤ (Additive (LineBundleClass X)) := X.finite_picard_of_isRationalOver ℂ
  let d : K := ⟨δ, (hD.effectiveCartierClass_mem_boundaryOrthogonal_iff_of_isNef hnef).2
    (by simpa only [Chow.intersectionBilinForm_apply, toMul_ofMul] using hsq)⟩
  have hs : (B).IsSymm :=
    ⟨fun x y ↦ by simp only [Chow.intersectionBilinForm_apply, Chow.classIntersectionNumber_comm]⟩
  let : IsNoetherian X := isNoetherian_of_finiteType s
  let := (s).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let U : X.Opens := D.support.compl
  have hm : δ ∈ U.primeDivisorSpanCompl := by
    have htop : D.comap U.ι = ⊤ :=
      (D.comap_eq_top_iff _).mpr (Scheme.Opens.ι_preimage_self U)
    exact (U.mem_primeDivisorSpanCompl_iff _).mpr (by
      rw [pullback_inv, hD.pullback_mk_toInvertibleSheaf_eq_one_of_comap_eq_top htop, inv_one])
  have hr : d ∈ ((B).restrict K).orthogonal ⊤ := by
    have hδ := BilinForm.le_orthogonal_orthogonal hs.isRefl hm
    refine BilinForm.mem_orthogonal_iff.mpr fun x _ ↦ ?_
    have hx : x.val ∈ (B).orthogonal U.primeDivisorSpanCompl :=
      (congrArg (fun M ↦ x.val ∈ M) (D.boundaryOrthogonal_def ℂ)).mp x.property
    exact BilinForm.mem_orthogonal_iff.mp hδ x.val hx
  have hdprim : IsPrimitive d := hprim.of_map (g := (K).subtype)
  obtain ⟨f, hf⟩ := isPrimitive_def.mp hdprim
  obtain ⟨a, ha, hval, hroots⟩ :=
    QPainleve.exists_root_avoiding_period ((B).restrict K) (hs.restrict K) hr f hf
  exact ⟨d, a, rfl, ha, hval, hroots⟩

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
