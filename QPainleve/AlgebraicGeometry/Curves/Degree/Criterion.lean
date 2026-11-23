/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.CartierDivisor.SectionDivision
import QPainleve.AlgebraicGeometry.Cohomology.SerreVanishing
import QPainleve.AlgebraicGeometry.IdealSheaf.Tensor.GlobalGeneration
import QPainleve.AlgebraicGeometry.LineBundle.GlobalGeneration
import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.Degree
import TauCeti.AlgebraicGeometry.Curves.Normalization

/-!
# The degree criterion for ampleness on integral projective curves

Positive Euler degree makes the Euler characteristic of a high power positive even
after twisting by a fixed line bundle. Choose that twist so a nonzero section compares
the power to an ample line bundle. The section cuts out a finite Cartier divisor.
Lifting sections across this divisor exhibits the original power as the tensor
product of an ample bundle and a globally generated bundle.

This is the projective integral case of the degree criterion in the Stacks Project,
[Lemma 33.44.14](https://stacks.math.columbia.edu/tag/0B5X).
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory Filter
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry.LineBundleClass

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [X.IsCurveOver k]

private theorem exists_pow_mul_section (a b : LineBundleClass X) (ha : 0 < a.eulerDegree k) :
    ∃ (n : ℕ) (_ : 0 < n) (M : InvertibleSheaf X), mk M = a ^ n * b ∧
      ∃ s : Γ(M.obj, ⊤), s ≠ 0 := by
  have : RelativeDimensionLE 1 (X ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  let c := Scheme.Modules.eulerCharBelow k X (InvertibleSheaf.trivial X).obj 2
  obtain ⟨n, hn⟩ := exists_nat_gt (max 0 (-(b.eulerDegree k + c)))
  have hn₀ : 0 < n := by exact_mod_cast (le_max_left _ _).trans_lt hn
  obtain ⟨M, hM⟩ := mk_surjective (a ^ n * b)
  refine ⟨n, hn₀, M, hM, ?_⟩
  have hd := (eulerDegree_mk k M).symm
  rw [hM, eulerDegree_mul_of_isIntegral, ← zpow_natCast, eulerDegree_zpow_of_isCurveOver,
    InvertibleSheaf.eulerDegree_def, Scheme.Modules.eulerCharBelow_two] at hd
  have hn₁ := (le_max_right 0 (-(b.eulerDegree k + c))).trans_lt hn
  have hdegree : 1 ≤ a.eulerDegree k := by omega
  have hpos : 0 < Module.finrank k (Cohomology M.obj 0) := by
    have hbound := mul_le_mul_of_nonneg_left hdegree (Int.natCast_nonneg n)
    dsimp only [c] at hn₁
    omega
  have := M.finiteDimensional_cohomology_of_isIntegral k (i := 0) (by decide)
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  exact ⟨cohomologyZeroBaseLinearEquiv k X M.obj v, fun h ↦
    hv ((cohomologyZeroBaseLinearEquiv k X M.obj).injective (h.trans (map_zero _).symm))⟩

variable [X.IsProjectiveOver k]

/-- On an integral projective curve over any field, ampleness is equivalent to positive
Euler degree. This includes singular integral curves. -/
theorem isAmple_iff_eulerDegree_pos (a : LineBundleClass X) :
    a.IsAmple ↔ 0 < a.eulerDegree k := by
  refine ⟨IsAmple.eulerDegree_pos, fun ha ↦ ?_⟩
  obtain ⟨h, hh⟩ := X.exists_isAmple_of_isProjectiveOver k
  obtain ⟨A, rfl⟩ := mk_surjective h
  let F := 𝟙_ X.Modules
  have hgen := F.eventually_exists_generatingSections_tensor_tensorPow_of_isAmple A hh
  have hvan := (X ↘ Spec (.of k)).eventually_subsingleton_cohomology_tensorPow_of_isAmple F A hh
  obtain ⟨m, ⟨σ, _⟩, hm⟩ := (hgen.and hvan).exists
  let B := A.tensorPow m
  let eB : F ⊗ B.obj ≅ B.obj := λ_ B.obj
  have hB : B.IsGloballyGenerated :=
    InvertibleSheaf.isGloballyGenerated_iff_nonempty_generatingSections.mpr
      ⟨σ.equivOfIso eB⟩
  have : Subsingleton (Cohomology (F ⊗ B.obj) 1) := hm 1 one_pos
  obtain ⟨n, hn, M, hM, s, hs⟩ :=
    exists_pow_mul_section a ((mk A)⁻¹ * (mk B)⁻¹) ha
  let I := M.zeroIdeal s
  let hI := M.isEffectiveCartier_zeroIdeal hs
  let N := M.tensorProduct B
  have : RelativeDimensionLE 1 (X ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  have : IsFinite (I.subschemeι ≫ X ↘ Spec (.of k)) := hI.isFinite_subschemeι_comp
  have : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ X ↘ Spec (.of k))
  -- Dividing the section by its own zero ideal trivializes the factor containing `M`.
  obtain ⟨e, _⟩ := (M.zeroIdeal_eq_iff_exists_iso_tensorLift (I := I) hs).mp rfl
  let iso : N.obj ⊗ I.sheaf ≅ F ⊗ B.obj :=
    β_ N.obj I.sheaf ≪≫ whiskerLeftIso I.sheaf (M.tensorProductObjIso B) ≪≫
      (α_ I.sheaf M.obj B.obj).symm ≪≫ whiskerRightIso e.symm B.obj
  have hNvan := (cohomologyBaseLinearEquivOfIso k iso 1).toEquiv.subsingleton
  have hN := M.isGloballyGenerated_tensorProduct_of_isAffine_zeroIdeal B s hB hNvan
  apply IsAmple.of_pow hn
  have hclass : mk A * mk N = a ^ n := by
    calc
      mk A * mk N = a ^ n * (mk A * (mk A)⁻¹) * ((mk B)⁻¹ * mk B) := by
        simp only [N, mk_tensorProduct, hM]
        ac_rfl
      _ = a ^ n := by simp only [mul_inv_cancel, inv_mul_cancel, mul_one]
  exact hclass ▸ hh.mul_mk_of_isGloballyGenerated hN

end TauCeti.AlgebraicGeometry.LineBundleClass
