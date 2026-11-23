/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.LineBundle.GlobalGeneration
import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Pullback
import TauCeti.AlgebraicGeometry.LineBundle.SectionDegree
import TauCeti.AlgebraicGeometry.Curves.Normalization

/-!
# Nefness from globally generated line bundles

A globally generated line bundle restricts to a line bundle with a nonzero section on every
integral curve. In particular, sufficiently high ample twists of any line bundle are nef.
-/

public section

open AlgebraicGeometry CategoryTheory Filter
open TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- A globally generated line bundle has nonnegative degree on every proper integral curve. -/
theorem InvertibleSheaf.IsGloballyGenerated.isNef {k : Type u} [Field k] {X : Scheme.{u}}
    {L : InvertibleSheaf X} (hL : L.IsGloballyGenerated) (f : X ⟶ Spec (.of k)) :
    (LineBundleClass.mk L).IsNef k f := by
  refine (LineBundleClass.isNef_iff k f _).mpr fun C _ _ i _ _ ↦ ?_
  have : RelativeDimensionLE 1 (C ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  let M := (InvertibleSheaf.pullback i).obj L
  have hM : M.IsGloballyGenerated := hL.pullback i
  obtain ⟨s, hs⟩ := InvertibleSheaf.isGloballyGenerated_iff.mp hM (genericPoint C)
  have hs₀ : s ≠ 0 := by
    intro h
    simp [h, Scheme.Modules.nonvanishingLocus_zero] at hs
  rw [LineBundleClass.intersectionNumber_def, LineBundleClass.pullback_mk,
    LineBundleClass.eulerDegree_mk]
  exact M.eulerDegree_nonneg_of_ne_zero k s hs₀

/-- Twisting a line-bundle class by every sufficiently high power of an ample class makes it
nef. -/
theorem LineBundleClass.IsAmple.eventually_isNef_mul_pow {k : Type u} [Field k]
    {X : Scheme.{u}} {a : LineBundleClass X} (ha : a.IsAmple) (b : LineBundleClass X)
    (f : X ⟶ Spec (.of k)) :
    ∀ᶠ n : ℕ in atTop, (b * a ^ n).IsNef k f := by
  obtain ⟨L, rfl⟩ := LineBundleClass.mk_surjective a
  obtain ⟨M, rfl⟩ := LineBundleClass.mk_surjective b
  filter_upwards [M.obj.eventually_exists_generatingSections_tensor_tensorPow_of_isAmple L ha]
    with n ⟨s, _⟩
  let P := M.tensorProduct (L.tensorPow n)
  have hP : P.IsGloballyGenerated :=
    InvertibleSheaf.isGloballyGenerated_iff_nonempty_generatingSections.mpr
      ⟨s.equivOfIso (M.tensorProductObjIso (L.tensorPow n)).symm⟩
  simpa only [P, LineBundleClass.mk_tensorProduct, LineBundleClass.mk_tensorPow] using hP.isNef f

end TauCeti.AlgebraicGeometry
