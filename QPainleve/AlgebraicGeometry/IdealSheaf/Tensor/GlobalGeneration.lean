/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.ZeroDivisor
public import QPainleve.AlgebraicGeometry.IdealSheaf.Tensor.Restriction
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Basic

import QPainleve.AlgebraicGeometry.LineBundle.Pullback
import QPainleve.AlgebraicGeometry.LineBundle.TensorProduct

/-!
# Global generation across an affine zero scheme

A section of a line bundle and generators of a second bundle generate their tensor product
away from the zero scheme of the section. If that scheme is affine, sections of the
restriction generate along it, and first cohomology of the ideal-sheaf twist controls
whether these sections lift.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

variable {X : Scheme.{u}}

/-- Tensoring a globally generated line bundle by a bundle with a section of affine zero
scheme preserves global generation if the first cohomology of the product twisted by the
zero ideal vanishes. -/
theorem isGloballyGenerated_tensorProduct_of_isAffine_zeroIdeal (M B : InvertibleSheaf X)
    (s : Γ(M.obj, ⊤)) (hB : B.IsGloballyGenerated) [IsAffine (M.zeroIdeal s).subscheme]
    (hvan : Subsingleton (Cohomology ((M.tensorProduct B).obj ⊗ (M.zeroIdeal s).sheaf) 1)) :
    (M.tensorProduct B).IsGloballyGenerated := by
  let I := M.zeroIdeal s
  let N := M.tensorProduct B
  let i := I.subschemeι
  have : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X N.obj := N.property
  apply isGloballyGenerated_iff.mpr
  intro x
  by_cases hx : x ∈ I.support
  · have hx' : x ∈ (I.support : Set X) := hx
    rw [← I.range_subschemeι] at hx'
    obtain ⟨y, hy⟩ := hx'
    let P := (pullback i).obj N
    obtain ⟨t, ht⟩ := isGloballyGenerated_iff.mp P.isGloballyGenerated_of_isAffine y
    let e : (Scheme.Modules.pullback i).obj N.obj ≅ P.obj :=
      eqToIso (pullback_obj_obj i N).symm
    obtain ⟨v, hv⟩ := I.surjective_pullbackSectionsLE_of_subsingleton_cohomology_one N hvan
      (e.symm.hom.app ⊤ t)
    refine ⟨v, ?_⟩
    rw [← hy]
    rw [← nonvanishingLocus_hom_app e.symm, ← hv,
      nonvanishingLocus_pullbackSectionsLE, top_inf_eq] at ht
    exact i.mem_preimage.mp ht
  · obtain ⟨t, ht⟩ := isGloballyGenerated_iff.mp hB x
    refine ⟨(M.tensorProductObjIso B).symm.hom.app ⊤ (tmulRight M.obj t s), ?_⟩
    rw [nonvanishingLocus_hom_app (M.tensorProductObjIso B).symm,
      nonvanishingLocus_tmulRight]
    exact ⟨(M.mem_nonvanishingLocus_iff_notMem_support_zeroIdeal s x).mpr hx, ht⟩

end TauCeti.AlgebraicGeometry.InvertibleSheaf
