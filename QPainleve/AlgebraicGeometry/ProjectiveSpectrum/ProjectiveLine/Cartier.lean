/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.ClosedImmersion
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine

import QPainleve.AlgebraicGeometry.IntersectionNumber.ClosedPoint
import QPainleve.AlgebraicGeometry.RationalPoint
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Cartier fibers over the projective line

The scheme-theoretic fiber of a flat morphism over a closed point of the projective line
over an algebraically closed field is an effective Cartier divisor. Its associated line
bundle has class given by the pullback of the degree-one twisting bundle.
-/

public section

open CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Over an algebraically closed field, every closed fiber of a flat morphism to the
projective line is effective Cartier with divisor class the pullback of `𝒪(1)`. -/
theorem exists_cartier_fiber_class_eq_pullback_twistingBundle
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ projectiveLine k) [Flat f] {y : projectiveLine k}
    (hy : IsClosed ({y} : Set (projectiveLine k))) :
    ∃ h : (f.fiberι y).ker.IsEffectiveCartier,
      (LineBundleClass.mk h.toInvertibleSheaf)⁻¹ =
        pullback f (LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle k (Fin 2 → k) 1)) := by
  let P := projectiveLine k
  let j := P.fromSpecResidueField y
  have : IsClosedImmersion j := isClosed_singleton_iff_isClosedImmersion.mp hy
  have : TauCeti.AlgebraicGeometry.IsRegular P := ⟨fun _ ↦ inferInstance⟩
  have hP := P.isEffectiveCartier_ker_fromSpecResidueField_of_dim_eq_one hy
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one k)
  have ht : (LineBundleClass.mk hP.toInvertibleSheaf)⁻¹ =
      LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle k (Fin 2 → k) 1) := by
    apply Additive.ofMul.injective
    apply (projectiveLine.picardDegreeEquiv k).injective
    rw [projectiveLine.picardDegreeEquiv_apply, projectiveLine.picardDegreeEquiv_apply,
      toMul_ofMul, toMul_ofMul,
      projectiveLine.eulerDegree_inv, eulerDegree_mk_ker_fromSpecResidueField hy,
      (P ↘ Spec (.of k)).residueDegree_eq_one_of_isClosed hy, Nat.cast_one, neg_neg,
      eulerDegree_mk]
    exact (projectiveLine.eulerDegree_twistingSheaf k 1).symm
  have hker : (f.fiberι y).ker = j.ker.comap f :=
    IdealSheafData.ker_fst_of_isClosedImmersion j f
  have hJ := hP.comap f
  let h : (f.fiberι y).ker.IsEffectiveCartier := hker ▸ hJ
  refine ⟨h, ?_⟩
  rw [mk_toInvertibleSheaf_congr h hJ hker, ← ht, pullback_inv,
    hP.pullback_mk_toInvertibleSheaf hJ]

end AlgebraicGeometry.Scheme.Hom
