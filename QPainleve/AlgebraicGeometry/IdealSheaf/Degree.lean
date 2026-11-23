/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Degree of the restriction of a closed point ideal

On a projective scheme over an algebraically closed field, the Cartier restriction
of a reduced closed point ideal along a closed immersion has Euler degree determined
by whether the image contains the point.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open LineBundleClass Scheme.IdealSheafData

universe u

namespace QPainleve

variable (k : Type u) [Field k] [hk : IsAlgClosed k]
  {C D : Scheme.{u}} [C.Over (Spec (.of k))] [hProj : C.IsProjectiveOver k]
  (e : C ⟶ D) [heClosed : IsClosedImmersion e]

include hk hProj heClosed in
/-- The Cartier ideal obtained by restricting a reduced closed point along a closed
immersion into its ambient scheme has degree minus one if the point lies in the image
and degree zero otherwise. -/
theorem eulerDegree_mk_comap_point (p : D) (hp : IsClosed ({p} : Set D))
    (h : ((D.fromSpecResidueField p).ker.comap e).IsEffectiveCartier)
    [Decidable (p ∈ Set.range e)] :
    eulerDegree k (mk h.toInvertibleSheaf) = if p ∈ Set.range e then -1 else 0 := by
  by_cases hmem : p ∈ Set.range e
  · obtain ⟨q, rfl⟩ := hmem
    have hq : IsClosed ({q} : Set C) := by
      apply e.isClosedEmbedding.isClosed_iff_image_isClosed.mpr
      simpa only [Set.image_singleton] using hp
    let s := C.fromSpecResidueField q
    have hs : IsClosedImmersion s := isClosed_singleton_iff_isClosedImmersion.mp hq
    have hker : (D.fromSpecResidueField (e q)).ker.comap e = s.ker :=
      e.comap_ker_fromSpecResidueField_apply q
    have hC : s.ker.IsEffectiveCartier := hker ▸ h
    let f := C ↘ Spec (CommRingCat.of k)
    have : IsIso (s ≫ f) := by
      rw [← SpecMap_residueFieldIsoBase_inv f q hq]
      infer_instance
    have : IsIso (s.ker.subschemeι ≫ f) := by
      rw [← isIso_comp_left_iff s.toImage, ← Category.assoc, Scheme.Hom.toImage_imageι]
      infer_instance
    have := Scheme.Modules.moduleFinite_cohomology_of_isProjectiveOver k
      (InvertibleSheaf.trivial C).obj 0
    have := Scheme.Modules.moduleFinite_cohomology_of_isProjectiveOver k
      (InvertibleSheaf.trivial C).obj 1
    rw [mk_toInvertibleSheaf_congr h hC hker, eulerDegree_mk,
      hC.eulerDegree_toInvertibleSheaf k _ default, Scheme.Hom.finrank_eq_one_of_isIso]
    simp
  · have htop : (D.fromSpecResidueField p).ker.comap e = ⊤ := by
      rw [comap_eq_top_iff, ← Opens.coe_eq_univ, Scheme.Hom.coe_preimage,
        Closeds.coe_compl, Scheme.support_ker_fromSpecResidueField_of_isClosed hp,
        Set.eq_univ_iff_forall]
      exact fun q hq ↦ hmem ⟨q, hq⟩
    rw [mk_toInvertibleSheaf_congr h (isEffectiveCartier_top C) htop,
      mk_toInvertibleSheaf_top, eulerDegree_one, ite_eq_right hmem]

end QPainleve
