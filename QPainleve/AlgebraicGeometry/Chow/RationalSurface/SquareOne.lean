/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Plane

import QPainleve.AlgebraicGeometry.CartierDivisor.Pullback
import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
import QPainleve.AlgebraicGeometry.Chow.ProjectivePlane.Degree
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Effectivity
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.NakaiMoishezon
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import QPainleve.AlgebraicGeometry.IdealSheaf.ClosedImmersion
import QPainleve.AlgebraicGeometry.IntersectionNumber.Ample
import QPainleve.AlgebraicGeometry.IntersectionNumber.GlobalGeneration
import QPainleve.AlgebraicGeometry.Morphisms.Finite
import TauCeti.AlgebraicGeometry.Cohomology.Genus
import TauCeti.AlgebraicGeometry.Curves.ProjectiveLine

/-!
# The square-one branch of the minimal rational surface classification

A square-one projective-line divisor whose complete linear system consists of integral
divisors yields an isomorphism to the projective plane. Restricting sections to a
curve of degree zero gives at most a one-dimensional image. The curve therefore
lies in an integral member, forcing it to be that entire member and to have degree one.

See [Vakil, *Complex Algebraic Surfaces*, Class 17, §2][Vakil].

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass17A.pdf
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve TopologicalSpace
open Scheme.IdealSheafData Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open LineBundleClass

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [hProj : X.IsProjectiveOver k]
  [hSmooth : SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [hRat : Scheme.IsRationalOver (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "B" => Chow.classIntersectionNumber k X
local notation "K" => LineBundleClass.mk (canonicalBundle k X 2)
local notation "cl(" h ")" =>
  LineBundleClass.mk (InvertibleSheaf.dual (IsEffectiveCartier.toInvertibleSheaf h))

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

include hRat in
private theorem isAmple_of_self_pos_of_integral_members
    (L : InvertibleSheaf X)
    (hnef : (LineBundleClass.mk L).IsNef k (X ↘ S)) (hnum : 1 < Module.finrank k Γ(L.obj, ⊤))
    (hpos : 0 < B (LineBundleClass.mk L) (LineBundleClass.mk L))
    (hmem : ∀ (J : X.IdealSheafData) (hJ : J.IsEffectiveCartier),
      cl(hJ) = LineBundleClass.mk L → IsIntegral J.subscheme) :
    (LineBundleClass.mk L).IsAmple := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := hRat.isIntegral_of_smooth
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ S)
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  refine ((LineBundleClass.mk L).isAmple_iff_self_pos_and_intersectionNumber_pos).mpr
    ⟨hpos, fun {C} _ _ i _ hi ↦ ?_⟩
  have : i.IsOver S := ⟨hi.symm⟩
  have hnn := hnef.intersectionNumber_nonneg i hi
  by_contra! hn
  obtain ⟨s, hs, hzero⟩ :=
    L.exists_nonzero_section_of_intersectionNumber_eq_zero hnum i (le_antisymm hn hnn)
  let hD := L.isEffective_zeroDivisor hs
  let J := hD.idealSheaf
  let hJ := hD.isEffectiveCartier_idealSheaf
  have hclass : (LineBundleClass.mk hJ.toInvertibleSheaf)⁻¹ = LineBundleClass.mk L := by
    rw [hD.mk_idealSheaf_eq_inv, inv_inv, L.toLineBundleClass_zeroDivisor hs]
  have : IsIntegral J.subscheme := hmem J hJ (by rwa [← inv_mk])
  have hcomap : J.comap i = ⊥ := by
    have hJzero : J = L.zeroIdeal s := L.idealSheaf_zeroDivisor hs
    rw [hJzero, ← L.zeroIdeal_pullbackSections, hzero]
    exact zeroIdeal_zero _
  have hle : J.subschemeι.ker ≤ i.ker := by
    rw [J.ker_subschemeι, ← Scheme.IdealSheafData.map_bot, le_map_iff_comap_le, hcomap]
  let j := IsClosedImmersion.lift J.subschemeι i hle
  have hj : j ≫ J.subschemeι = i := IsClosedImmersion.lift_fac _ _ _
  have : IsClosedImmersion (j ≫ J.subschemeι) := hj.symm ▸ inferInstance
  have : IsClosedImmersion j := IsClosedImmersion.of_comp j J.subschemeι
  have hdim := Scheme.IsCurveOver.topologicalKrullDim_eq_one k (X := C)
  have hJdim := hJ.topologicalKrullDim_subscheme_le (d := 1) (by simpa using hX.le)
  have : IsDominant j := j.isDominant_of_isFinite_of_topologicalKrullDim_le
    (ne_top_of_le_ne_top (by decide : (1 : WithBot ℕ∞) ≠ ⊤) hJdim) (hdim ▸ hJdim)
  have : Surjective j :=
    ⟨Set.range_eq_univ.mp (j.isClosedEmbedding.isClosed_range.dense_iff.mp j.denseRange)⟩
  have : IsIso j := isIso_of_isClosedImmersion_of_surjective j
  have hker : i.ker = J := by rw [← hj, Scheme.Hom.ker_comp_of_isIso, J.ker_subschemeι]
  have hinter := Chow.classIntersectionNumber_eq_intersectionNumber_of_isEffectiveCartier_ker
    k hX.le i hdim (hker.symm ▸ hJ) (LineBundleClass.mk L)
  rw [mk_toInvertibleSheaf_congr _ hJ hker, hclass] at hinter
  omega

end TauCeti.AlgebraicGeometry.InvertibleSheaf

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

attribute [local instance] MvPolynomial.gradedAlgebra

variable {I : X.IdealSheafData}

include hRat in
private theorem nef_and_canonicalDegree_of_square_one
    (hI : I.IsEffectiveCartier) (e : I.subscheme ≅ projectiveLine k) [e.hom.IsOver S]
    (hsq : B cl(hI) cl(hI) = 1) :
    cl(hI).IsNef k (X ↘ S) ∧ B cl(hI) K = -3 := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := hRat.isIntegral_of_smooth
  have : IsIntegral I.subscheme := IsIntegral.of_isIso e.inv
  have : I.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  have : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have hdim : topologicalKrullDim I.subscheme = 1 :=
    e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := projectiveLine k) k)
  have : I.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, hdim⟩
  let p : CodimensionOnePoint X := ⟨I.subschemeι (genericPoint I.subscheme),
    I.subschemeι.coheight_apply_genericPoint_eq_one_of_dim_eq_two k hX hdim⟩
  have hIeq := I.ker_subschemeι.symm.trans I.subschemeι.ker_eq_vanishingIdeal_closure_genericPoint
  have hp : primeDivisorClass p = cl(hI) := by
    rw [primeDivisorClass_def, ← inv_mk, mk_toInvertibleSheaf_congr _ hI hIeq.symm]
  have hnef : cl(hI).IsNef k (X ↘ S) :=
    (Chow.isNef_iff_classIntersectionNumber_nonneg k hX _).mpr fun q ↦ by
      by_cases he : q = p
      · rw [he, hp, hsq]
        decide
      · rw [← hp]
        exact Chow.classIntersectionNumber_primeDivisorClass_nonneg_of_ne k hX (Ne.symm he)
  have hg : I.subscheme.genus k = 0 :=
    Scheme.genus_eq_zero_iff_exists_iso_projectiveLine.mpr ⟨e, inferInstance⟩
  have hcan := I.subschemeι.two_mul_genus_sub_two_eq_intersection_of_isRationalOver k
  dsimp only at hcan
  rw [mk_toInvertibleSheaf_congr _ hI I.ker_subschemeι, inv_mk, hg, hsq] at hcan
  exact ⟨hnef, by omega⟩

include hRat in
private theorem one_lt_finrank_globalSections_of_square_one (L : InvertibleSheaf X)
    (hnef : (LineBundleClass.mk L).IsNef k (X ↘ S))
    (hsq : B (LineBundleClass.mk L) (LineBundleClass.mk L) = 1)
    (hcan : B (LineBundleClass.mk L) K = -3) :
    1 < Module.finrank k Γ(L.obj, ⊤) := by
  have := X.subsingleton_cohomology_two_of_isNef_of_isRationalOver k L hnef
  have hχ := eulerCharBelow_eq_riemannRoch_of_isRationalOver k (LineBundleClass.mk L)
  rw [eulerCharBelow_mk, Scheme.Modules.eulerCharBelow_succ, Scheme.Modules.eulerCharBelow_two,
    finrank_cohomology_zero_eq_finrank_globalSections, Module.finrank_zero_of_subsingleton
      (M := Cohomology L.obj 2), hsq, hcan] at hχ
  omega

include hRat in
/-- A square-one projective-line divisor whose complete linear system has integral
members identifies the surface with the projective plane over the base field.
The hyperplane class pulls back to the class of the given divisor. -/
theorem exists_iso_projectivePlane_of_square_one_linear_system
    (hI : I.IsEffectiveCartier) (e : I.subscheme ≅ projectiveLine k) [e.hom.IsOver S]
    (hsq : B cl(hI) cl(hI) = 1)
    (hmem : ∀ (J : X.IdealSheafData) (hJ : J.IsEffectiveCartier),
      cl(hJ) = cl(hI) → IsIntegral J.subscheme) :
    let 𝒜 := MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 3)) k
    let H : InvertibleSheaf (Proj 𝒜) := ⟨Proj.twistingSheaf 𝒜 1, inferInstance⟩
    ∃ E : X ≅ Proj 𝒜, E.hom ≫ Proj.toSpecCoeff 𝒜 = X ↘ S ∧
      LineBundleClass.pullback E.hom (LineBundleClass.mk H) = cl(hI) := by
  intro 𝒜 H
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := hRat.isIntegral_of_smooth
  have : IsRegular X := IsRegular.of_smooth (X ↘ S)
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  let L := hI.toInvertibleSheaf.dual
  obtain ⟨hnef, hcan⟩ := hI.nef_and_canonicalDegree_of_square_one e hsq
  have hdim := one_lt_finrank_globalSections_of_square_one L hnef hsq hcan
  have hA := L.isAmple_of_self_pos_of_integral_members hnef hdim (hsq ▸ zero_lt_one) hmem
  obtain ⟨hglob, hnum⟩ := L.isGloballyGenerated_and_finrank_globalSections_eq_three_of_self_eq_one
    hA hsq hcan
  obtain ⟨f, hf, hfin, ha⟩ := L.exists_finite_to_projectivePlane hA hglob hnum
  have : f.IsOver S := ⟨hf⟩
  have : IsIso f := (f.isIso_iff_hyperplane_pullback_square_eq_one hX.ge Equiv.ulift).mpr (by
    change B (pullback f (LineBundleClass.mk H)) (pullback f (LineBundleClass.mk H)) = 1
    rw [ha]
    exact hsq)
  exact ⟨asIso f, hf, ha⟩

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
