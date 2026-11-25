/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Incidence
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Picard
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.Chow.SurfaceIntersection.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
import QPainleve.AlgebraicGeometry.Blowup.Tower.Logarithmic.PolarCurve
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Chow.Birational
import QPainleve.AlgebraicGeometry.Chow.Nef.Cartier
import QPainleve.AlgebraicGeometry.Chow.ProjectivePlane.Basic
import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.IdealSheaf.ClosedImmersion
import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef.Pullback
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Integral
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Smooth
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample

/-!
# Degrees of polar curves in plane resolutions

The strict transform of a regular polar curve has degree zero or one against
the pullback of the line class of a specified plane target. In the total
exceptional basis this degree measures the difference between the original
degree and the sum of the orders on the successive strict transforms.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Module
open TauCeti.AlgebraicGeometry TauCeti.SymmetricAlgebra
open LineBundleClass Scheme.IdealSheafData Chow

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {n : ℕ} {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)

local notation "S" => Spec (CommRingCat.of k)
local notation "f" => (X ↘ S)
local notation "P" => Proj (homogeneousSubmodule k (Fin 3 → k))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) 1)
local notation "coords" => Pi.basisFun k (Fin 3)
local notation "polyIso" => Module.Basis.polynomialProjIso coords
local notation "H₀[" j "]" => Proj.coordinateHyperplaneIdeal (k := k) (n := 2) j
local notation "triangle" => radical (∏ j : Fin 3, H₀[j])
local notation "cl[" h "]" => (mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

private theorem exists_coordinateLine_comap_le {g : Y ⟶ P} {C E : Y.IdealSheafData}
    [IsIntegral C.subscheme] (hEC : E ≤ C) (hE : E.support ≤
      (comap triangle (g ≫ Iso.inv polyIso)).support) :
    ∃ j : Fin 3, (H₀[j]).comap (g ≫ Iso.inv polyIso) ≤ C := by
  let y := C.subschemeι (genericPoint C.subscheme)
  have hy : y ∈ C.support := by
    rw [← SetLike.mem_coe, ← C.range_subschemeι]
    exact Set.mem_range_self _
  have htriangle := hE (support_antitone hEC hy)
  simp only [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage,
    support_radical, Fin.prod_univ_three, support_mul, Closeds.coe_sup, Set.mem_union]
    at htriangle
  have hline : ∃ j : Fin 3, y ∈ ((H₀[j]).comap (g ≫ Iso.inv polyIso)).support := by
    simp only [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage]
    rcases htriangle with (h₀ | h₁) | h₂
    · exact ⟨0, h₀⟩
    · exact ⟨1, h₁⟩
    · exact ⟨2, h₂⟩
  obtain ⟨j, hj⟩ := hline
  refine ⟨j, ?_⟩
  rw [← C.ker_subschemeι, C.subschemeι.ker_eq_vanishingIdeal_closure_genericPoint,
    ← le_support_iff_le_vanishingIdeal]
  exact closure_minimal (Set.singleton_subset_iff.mpr hj)
    ((H₀[j]).comap (g ≫ Iso.inv polyIso)).support.isClosed

private theorem class_coordinateLine_comap (g : Y ⟶ P) (j : Fin 3)
    (hJ : ((H₀[j]).comap (g ≫ Iso.inv polyIso)).IsEffectiveCartier) :
    cl[hJ] = pullback g H := by
  have h₀ := Proj.isEffectiveCartier_coordinateHyperplaneIdeal (k := k) j
  rw [← h₀.pullback_mk_toInvertibleSheaf hJ, ← pullback_inv, inv_mk,
    Proj.mk_dual_coordinateHyperplaneIdeal,
    ← Module.Basis.pullback_mk_symmetricAlgebraTwistingBundle coords 1
      (Proj.polynomialTwistingBundle 1)
      (Proj.polynomialTwistingBundle_obj (k := k) (n := 2) 1),
    pullback_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable [IsAlgClosed k]

private theorem strictTransform_degree_of_triangle
    {C : X.IdealSheafData} [IsIntegral C.subscheme] [IsRegular C.subscheme]
    (hC : C.IsEffectiveCartier) (hdim : topologicalKrullDim C.subscheme = 1)
    (g : Y ⟶ P) (hg : g ≫ P ↘ S = T.toBase ≫ f) (hbir : Scheme.BirationalOver g (𝟙 P))
    {D : Y.IdealSheafData} (hDC : D ≤ T.strictTransform C)
    (htriangle : D.support ≤ (comap triangle (g ≫ Iso.inv polyIso)).support) :
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let : Y.Over S := ⟨T.toBase ≫ f⟩
    let hC' := hT.isEffectiveCartier_strictTransform f hC
    classIntersectionNumber k Y (pullback g H) (cl[hC']) = 0 ∨
      classIntersectionNumber k Y (pullback g H) (cl[hC']) = 1 := by
  intro hnoeth hOver hC'
  let := hnoeth
  let := hOver
  let : Y.IsProjectiveOver k := T.isProjectiveOver k
  let : IsIntegral Y := hT.isIntegral f
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f
  let : g.IsOver S := ⟨hg⟩
  let := (Y ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let a := hbir.partialIso
  let : IsDominant a.target.ι := Opens.isDominant_ι a.dense_target
  have hcomp : a.source.ι ≫ g = a.iso.hom ≫ a.target.ι := by
    symm
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using hbir.partialIso_isOver
  let : IsDominant (a.source.ι ≫ g) :=
    hcomp ▸ inferInstanceAs (IsDominant (a.iso.hom ≫ a.target.ι))
  let : IsDominant g := IsDominant.of_comp a.source.ι g
  obtain ⟨e, -⟩ := hT.exists_iso_strictTransform_regularCurve hdim
  let : IsIntegral (T.strictTransform C).subscheme := IsIntegral.of_isIso e.inv
  obtain ⟨j, hj⟩ := exists_coordinateLine_comap_le hDC htriangle
  let := Proj.isIntegral_polynomialProj (R := k) (σ := Fin 3)
  have hJ := (Proj.isEffectiveCartier_coordinateHyperplaneIdeal (k := k) j).comap_of_isDominant
    (g ≫ Iso.inv polyIso)
  have hdimY := topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y ↘ S) (n := 2)
  have hnef : (pullback g H).IsNef k (Y ↘ S) :=
    (isAmple_twistingSheaf k (Fin 3 → k) Nat.one_pos).isNef.pullback g
  have hsq : classIntersectionNumber k Y (pullback g H) (pullback g H) = 1 := by
    rw [g.classIntersectionNumber_pullback_of_birational (k := k) hbir,
      classIntersectionNumber_projectivePlane, Module.Basis.picardTwistEquiv_apply_twist]
    norm_num
  have hle := classIntersectionNumber_le_of_isNef_of_le_ideal k hdimY hnef hJ hC' hj
  rw [class_coordinateLine_comap g j hJ, hsq] at hle
  have hge := classIntersectionNumber_nonneg_of_isNef_of_isEffectiveCartier k hdimY hnef hC'
  omega

/-- In a logarithmic resolution of a birational map to the coordinate plane,
the sum of the line-system orders at the successive centers on a regular
polar curve is its original degree or one less. Membership in the sum is
tested on each strict transform before the next blowup. -/
theorem section_order_sum_of_triangle
    {C E : X.IdealSheafData} [IsIntegral C.subscheme] [IsRegular C.subscheme]
    (hC : C.IsEffectiveCartier) (hdim : topologicalKrullDim C.subscheme = 1) (hEC : E ≤ C)
    (g : Y ⟶ P) (hg : g ≫ P ↘ S = T.toBase ≫ f) (hbir : Scheme.BirationalOver g (𝟙 P))
    {D : Y.IdealSheafData}
    (hpole : E.comap T.toBase = D * hT.ramificationIdealSheafToBase k)
    (htriangle : D.support ≤ (comap triangle (g ≫ Iso.inv polyIso)).support) :
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let v := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    let a := classIntersectionNumber k X v.1.toMul (cl[hC])
    a - 1 ≤ ∑ j ∈ hT.strictTransformCenterIndices C, -v.2 j ∧
      (∑ j ∈ hT.strictTransformCenterIndices C, -v.2 j) ≤ a := by
  intro hnoeth v a
  let := hnoeth
  let : Y.Over S := ⟨T.toBase ≫ f⟩
  let hC' := hT.isEffectiveCartier_strictTransform f hC
  have hdeg := strictTransform_degree_of_triangle hT hC hdim g hg hbir
    (hT.le_strictTransform_of_pole_eq hdim hEC hpole) htriangle
  have hv : (T.picardMarking hT f v).toMul = pullback g H :=
    congrArg Additive.toMul ((T.picardMarking hT f).apply_symm_apply _)
  have hstrict : (T.picardMarking hT f
      (Additive.ofMul (cl[hC]), hT.strictTransformCoefficients C)).toMul = cl[hC'] :=
    congrArg Additive.toMul (hT.picardMarking_strictTransform f hC)
  have hpair := classIntersectionNumber_picardMarking k hT v
    (Additive.ofMul (cl[hC]), hT.strictTransformCoefficients C)
  simp only [hv, hstrict, toMul_ofMul] at hpair
  have hsum : (∑ j, v.2 j * hT.strictTransformCoefficients C j) =
      ∑ j ∈ hT.strictTransformCenterIndices C, -v.2 j := by
    simp only [hT.strictTransformCoefficients_eq_ite f hC hdim, mul_ite, mul_neg, mul_one,
      mul_zero, ← Finset.sum_filter, Finset.filter_univ_mem]
  rw [hsum] at hpair
  dsimp only at hdeg
  dsimp only [a]
  omega

end QPainleve.BlowupTower.IsClosedPointTower
