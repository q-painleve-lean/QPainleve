/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical

import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear

/-!
# Invariance of surface intersection under isomorphism

The Euler characteristic and the resulting intersection pairing commute with
pullback along scheme isomorphisms over the coefficient field. This lets one
compare the Picard pairings computed in different models of the same surface.
On smooth surfaces the canonical class also pulls back, giving invariance
of the Riemann–Roch equation for a line bundle.
-/

public section

open AlgebraicGeometry CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  (f : X ⟶ Y) [IsIso f] [f.IsOver (Spec (.of k))]

/-- Pullback along an isomorphism preserves the truncated Euler characteristic of a
line-bundle class, for every cutoff. -/
theorem LineBundleClass.eulerCharBelow_pullback_of_isIso (a : LineBundleClass Y) (q : ℕ) :
    eulerCharBelow k (pullback f a) q = eulerCharBelow k a q := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  rw [pullback_mk, eulerCharBelow_mk, eulerCharBelow_mk, InvertibleSheaf.pullback_obj_obj,
    Scheme.Hom.eulerCharBelow_pullback_of_isIso]

/-- Pullback along an isomorphism preserves the Euler-characteristic intersection pairing. -/
theorem Chow.classIntersectionNumber_pullback_of_isIso (a b : LineBundleClass Y) :
    classIntersectionNumber k X (LineBundleClass.pullback f a) (LineBundleClass.pullback f b) =
      classIntersectionNumber k Y a b := by
  simp only [classIntersectionNumber_eq, ← LineBundleClass.pullback_inv,
    ← LineBundleClass.pullback_mul, LineBundleClass.eulerCharBelow_pullback_of_isIso k f,
    ← LineBundleClass.pullback_one f]

namespace Chow

variable [Infinite k] [IsIntegral X] [IsIntegral Y] [X.IsProjectiveOver k] [Y.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  (e : X ≅ Y) [e.hom.IsOver (Spec (.of k))]

/-- Pullback along an isomorphism of smooth projective surfaces is an isometry of
their integral Picard intersection forms. -/
noncomputable def picardPullbackIsometry :
    (intersectionBilinForm k Y).IsometryEquiv (intersectionBilinForm k X) where
  toLinearEquiv := (LineBundleClass.pullbackEquiv e).toAdditive.toIntLinearEquiv
  map_app' a b := by
    simpa only [intersectionBilinForm_apply, LinearEquiv.toFun_eq_coe,
      AddEquiv.coe_toIntLinearEquiv,
      MulEquiv.toAdditive_apply_apply, LineBundleClass.pullbackEquiv_apply, toMul_ofMul] using
      classIntersectionNumber_pullback_of_isIso k e.hom a.toMul b.toMul

/-- The Picard isometry of a surface isomorphism sends a line-bundle class to its pullback. -/
@[simp]
theorem picardPullbackIsometry_apply (x : Additive (LineBundleClass Y)) :
    picardPullbackIsometry k e x = Additive.ofMul (LineBundleClass.pullback e.hom x.toMul) :=
  congrArg Additive.ofMul (LineBundleClass.pullbackEquiv_apply e x.toMul)

end Chow

namespace LineBundleClass

open QPainleve

variable [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]

/-- The doubled Riemann–Roch equation for the pullback of a line bundle along a surface
isomorphism is equivalent to the equation for the original line bundle. -/
theorem eulerCharBelow_eq_riemannRoch_pullback_iff_of_isIso (a : LineBundleClass Y) :
    let KX := mk (canonicalBundle k X 2)
    let KY := mk (canonicalBundle k Y 2)
    let B := Chow.classIntersectionNumber k X
    let C := Chow.classIntersectionNumber k Y
    let b := pullback f a
    2 * (eulerCharBelow k b 3 - eulerCharBelow k (1 : LineBundleClass X) 3) =
      B b b - B b KX ↔
    2 * (eulerCharBelow k a 3 - eulerCharBelow k (1 : LineBundleClass Y) 3) =
      C a a - C a KY := by
  have hK : pullback f (mk (canonicalBundle k Y 2)) = mk (canonicalBundle k X 2) := by
    rw [pullback_mk, mk_pullback_canonicalBundle]
  dsimp only
  rw [← hK, ← pullback_one f]
  simp only [eulerCharBelow_pullback_of_isIso, Chow.classIntersectionNumber_pullback_of_isIso]

end LineBundleClass

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

open TauCeti.AlgebraicGeometry LineBundleClass LinearMap.BilinForm

variable {k : Type u} [Field k] [Infinite k] {X Y : Scheme.{u}}
  [IsIntegral X] [IsIntegral Y] [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [Y.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]

/-- Pullback along an isomorphism over the ground field identifies the two boundary
orthogonals when the boundary supports correspond. -/
theorem pullback_mem_boundaryOrthogonal_iff (D : X.IdealSheafData) (E : Y.IdealSheafData)
    (f : X ⟶ Y) [IsIso f] [f.IsOver (Spec (.of k))]
    (h : (E.comap f).support = D.support) (L : LineBundleClass Y) :
    Additive.ofMul (pullback f L) ∈ D.boundaryOrthogonal k ↔
      Additive.ofMul L ∈ E.boundaryOrthogonal k := by
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  let : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ Spec (.of k))
  let := (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := (Y ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let U := E.support.compl
  have hU : f ⁻¹ᵁ U = D.support.compl := (E.compl_support_comap f).symm.trans (congrArg _ h)
  have hspan (M : LineBundleClass Y) :
      Additive.ofMul (pullback f M) ∈ Scheme.Opens.primeDivisorSpanCompl D.support.compl ↔
        Additive.ofMul M ∈ Scheme.Opens.primeDivisorSpanCompl U := by
    rw [← hU, ← Submodule.Quotient.mk_eq_zero, ← Submodule.Quotient.mk_eq_zero,
      ← f.quotientPrimeDivisorSpanComplEquiv_mk, LinearEquiv.map_eq_zero_iff]
  have hsurj : Function.Surjective
      (fun M : LineBundleClass Y ↦ Additive.ofMul (pullback f M)) :=
    Additive.ofMul.surjective.comp (pullback_surjective_of_isOpenImmersion f)
  have hsurj' : Function.Surjective (Additive.ofMul : LineBundleClass Y → _) :=
    Additive.ofMul.surjective
  rw [D.boundaryOrthogonal_def, E.boundaryOrthogonal_def, mem_orthogonal_iff, mem_orthogonal_iff,
    hsurj.forall, hsurj'.forall]
  simp only [hspan, U, Chow.intersectionBilinForm_apply, toMul_ofMul,
    Chow.classIntersectionNumber_pullback_of_isIso k f]

end AlgebraicGeometry.Scheme.IdealSheafData
