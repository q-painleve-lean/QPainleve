/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import QPainleve.AlgebraicGeometry.IdealSheaf.Tensor.SectionLifting
public import QPainleve.LinearAlgebra.BilinearForm.Primitive
public import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine

import QPainleve.AlgebraicGeometry.Curves.GenusZero
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Cohomology

/-!
# Line bundles of degree one along rational rulings

On a smooth projective rational surface, a projective-line divisor of square zero
has primitive class. The perfect Picard pairing then gives a line bundle of
degree one on every projective-line divisor in that class.

See [Vakil, *Complex Algebraic Surfaces*, Class 17, §2][Vakil] for the ruled case
of the classification of minimal rational surfaces.

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass17A.pdf#page=4
-/

public section

open AlgebraicGeometry CategoryTheory Filter QPainleve
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.LineBundleClass

universe u

variable {k : Type u} [Field k]
local notation "S" => Spec (CommRingCat.of k)
local notation "L[" h "]" => Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf h
local notation "A(" h ")" => (LineBundleClass.mk L[h])⁻¹
local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k)
local notation "B[" X "]" => Chow.classIntersectionNumber k X

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {X : Scheme.{u}} [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [IsAlgClosed k] [hRat : Scheme.IsRationalOver (X ↘ Spec (.of k))]
  {I : X.IdealSheafData}

include hRat in
/-- A square-zero Cartier divisor is primitive in the Picard group of a smooth projective
rational surface if the divisor is a projective line. -/
theorem isPrimitive_of_selfIntersection_eq_zero_of_projectiveLine
    (hI : I.IsEffectiveCartier)
    (e : I.subscheme ≅ projectiveLine k) [e.hom.IsOver S]
    (hI₂ : B[X] (A(hI)) (A(hI)) = 0) :
    TauCeti.IsPrimitive (Additive.ofMul (A(hI))) := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := hRat.isIntegral_of_smooth
  have : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have : Module.Free ℤ (Additive (LineBundleClass X)) := X.free_picard_of_isRationalOver k
  have : I.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
  have : I.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨IsIntegral.of_isIso e.inv, inferInstance,
      e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
        (Scheme.IsCurveOver.topologicalKrullDim_eq_one k)⟩
  have hgen : I.subscheme.genus k = 0 :=
    Scheme.genus_eq_zero_iff_exists_iso_projectiveLine.mpr ⟨e, inferInstance⟩
  have hadj := I.subschemeι.two_mul_genus_sub_two_eq_intersection_of_isRationalOver k
  dsimp only at hadj
  rw [mk_toInvertibleSheaf_congr _ hI I.ker_subschemeι, hI₂, hgen] at hadj
  let Q := Chow.classIntersectionBilinForm k
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2))
  let F := Additive.ofMul (A(hI))
  let K := Additive.ofMul (LineBundleClass.mk (canonicalBundle k X 2))
  have hFF : Q F F = 0 := by
    simpa only [Q, F, Chow.classIntersectionBilinForm_apply, toMul_ofMul] using hI₂
  have hKF : Q K F = -2 := by
    simp only [Q, K, F, Chow.classIntersectionBilinForm_apply, toMul_ofMul,
      Chow.classIntersectionNumber_comm (LineBundleClass.mk (canonicalBundle k X 2))]
    omega
  have hchar : Q.IsCharacteristic K := Chow.isCharacteristic_canonicalBundle_of_isRationalOver k X
  exact hchar.isPrimitive_of_apply_eq_neg_two hFF hKF

include hRat in
/-- On a smooth projective rational surface, a square-zero projective-line divisor
has intersection number one with some line bundle. -/
theorem exists_line_bundle_classIntersectionNumber_eq_one_of_projectiveLine
    (hI : I.IsEffectiveCartier) (e : I.subscheme ≅ projectiveLine k) [e.hom.IsOver S]
    (hI₂ : B[X] (A(hI)) (A(hI)) = 0) :
    ∃ L : InvertibleSheaf X, B[X] (LineBundleClass.mk L) (A(hI)) = 1 := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := hRat.isIntegral_of_smooth
  have : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  let Q := Chow.classIntersectionBilinForm k hX
  have : Q.IsPerfPair := Chow.isPerfPair_classIntersectionBilinForm_of_isRationalOver k X
  obtain ⟨φ, hφ⟩ := TauCeti.isPrimitive_def.mp
    (hI.isPrimitive_of_selfIntersection_eq_zero_of_projectiveLine e hI₂)
  let a := Q.toPerfPair.symm φ
  obtain ⟨L, hL⟩ := mk_surjective a.toMul
  refine ⟨L, ?_⟩
  have h : Q a (Additive.ofMul (A(hI))) = 1 :=
    (DFunLike.congr_fun (Q.apply_symm_toPerfPair_self φ) _).trans hφ
  simpa only [Q, Chow.classIntersectionBilinForm_apply, toMul_ofMul, ← hL] using h

include hRat in
/-- On a smooth projective rational surface, a square-zero projective-line divisor
admits a line bundle of fiber degree one. This single bundle restricts to
`𝒪(1)` on every projective-line divisor in the same class, and sufficiently
large positive twists along each such divisor lift all its sections. -/
theorem exists_line_bundle_of_fiber_degree_one (hI : I.IsEffectiveCartier)
    (e : I.subscheme ≅ projectiveLine k) [e.hom.IsOver S]
    (hI₂ : B[X] (A(hI)) (A(hI)) = 0) :
    ∃ L : InvertibleSheaf X, ∀ {J : X.IdealSheafData} (hJ : J.IsEffectiveCartier),
      A(hJ) = A(hI) → ∀ (e' : projectiveLine k ≅ J.subscheme), e'.hom.IsOver S →
        Nonempty (((InvertibleSheaf.pullback (e'.hom ≫ J.subschemeι)).obj L).obj ≅
          Proj.twistingSheaf 𝒜 1) ∧
        ∀ᶠ n : ℕ in atTop, Function.Surjective (J.subschemeι.pullbackSectionsLE
          (L.tensorProduct (L[hJ].dual.tensorPow n)).obj ⊤ ⊤ (by simp)) := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := hRat.isIntegral_of_smooth
  have : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  obtain ⟨L, hLF⟩ := hI.exists_line_bundle_classIntersectionNumber_eq_one_of_projectiveLine e hI₂
  refine ⟨L, fun {J} hJ hJI e' he' ↦ ?_⟩
  let : e'.hom.IsOver S := he'
  let i := e'.hom ≫ J.subschemeι
  have hker : i.ker = J := (Scheme.Hom.ker_comp_of_isIso _ _).trans J.ker_subschemeι
  have hi : i.ker.IsEffectiveCartier := hker ▸ hJ
  have hdeg (x : LineBundleClass X) : intersectionNumber k i x = B[X] x (A(hJ)) := by
    rw [← Chow.classIntersectionNumber_eq_intersectionNumber_of_isEffectiveCartier_ker k hX.le i
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one k) hi,
      mk_toInvertibleSheaf_congr _ hJ hker]
  have hL₁ : intersectionNumber k i (LineBundleClass.mk L) = 1 := by
    rw [hdeg, hJI, hLF]
  refine ⟨(projectiveLine.nonempty_iso_twistingSheaf_iff k _ _).mpr
    ((intersectionNumber_mk k i L).symm.trans hL₁), ?_⟩
  have hzero : eulerDegree k (pullback i (A(hJ))) = 0 := by
    rw [← intersectionNumber_def, hdeg, hJI, hI₂]
  have ht : pullback i (A(hJ)) = 1 := by
    apply Additive.ofMul.injective
    apply (projectiveLine.picardDegreeEquiv k).injective
    simp only [projectiveLine.picardDegreeEquiv_apply, toMul_ofMul, eulerDegree_one, hzero]
  have ht' : pullback J.subschemeι (LineBundleClass.mk L[hJ]) = 1 := by
    have h := congrArg (pullback e'.inv) ht
    have hcomp : e'.inv ≫ i = J.subschemeι := e'.inv_hom_id_assoc _
    rw [pullback_comp e'.inv i, hcomp, pullback_one, pullback_inv] at h
    exact inv_eq_one.mp h
  exact hJ.eventually_surjective_pullbackSectionsLE_of_trivial_conormal (k := k) L ht'
    (J.subsingleton_cohomology_one_tensor_pushforwardSubscheme_of_projectiveLine L e'
      (by rw [hL₁]; decide))

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
