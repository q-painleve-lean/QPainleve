/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.SurfaceIntersection.Basic
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.ClosedImmersion
public import QPainleve.AlgebraicGeometry.CartierDivisor.Excision
public import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
public import QPainleve.AlgebraicGeometry.Scheme.LocalDimension
import TauCeti.AlgebraicGeometry.Curves.Normalization
import TauCeti.AlgebraicGeometry.LineBundle.BaseChange
import QPainleve.AlgebraicGeometry.Cohomology.Support
import QPainleve.AlgebraicGeometry.IdealSheaf.ClosedImmersion
import QPainleve.AlgebraicGeometry.IdealSheaf.EulerCharacteristic
import QPainleve.AlgebraicGeometry.IdealSheaf.Image.Over

/-!
# Surface intersection and restriction to a curve

The surface intersection pairing with the class of a Cartier curve is the degree
of the restricted line bundle. Twisting by the curve changes the pairing by that
same degree, independently of the starting twist. Distinct prime divisors meet
nonnegatively, and intersection with a Weil divisor class is the sum over its components.
The prime curves supported on a boundary ideal define an orthogonal sublattice.

## References

* O. Debarre, *Introduction to Mori Theory*, §3.2, Theorem 3.6 and formula (3.3).
* The Stacks Project, Definition 33.45.3 (tag 0BEP).
* Tau Ceti's `LineBundleClass.intersectionNumber_inv_mk_toInvertibleSheaf_nonneg`
  for nonnegativity of proper intersections.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open TauCeti
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry.Chow

section

variable (k : Type u) [Field k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

/-- The integer intersection matrix of an indexed family of prime divisors. -/
public noncomputable def primeIntersectionMatrix {ι : Type*} (p : ι → CodimensionOnePoint X) :
    Matrix ι ι ℤ :=
  Matrix.of fun i j ↦
    classIntersectionNumber k X (LineBundleClass.primeDivisorClass (p i))
      (LineBundleClass.primeDivisorClass (p j))

/-- An entry pairs the prime classes at the chosen row and column indices. -/
@[simp]
public theorem primeIntersectionMatrix_apply {ι : Type*} (p : ι → CodimensionOnePoint X)
    (i j : ι) :
    primeIntersectionMatrix k p i j =
      classIntersectionNumber k X (LineBundleClass.primeDivisorClass (p i))
        (LineBundleClass.primeDivisorClass (p j)) :=
  (rfl)

end

section

variable (k : Type u) [Field k] [Infinite k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]

private theorem eulerCharBelow_three_eq_two {C : Scheme.{u}}
    [C.Over (Spec (.of k))] [C.IsProjectiveOver k] (hC : topologicalKrullDim C = 1)
    (a : LineBundleClass C) :
    LineBundleClass.eulerCharBelow k a 3 = LineBundleClass.eulerCharBelow k a 2 := by
  obtain ⟨L, rfl⟩ := LineBundleClass.mk_surjective a
  have := subsingleton_cohomology_of_projective_dim_lt (k := k) L.obj (q := 2) (by rw [hC]; decide)
  simp only [LineBundleClass.eulerCharBelow_mk, eulerCharBelow_succ k L.obj 2,
    Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero, add_zero]

omit [Infinite k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k] in
private theorem intersectionNumber_eq_eulerCharBelow_sub {C : Scheme.{u}}
    [C.Over (Spec (.of k))] (i : C ⟶ X) (a : LineBundleClass X) :
    LineBundleClass.intersectionNumber k i a =
      LineBundleClass.eulerCharBelow k (LineBundleClass.pullback i a) 2 -
      LineBundleClass.eulerCharBelow k (1 : LineBundleClass C) 2 := by
  obtain ⟨L, rfl⟩ := LineBundleClass.mk_surjective a
  rw [LineBundleClass.intersectionNumber_mk_eq_eulerCharBelow_sub,
    LineBundleClass.pullback_mk, LineBundleClass.eulerCharBelow_mk,
    ← LineBundleClass.eulerCharBelow_mk k ((InvertibleSheaf.pullback i).obj
      (InvertibleSheaf.trivial X)), ← LineBundleClass.pullback_mk,
    LineBundleClass.mk_trivial, LineBundleClass.pullback_one]

/-- Twisting the second class by an integral effective Cartier curve adds the
degree of the first class restricted to that curve. -/
public theorem classIntersectionNumber_mul_inv_mk_toInvertibleSheaf
    (hX : topologicalKrullDim X ≤ 2) {I : X.IdealSheafData} (hI : I.IsEffectiveCartier)
    [IsIntegral I.subscheme] (hC : topologicalKrullDim I.subscheme = 1)
    (a b : LineBundleClass X) :
    classIntersectionNumber k X a (b * (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹) =
      classIntersectionNumber k X a b + LineBundleClass.intersectionNumber k I.subschemeι a := by
  have : I.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
  have hdim : topologicalKrullDim X < 3 := hX.trans_lt (by decide)
  have hχ (c : LineBundleClass X) :=
    hI.eulerCharBelow_eq_add_restriction (k := k) c hdim
  simp only [eulerCharBelow_three_eq_two k hC] at hχ
  have hdeg := LineBundleClass.intersectionNumber_mul_of_isClosedImmersion k I.subschemeι
    (comp_over I.subschemeι _).symm hC a⁻¹ b⁻¹
  rw [LineBundleClass.intersectionNumber_inv_of_isClosedImmersion k I.subschemeι
    (comp_over I.subschemeι _).symm hC a] at hdeg
  simp only [intersectionNumber_eq_eulerCharBelow_sub k I.subschemeι] at hdeg
  rw [classIntersectionNumber_eq, classIntersectionNumber_eq, mul_inv_rev, inv_inv,
    mul_comm (LineBundleClass.mk hI.toInvertibleSheaf) b⁻¹, ← mul_assoc,
    intersectionNumber_eq_eulerCharBelow_sub]
  linarith [hχ b⁻¹, hχ (a⁻¹ * b⁻¹)]

/-- Twisting by any integral multiple of an integral effective Cartier curve adds that multiple
of the degree of restriction. -/
public theorem classIntersectionNumber_mul_zpow_inv_mk_toInvertibleSheaf
    (hX : topologicalKrullDim X ≤ 2) {I : X.IdealSheafData} (hI : I.IsEffectiveCartier)
    [IsIntegral I.subscheme] (hC : topologicalKrullDim I.subscheme = 1)
    (a b : LineBundleClass X) (n : ℤ) :
    classIntersectionNumber k X a (b * (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ ^ n) =
      classIntersectionNumber k X a b +
        n * LineBundleClass.intersectionNumber k I.subschemeι a := by
  let e := (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
  have hadd (x : LineBundleClass X) :
      classIntersectionNumber k X a (x * e) =
        classIntersectionNumber k X a x + LineBundleClass.intersectionNumber k I.subschemeι a :=
    classIntersectionNumber_mul_inv_mk_toInvertibleSheaf k hX hI hC a x
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, ← mul_assoc, hadd, ih, add_mul, one_mul, add_assoc]
  | pred n ih =>
    have hstep := hadd (b * e ^ (-(n : ℤ) - 1))
    rw [mul_assoc, mul_zpow_self, sub_add_cancel, ih] at hstep
    dsimp only [e] at hstep
    rw [sub_mul, one_mul]
    omega

/-- The surface intersection with the class of an integral effective Cartier curve equals
the degree of restriction to that curve. -/
public theorem classIntersectionNumber_eq_intersectionNumber_subschemeι
    (hX : topologicalKrullDim X ≤ 2) {I : X.IdealSheafData} (hI : I.IsEffectiveCartier)
    [IsIntegral I.subscheme] (hC : topologicalKrullDim I.subscheme = 1) (a : LineBundleClass X) :
    classIntersectionNumber k X a (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ =
      LineBundleClass.intersectionNumber k I.subschemeι a := by
  simpa only [one_mul, classIntersectionNumber_one_right, zero_add] using
    classIntersectionNumber_mul_inv_mk_toInvertibleSheaf k hX hI hC a 1

/-- The surface intersection with a closed integral Cartier curve equals the degree on the
given curve, with its specified immersion over the base field. -/
public theorem classIntersectionNumber_eq_intersectionNumber_of_isEffectiveCartier_ker
    (hX : topologicalKrullDim X ≤ 2) {C : Scheme.{u}} [C.Over (Spec (.of k))]
    [IsIntegral C] (i : C ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (hC : topologicalKrullDim C = 1) (hi : i.ker.IsEffectiveCartier) (a : LineBundleClass X) :
    classIntersectionNumber k X a (LineBundleClass.mk hi.toInvertibleSheaf)⁻¹ =
      LineBundleClass.intersectionNumber k i a := by
  have hdim := IsHomeomorph.topologicalKrullDim_eq _ i.toImage.homeomorph.isHomeomorph
  have : IsIntegral i.ker.subscheme := IsIntegral.of_isIso i.toImage
  rw [classIntersectionNumber_eq_intersectionNumber_subschemeι k hX hi (hdim.symm.trans hC)]
  calc
    _ = LineBundleClass.intersectionNumber k (i.toImage ≫ i.imageι) a := by
      rw [← LineBundleClass.intersectionNumber_pullback]
      simp only [LineBundleClass.intersectionNumber_def]
      exact (LineBundleClass.eulerDegree_pullback_of_isIso (k := k)
        i.toImage (comp_over i.toImage _) _).symm
    _ = _ := by rw [i.toImage_imageι]

/-- On a regular integral projective surface, intersection with the class of any closed integral
curve equals degree on the curve. Its class is the inverse of the class of its ideal sheaf. -/
public theorem classIntersectionNumber_eq_intersectionNumber
    [IrreducibleSpace X] [IsRegular X] (hX : topologicalKrullDim X = 2)
    {C : Scheme.{u}} [C.Over (Spec (.of k))] [IsIntegral C]
    (i : C ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (hC : topologicalKrullDim C = 1) (a : LineBundleClass X) :
    classIntersectionNumber k X a
        (LineBundleClass.mk
          (i.isEffectiveCartier_ker_of_isRegular_of_dim_eq_two k hX hC).toInvertibleSheaf)⁻¹ =
      LineBundleClass.intersectionNumber k i a :=
  classIntersectionNumber_eq_intersectionNumber_of_isEffectiveCartier_ker k hX.le i hC _ a

open Scheme.IdealSheafData

section Factorial

variable [IsIntegral X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

private theorem classIntersectionNumber_mul_primeDivisorClass [IsLocallyNoetherian X]
    (hX : topologicalKrullDim X = 2) (p : CodimensionOnePoint X) (a b : LineBundleClass X) :
    classIntersectionNumber k X a (b * LineBundleClass.primeDivisorClass p) =
      classIntersectionNumber k X a b +
      LineBundleClass.intersectionNumber k
        (vanishingIdeal ⟨closure {(p : X)}, isClosed_closure⟩).subschemeι a := by
  rw [LineBundleClass.primeDivisorClass_def]
  exact classIntersectionNumber_mul_inv_mk_toInvertibleSheaf k hX.le
    (isEffectiveCartier_vanishingIdeal_closure_singleton p.property)
    (QPainleve.topologicalKrullDim_vanishingIdeal_subscheme k hX p) a b

/-- Intersecting with a prime divisor class gives the degree on its reduced closed curve. -/
public theorem classIntersectionNumber_primeDivisorClass_eq_intersectionNumber
    [IsLocallyNoetherian X] (hX : topologicalKrullDim X = 2) (p : CodimensionOnePoint X)
    (a : LineBundleClass X) :
    classIntersectionNumber k X a (LineBundleClass.primeDivisorClass p) =
      LineBundleClass.intersectionNumber k
        (vanishingIdeal ⟨closure {(p : X)}, isClosed_closure⟩).subschemeι a := by
  simpa only [one_mul, classIntersectionNumber_one_right, zero_add] using
    classIntersectionNumber_mul_primeDivisorClass k hX p a 1

/-- Intersection with the prime class of an integral closed curve computes the degree
on that curve with its given closed immersion. -/
public theorem classIntersectionNumber_primeDivisorClass_eq_intersectionNumber_of_isClosedImmersion
    [IsLocallyNoetherian X] (hX : topologicalKrullDim X = 2)
    {C : Scheme.{u}} [C.Over (Spec (.of k))] [IsIntegral C]
    (i : C ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (hC : topologicalKrullDim C = 1) (a : LineBundleClass X) :
    let p : CodimensionOnePoint X :=
      ⟨i (genericPoint C), i.coheight_apply_genericPoint_eq_one_of_dim_eq_two k hX hC⟩
    classIntersectionNumber k X a (LineBundleClass.primeDivisorClass p) =
      LineBundleClass.intersectionNumber k i a := by
  intro p
  have hp : (vanishingIdeal ⟨closure {(p : X)}, isClosed_closure⟩).IsEffectiveCartier :=
    isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  have he := i.ker_eq_vanishingIdeal_closure_genericPoint
  have hi : i.ker.IsEffectiveCartier := he ▸ hp
  rw [LineBundleClass.primeDivisorClass_def, ← LineBundleClass.mk_toInvertibleSheaf_congr hi hp he]
  exact classIntersectionNumber_eq_intersectionNumber_of_isEffectiveCartier_ker k hX.le i hC hi a

/-- Distinct prime divisors on an integral locally factorial projective surface intersect
nonnegatively in the surface pairing. -/
public theorem classIntersectionNumber_primeDivisorClass_nonneg_of_ne
    [IsLocallyNoetherian X] (hX : topologicalKrullDim X = 2)
    {p q : CodimensionOnePoint X} (hpq : p ≠ q) :
    0 ≤ classIntersectionNumber k X (LineBundleClass.primeDivisorClass p)
      (LineBundleClass.primeDivisorClass q) := by
  let I := vanishingIdeal (X := X) ⟨closure {(p : X)}, isClosed_closure⟩
  let J := vanishingIdeal (X := X) ⟨closure {(q : X)}, isClosed_closure⟩
  have hI : I.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  have hC := QPainleve.topologicalKrullDim_vanishingIdeal_subscheme k hX q
  have : J.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k J.subschemeι
  have : J.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr ⟨inferInstance, inferInstance, hC⟩
  have : RelativeDimensionLE 1 (J.subscheme ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr hC.le
  rw [classIntersectionNumber_primeDivisorClass_eq_intersectionNumber k hX,
    LineBundleClass.primeDivisorClass_def]
  exact LineBundleClass.intersectionNumber_inv_mk_toInvertibleSheaf_nonneg k J.subschemeι hI
    (hI.comap_subschemeι_vanishingIdeal_closure_singleton_of_ne hpq.symm)

/-- The surface intersection pairing on an integral locally factorial projective surface
is additive in the second class under tensor product. -/
public theorem classIntersectionNumber_mul_right (hX : topologicalKrullDim X = 2)
    (a b c : LineBundleClass X) :
    classIntersectionNumber k X a (b * c) =
      classIntersectionNumber k X a b + classIntersectionNumber k X a c := by
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  -- The classes that add a constant increment under tensor product form a subgroup.
  let S : Subgroup (LineBundleClass X) :=
    { carrier := {d | ∀ e, classIntersectionNumber k X a (e * d) =
        classIntersectionNumber k X a e + classIntersectionNumber k X a d}
      one_mem' := by
        intro e
        simp
      mul_mem' := fun {d f} hd hf e ↦ by
        rw [← mul_assoc, hf (e * d), hd e, hf d, add_assoc]
      inv_mem' := fun {d} hd e ↦ by
        have h := hd (e * d⁻¹)
        have hinv := hd d⁻¹
        rw [inv_mul_cancel_right] at h
        rw [inv_mul_cancel, classIntersectionNumber_one_right] at hinv
        omega }
  have hprime (p : CodimensionOnePoint X) : LineBundleClass.primeDivisorClass p ∈ S := by
    intro e
    rw [classIntersectionNumber_primeDivisorClass_eq_intersectionNumber k hX]
    exact classIntersectionNumber_mul_primeDivisorClass k hX p a e
  obtain ⟨D, hD⟩ := Scheme.CartierDivisor.weilToLineBundleClassHom_surjective (Additive.ofMul c)
  have hDc : (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul = c :=
    congrArg Additive.toMul hD
  have hc : c ∈ S := by
    rw [← hDc, LineBundleClass.toMul_weilToLineBundleClassHom, Finsupp.prod]
    exact S.prod_mem fun p _ ↦ S.zpow_mem (hprime p) _
  exact hc b

/-- The surface intersection pairing on an integral locally factorial projective surface
is additive in the first class under tensor product. -/
public theorem classIntersectionNumber_mul_left (hX : topologicalKrullDim X = 2)
    (a b c : LineBundleClass X) :
    classIntersectionNumber k X (a * b) c =
      classIntersectionNumber k X a c + classIntersectionNumber k X b c := by
  rw [classIntersectionNumber_comm (a * b), classIntersectionNumber_mul_right k hX,
    classIntersectionNumber_comm c a, classIntersectionNumber_comm c b]

/-- The surface intersection pairing as a bilinear form on the additive Picard group. -/
public noncomputable def classIntersectionBilinForm (hX : topologicalKrullDim X = 2) :
    LinearMap.BilinForm ℤ (Additive (LineBundleClass X)) :=
  let right (a : Additive (LineBundleClass X)) : Additive (LineBundleClass X) →+ ℤ :=
    { toFun := fun b ↦ classIntersectionNumber k X a.toMul b.toMul
      map_zero' := classIntersectionNumber_one_right _
      map_add' := fun b c ↦ classIntersectionNumber_mul_right k hX a.toMul b.toMul c.toMul }
  ({ toFun := fun a ↦ (right a).toIntLinearMap
     map_zero' := LinearMap.ext fun _ ↦ classIntersectionNumber_one_left _
     map_add' := fun a b ↦ LinearMap.ext fun c ↦
       classIntersectionNumber_mul_left k hX a.toMul b.toMul c.toMul } :
    Additive (LineBundleClass X) →+ (Additive (LineBundleClass X) →ₗ[ℤ] ℤ)).toIntLinearMap

/-- Evaluation of the bilinear form agrees with the Euler-characteristic pairing. -/
@[simp]
public theorem classIntersectionBilinForm_apply (hX : topologicalKrullDim X = 2)
    (a b : Additive (LineBundleClass X)) :
    classIntersectionBilinForm k hX a b = classIntersectionNumber k X a.toMul b.toMul :=
  (rfl)

/-- The bilinear form on the additive Picard group is symmetric. -/
public theorem classIntersectionBilinForm_isSymm (hX : topologicalKrullDim X = 2) :
    (classIntersectionBilinForm k hX).IsSymm := by
  constructor
  intro a b
  simpa only [classIntersectionBilinForm_apply] using classIntersectionNumber_comm a.toMul b.toMul

/-- Intersecting with the `n`th tensor power scales the intersection by `n`. -/
public theorem classIntersectionNumber_pow_right (hX : topologicalKrullDim X = 2)
    (a b : LineBundleClass X) (n : ℕ) :
    classIntersectionNumber k X a (b ^ n) = (n : ℤ) * classIntersectionNumber k X a b := by
  let l := classIntersectionBilinForm k hX (Additive.ofMul a)
  simpa only [l, classIntersectionBilinForm_apply, toMul_zsmul, toMul_ofMul,
    Int.zsmul_eq_mul, zpow_natCast] using l.map_smul (n : ℤ) (Additive.ofMul b)

/-- The intersection of an `n`th tensor power with another class scales by `n`. -/
public theorem classIntersectionNumber_pow_left (hX : topologicalKrullDim X = 2)
    (a b : LineBundleClass X) (n : ℕ) :
    classIntersectionNumber k X (a ^ n) b = (n : ℤ) * classIntersectionNumber k X a b := by
  rw [classIntersectionNumber_comm (a ^ n) b, classIntersectionNumber_pow_right k hX,
    classIntersectionNumber_comm b a]

/-- Intersection with the class of a Weil divisor is the sum of the intersections with
its prime divisors weighted by their multiplicities. -/
public theorem classIntersectionNumber_weilToLineBundleClassHom
    [IsNoetherian X] (hX : topologicalKrullDim X = 2) (a : LineBundleClass X)
    (D : SchemeWeilDivisor X) :
    classIntersectionNumber k X a (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul =
      D.sum (fun p n ↦
        n * classIntersectionNumber k X a (LineBundleClass.primeDivisorClass p)) := by
  let f := classIntersectionBilinForm k hX (Additive.ofMul a)
  calc
    _ = f (Scheme.CartierDivisor.weilToLineBundleClassHom X D) :=
      (classIntersectionBilinForm_apply k hX _ _).symm
    _ = f (Scheme.CartierDivisor.weilToLineBundleClassHom X (D.sum Finsupp.single)) := by
      rw [Finsupp.sum_single]
    _ = _ := by
      rw [map_finsuppSum, map_finsuppSum]
      simp only [Scheme.CartierDivisor.weilToLineBundleClassHom_single, map_zsmul, f,
        classIntersectionBilinForm_apply, LineBundleClass.primeDivisorClass_def, toMul_ofMul,
        Int.zsmul_eq_mul]

/-- An effective Weil divisor meets a prime outside its support nonnegatively. -/
public theorem classIntersectionNumber_primeDivisorClass_nonneg_of_notMem_support
    [IsNoetherian X] (hX : topologicalKrullDim X = 2) {D : SchemeWeilDivisor X} (hD : 0 ≤ D)
    {p : CodimensionOnePoint X} (hp : p ∉ D.support) :
    0 ≤ classIntersectionNumber k X (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul
      (LineBundleClass.primeDivisorClass p) := by
  rw [classIntersectionNumber_comm, classIntersectionNumber_weilToLineBundleClassHom k hX]
  refine Finsupp.sum_nonneg fun q hq ↦ mul_nonneg (hD q) ?_
  exact classIntersectionNumber_primeDivisorClass_nonneg_of_ne k hX
    (fun he ↦ hp (he.symm ▸ hq))

end Factorial

end

section SmoothSurface

variable (k : Type u) [Field k] [Infinite k] (X : Scheme.{u})
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

/-- The integral Picard intersection form of a smooth integral projective surface. -/
public noncomputable def intersectionBilinForm :
    LinearMap.BilinForm ℤ (Additive (LineBundleClass X)) :=
  let f := (X ↘ Spec (CommRingCat.of k))
  letI : IsNoetherian X := isNoetherian_of_finiteType f
  letI := (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  classIntersectionBilinForm k (topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2))

@[simp]
public theorem intersectionBilinForm_apply (x y : Additive (LineBundleClass X)) :
    intersectionBilinForm k X x y = classIntersectionNumber k X x.toMul y.toMul := by
  simp only [intersectionBilinForm, classIntersectionBilinForm_apply]

end SmoothSurface

end TauCeti.AlgebraicGeometry.Chow

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} [IsIntegral X]

/-- The Picard sublattice orthogonal to the prime curves in the support of a boundary
ideal on a smooth integral projective surface. -/
public noncomputable def boundaryOrthogonal
    (D : X.IdealSheafData) (k : Type u) [Field k] [Infinite k]
    [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] :
    Submodule ℤ (Additive (LineBundleClass X)) :=
  letI := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  letI := (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  (Chow.intersectionBilinForm k X).orthogonal
    (Scheme.Opens.primeDivisorSpanCompl D.support.compl)

/-- The boundary orthogonal is computed using the intersection form and the span of the
prime divisors in the complement of the boundary open. -/
public theorem boundaryOrthogonal_def
    (D : X.IdealSheafData) (k : Type u) [Field k] [Infinite k]
    [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] :
    letI := isNoetherian_of_finiteType (X ↘ Spec (.of k))
    letI := (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    D.boundaryOrthogonal k = (Chow.intersectionBilinForm k X).orthogonal
      (Scheme.Opens.primeDivisorSpanCompl D.support.compl) :=
  (rfl)

end AlgebraicGeometry.Scheme.IdealSheafData
