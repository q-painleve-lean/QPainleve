/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.SurfaceIntersection
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.ClosedImmersion
import TauCeti.AlgebraicGeometry.CartierDivisor.Excision
import TauCeti.AlgebraicGeometry.LineBundle.BaseChange
import TauCeti.AlgebraicGeometry.Chow.DivisorClass
import QPainleve.AlgebraicGeometry.Cohomology.Support
import QPainleve.AlgebraicGeometry.IdealSheaf.EulerCharacteristic

/-!
# Surface intersection and restriction to a curve

The surface intersection pairing with the class of a Cartier curve is the degree
of the restricted line bundle. Twisting by the curve changes the pairing by that
same degree, independently of the starting twist.

## References

* O. Debarre, *Introduction to Mori Theory*, §3.2, Theorem 3.6 and formula (3.3).
* The Stacks Project, Definition 33.45.3 (tag 0BEP).
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open TauCeti
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry.Chow

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
  have he : i.toImage ≫ (i.ker.subscheme ↘ Spec (.of k)) = C ↘ Spec (.of k) := by
    rw [Scheme.IdealSheafData.over_eq_subschemeι_comp, ← Category.assoc]
    exact (congrArg (· ≫ X ↘ Spec (.of k)) i.toImage_imageι).trans (comp_over i _)
  calc
    _ = LineBundleClass.intersectionNumber k (i.toImage ≫ i.imageι) a := by
      rw [← LineBundleClass.intersectionNumber_pullback]
      simp only [LineBundleClass.intersectionNumber_def]
      exact (LineBundleClass.eulerDegree_pullback_of_isIso (k := k) i.toImage he _).symm
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

section Factorial

open Scheme.IdealSheafData

variable [IsIntegral X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

private theorem classIntersectionNumber_mul_primeDivisorClass [IsLocallyNoetherian X]
    (hX : topologicalKrullDim X = 2) (p : CodimensionOnePoint X) (a b : LineBundleClass X) :
    classIntersectionNumber k X a (b * LineBundleClass.primeDivisorClass p) =
      classIntersectionNumber k X a b +
      LineBundleClass.intersectionNumber k
        (vanishingIdeal ⟨closure {(p : X)}, isClosed_closure⟩).subschemeι a := by
  let I := vanishingIdeal (X := X) ⟨closure {(p : X)}, isClosed_closure⟩
  have hrange : Set.range I.subschemeι = closure {(p : X)} := by
    rw [I.range_subschemeι, coe_support_vanishingIdeal, Closeds.coe_mk]
  obtain ⟨d, hheight, hd⟩ := mem_pointsOfDimension.mp
    ((coheight_eq_one_iff_mem_pointsOfDimension k (n := 2) hX).mp p.property)
  have hd₁ : d = 1 := by omega
  have hC : topologicalKrullDim I.subscheme = 1 := by
    rw [← topologicalKrullDim_range_of_isPreimmersion I.subschemeι, hrange,
      ← height_eq_topologicalKrullDim_closure_singleton, hheight, hd₁]
    rfl
  rw [LineBundleClass.primeDivisorClass_def]
  exact classIntersectionNumber_mul_inv_mk_toInvertibleSheaf k hX.le
    (isEffectiveCartier_vanishingIdeal_closure_singleton p.property) hC a b

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
    have h := classIntersectionNumber_mul_primeDivisorClass k hX p a 1
    rw [one_mul, classIntersectionNumber_one_right, zero_add] at h
    rw [h]
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

end Factorial

end TauCeti.AlgebraicGeometry.Chow
