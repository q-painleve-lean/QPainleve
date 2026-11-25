/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.ExceptionalRay
public import QPainleve.AlgebraicGeometry.Chow.Nef.Cone

import QPainleve.AlgebraicGeometry.Chow.ProperIntersection
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.ExceptionalPrime
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Numerical
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension

/-!
# Transport of exceptional configurations

An integral Picard isometry preserving the canonical class and the real nef cones
transports a pairwise disjoint configuration of exceptional curves of the first kind.
The transported classes determine negative extremal rays. Their integral canonical
degrees and arithmetic adjunction identify the prime curves on those rays.

This is the transport of exceptional curves in [Gross, Hacking and Keel,
*Moduli of surfaces with an anti-canonical cycle*, proof of Theorem 1.8](
https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve
open TopologicalSpace (Closeds)
open AlgebraicGeometry.Scheme.IdealSheafData TauCeti.AlgebraicGeometry.LineBundleClass
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry.Chow

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [X.IsProjectiveOver k] [Y.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]

local notation "Pic(" S ")" => Additive (LineBundleClass S)
local notation "V(" S ")" => (ℝ ⊗[ℤ] Pic(S))
local notation "K(" S ")" => mk (canonicalBundle k S 2)
local notation "B(" S ")" => classIntersectionNumber k S
local notation "P" => primeDivisorClass
local notation "curveIdeal" p:arg =>
  vanishingIdeal (Closeds.mk (closure {(p : X)}) isClosed_closure)

variable [hRatX : Scheme.IsRationalOver (X ↘ Spec (.of k))]
  [hRatY : Scheme.IsRationalOver (Y ↘ Spec (.of k))]
  [TopologicalSpace V(X)] [IsTopologicalAddGroup V(X)] [ContinuousSMul ℝ V(X)] [T2Space V(X)]
  [TopologicalSpace V(Y)] [IsTopologicalAddGroup V(Y)] [ContinuousSMul ℝ V(Y)] [T2Space V(Y)]

include hRatX hRatY in
private theorem exists_transport_exceptional_primes [IsIntegral X] [IsIntegral Y]
    [FiniteDimensional ℝ V(X)] [FiniteDimensional ℝ V(Y)] [IsLocallyNoetherian X]
    [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)] {ι : Type*}
    (e : (intersectionBilinForm k X).IsometryEquiv (intersectionBilinForm k Y))
    (hK : e (Additive.ofMul K(X)) = Additive.ofMul K(Y))
    (hnef : (e.baseChange ℝ) '' (nefCone k (X := X) : Set V(X)) = nefCone k (X := Y))
    (p : ι → CodimensionOnePoint X)
    (hsq : ∀ j, B(X) (P (p j)) (P (p j)) = -1)
    (hcan : ∀ j, B(X) (P (p j)) K(X) = -1)
    (horth : Pairwise (fun i j ↦ B(X) (P (p i)) (P (p j)) = 0)) :
    let : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ Spec (.of k))
    let : ∀ x : Y, UniqueFactorizationMonoid (Y.presheaf.stalk x) :=
      (Y ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    ∃ q : ι → CodimensionOnePoint Y,
      (∀ j, P (q j) = (e (Additive.ofMul (P (p j)))).toMul ∧
        (vanishingIdeal ⟨closure {(q j : Y)}, isClosed_closure⟩).IsExceptionalCurveOfFirstKind) ∧
      Pairwise (fun i j ↦ Disjoint
        ((vanishingIdeal ⟨closure {(q i : Y)}, isClosed_closure⟩).support : Set Y)
        (vanishingIdeal ⟨closure {(q j : Y)}, isClosed_closure⟩).support) := by
  intro _ _
  let a (j : ι) := (e (Additive.ofMul (P (p j)))).toMul
  have hmap (L M : LineBundleClass X) :
      B(Y) (e (Additive.ofMul L)).toMul (e (Additive.ofMul M)).toMul = B(X) L M := by
    simpa only [intersectionBilinForm_apply, toMul_ofMul] using
      e.map_app (Additive.ofMul M) (Additive.ofMul L)
  have hs (j : ι) : B(Y) (a j) (a j) = -1 := (hmap _ _).trans (hsq j)
  have hc (j : ι) : B(Y) (a j) K(Y) = -1 := by
    simpa only [a, hK, toMul_ofMul, hcan] using hmap (P (p j)) K(X)
  have : (realIntersectionBilinForm k X).IsContPerfPair :=
    isContPerfPair_realIntersectionBilinForm_of_isRationalOver k
  have : (realIntersectionBilinForm k Y).IsContPerfPair :=
    isContPerfPair_realIntersectionBilinForm_of_isRationalOver k
  let eℝ : (realIntersectionBilinForm k X).IsometryEquiv (realIntersectionBilinForm k Y) :=
    { toLinearEquiv := (e.baseChange ℝ).toLinearEquiv
      map_app' := fun x y ↦ by
        simpa only [realIntersectionBilinForm_def, LinearMap.toFun_eq_coe, LinearEquiv.coe_coe,
          LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv] using (e.baseChange ℝ).map_app y x }
  have hnef' : eℝ '' (nefCone k (X := X) : Set V(X)) = nefCone k (X := Y) := hnef
  have hf (j : ι) : (PointedCone.hull ℝ {(1 : ℝ) ⊗ₜ[ℤ] Additive.ofMul (a j)}).IsFaceOf
      (closedCurveCone k (X := Y)).toPointedCone := by
    have hneg : realIntersectionBilinForm k X (realPrimeDivisorClass k (p j))
        (realPrimeDivisorClass k (p j)) < 0 := by
      simp [realPrimeDivisorClass_def, hsq j]
    have he (v : V(X)) : eℝ v = e.baseChange ℝ v := rfl
    simpa only [he, realPrimeDivisorClass_def, LinearMap.BilinForm.IsometryEquiv.baseChange_tmul,
      a, ofMul_toMul] using
      isFaceOf_hull_singleton_image_realPrimeDivisorClass k eℝ hnef' (p j) hneg
  exact exists_pairwise_disjoint_exceptionalCurves_of_extremal_rays k a hs hc
    (fun i j hij ↦ (hmap _ _).trans (horth hij)) hf
    (fun j ↦ exists_effectiveWeilDivisor_of_exceptional_extremalRay k (hf j) (hs j) (hc j))

/-- A canonical-class-preserving Picard isometry identifying the real nef cones transports
pairwise disjoint exceptional curves to pairwise disjoint exceptional curves. The positive
divisor class of each target curve is the image of the corresponding source class. -/
theorem exists_pairwise_disjoint_exceptionalCurves_of_nefCone_isometry {ι : Type*}
    (E : ι → X.IdealSheafData) (hE : ∀ j, (E j).IsExceptionalCurveOfFirstKind)
    (hdis : Pairwise fun i j ↦ Disjoint ((E i).support : Set X) (E j).support) :
    let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
    let : Smooth (Y ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
    let : IsIntegral X := hRatX.isIntegral_of_smooth
    let : IsIntegral Y := hRatY.isIntegral_of_smooth
    let : Module.Finite ℤ Pic(X) := X.finite_picard_of_isRationalOver k (rational := hRatX)
    let : Module.Finite ℤ Pic(Y) := Y.finite_picard_of_isRationalOver k (rational := hRatY)
    ∀ (e : (intersectionBilinForm k X).IsometryEquiv (intersectionBilinForm k Y)),
      e (Additive.ofMul K(X)) = Additive.ofMul K(Y) →
      (e.baseChange ℝ) '' (nefCone k (X := X) : Set V(X)) = nefCone k (X := Y) →
      ∃ (F : ι → Y.IdealSheafData) (hF : ∀ j, (F j).IsExceptionalCurveOfFirstKind),
        (∀ j, e (Additive.ofMul (mk (hE j).isEffectiveCartier.toInvertibleSheaf)⁻¹) =
          Additive.ofMul (mk (hF j).isEffectiveCartier.toInvertibleSheaf)⁻¹) ∧
        Pairwise fun i j ↦ Disjoint ((F i).support : Set Y) (F j).support := by
  intro _ _ _ _ _ _ e hK hnef
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  have := (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let p (j : ι) : CodimensionOnePoint X :=
    letI : IsIntegral (E j).subscheme := (hE j).isIntegral_subscheme
    ⟨(E j).subschemeι (genericPoint (E j).subscheme),
      (hE j).isEffectiveCartier.coheight_subschemeι_genericPoint⟩
  have hp (j : ι) : curveIdeal (p j) = E j := by
    have : IsIntegral (E j).subscheme := (hE j).isIntegral_subscheme
    exact (E j).vanishingIdeal_closure_subschemeι_genericPoint
  have hP (j : ι) : P (p j) = (mk (hE j).isEffectiveCartier.toInvertibleSheaf)⁻¹ := by
    rw [primeDivisorClass_def, mk_toInvertibleSheaf_congr _ _ (hp j)]
  have hnum (j : ι) := (isExceptionalCurveOfFirstKind_vanishingIdeal_iff k (p j)).mp
    (by rw [hp]; exact hE j)
  have horth : Pairwise (fun i j ↦ B(X) (P (p i)) (P (p j)) = 0) := by
    intro i j hij
    have hd : Disjoint ((E i).support : Set X) (E j).support := hdis hij
    rw [← hp i, ← hp j] at hd
    simp only [coe_support_vanishingIdeal, Closeds.coe_mk] at hd
    have hne : p i ≠ p j := by
      intro he
      exact Set.disjoint_left.mp hd (subset_closure (Set.mem_singleton _))
        (he ▸ subset_closure (Set.mem_singleton _))
    have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)
    apply le_antisymm ?_ (classIntersectionNumber_primeDivisorClass_nonneg_of_ne k hX hne)
    have hpos := classIntersectionNumber_primeDivisorClass_pos_iff k hX.le hne
    exact not_lt.mp fun h ↦ (hpos.mp h).ne_empty (Set.disjoint_iff_inter_eq_empty.mp hd)
  obtain ⟨q, hq, hdisq⟩ := exists_transport_exceptional_primes k e hK hnef p
    (fun j ↦ (hnum j).1) (fun j ↦ (hnum j).2) horth
  let F (j : ι) : Y.IdealSheafData := vanishingIdeal ⟨closure {(q j : Y)}, isClosed_closure⟩
  refine ⟨F, fun j ↦ (hq j).2, fun j ↦ ?_, hdisq⟩
  have : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ Spec (.of k))
  have := (Y ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  rw [← hP]
  have heq := (hq j).1.symm.trans (primeDivisorClass_def (q j))
  simpa only [ofMul_toMul] using congrArg Additive.ofMul heq

end TauCeti.AlgebraicGeometry.Chow
