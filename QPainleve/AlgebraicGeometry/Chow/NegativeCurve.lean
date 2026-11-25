/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.CurveCone
public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic

import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.AlgebraicGeometry.IdealSheaf.ClosedImmersion
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Numerical
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension

/-!
# Negative curves off an anticanonical divisor

On a smooth projective rational surface, an integral curve whose generic point lies off
an effective anticanonical divisor has negative self-intersection exactly when it is
exceptional of the first kind and meets the divisor with intersection number one,
or has arithmetic genus zero, self-intersection `-2`, and is disjoint from the divisor.
This is the negative-curve calculation used by Gross, Hacking and Keel in
[*Moduli of surfaces with an anti-canonical cycle*, Lemma 2.14][GHK].

[GHK]: https://paulhacking.github.io/mlp.pdf
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve
open TauCeti.AlgebraicGeometry LineBundleClass

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [Scheme.IsRationalOver (X ↘ Spec (.of k))]
  {I D : X.IdealSheafData} [I.subscheme.IsCurveOver k]

local notation "B" => Chow.classIntersectionNumber k X
local notation "K" => LineBundleClass.mk (canonicalBundle k X 2)

/-- A negative integral curve outside the components of an effective anticanonical
divisor is either an exceptional curve of the first kind of boundary degree one, or a
genus-zero curve of square `-2` disjoint from the boundary. Conversely, both types
have negative square. The anticanonical condition says that the ideal of the boundary
has the class of the canonical line bundle. -/
theorem classIntersectionNumber_self_neg_iff_of_anticanonical
    (hI : I.IsEffectiveCartier) (hD : D.IsEffectiveCartier)
    (hcan : LineBundleClass.mk hD.toInvertibleSheaf = K)
    (hproper : I.subschemeι (genericPoint I.subscheme) ∉ D.support) :
    let a := (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
    let d := (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹
    B a a < 0 ↔ (I.IsExceptionalCurveOfFirstKind ∧ B d a = 1) ∨
      (I.subscheme.genus k = 0 ∧ B a a = -2 ∧ Disjoint (I.support : Set X) D.support) := by
  intro a d
  let i := I.subschemeι
  have hdim : topologicalKrullDim I.subscheme = 1 := IsCurveOver.topologicalKrullDim_eq_one k
  have : Nonempty X := Nonempty.map i inferInstance
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)
  have hdegree (b : LineBundleClass X) : B b a = intersectionNumber k i b :=
    Chow.classIntersectionNumber_eq_intersectionNumber_subschemeι k hX.le hI hdim b
  have : I.subscheme.IsProjectiveOver k := Scheme.IsProjectiveOver.of_isClosedImmersion k i
  have : RelativeDimensionLE 1 (I.subscheme ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr hdim.le
  have hfinite (q : ℕ) :
      FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial I.subscheme).obj q) :=
    Scheme.Modules.moduleFinite_cohomology_of_isProjectiveOver k _ q
  have := hfinite 0
  have := hfinite 1
  have hD' := hD.comap_of_isIntegral i hproper
  have hd : 0 ≤ B d a := by
    rw [hdegree]
    exact intersectionNumber_inv_mk_toInvertibleSheaf_nonneg k i hD hD'
  have hdisjoint (hz : B d a = 0) : Disjoint (I.support : Set X) D.support := by
    refine Set.disjoint_left.mpr fun x hx hxD ↦ ?_
    rw [← Scheme.IdealSheafData.range_subschemeι] at hx
    obtain ⟨y, rfl⟩ := hx
    have hpos : 0 < B d a := by
      rw [hdegree]
      exact (intersectionNumber_inv_mk_toInvertibleSheaf_pos_iff k i hD hD').mpr ⟨y, hxD⟩
    omega
  have hadj := I.subschemeι.two_mul_genus_sub_two_eq_intersection_of_isRationalOver k
  dsimp only at hadj
  rw [mk_toInvertibleSheaf_congr _ hI (ker_subschemeι I)] at hadj
  have hanti : B a K = - B d a := by
    rw [Chow.classIntersectionNumber_comm a K, hdegree, hdegree, ← hcan]
    simp only [d, intersectionNumber_inv_of_isIntegral, neg_neg]
  have hadj' : 2 * (I.subscheme.genus k : ℤ) - 2 = B a a + B a K := hadj
  rw [hanti, ← sub_eq_add_neg] at hadj'
  have hexc : I.IsExceptionalCurveOfFirstKind ↔ I.subscheme.genus k = 0 ∧ B a a = -1 :=
    hI.isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_classIntersectionNumber (k := k) hX.le
  constructor
  · intro hneg
    have hg : I.subscheme.genus k = 0 := by omega
    by_cases h₁ : B a a = -1
    · exact Or.inl ⟨hexc.mpr ⟨hg, h₁⟩, by omega⟩
    · exact Or.inr ⟨hg, by omega, hdisjoint (by omega)⟩
  · rintro (⟨hE, _⟩ | ⟨_, h₂, _⟩)
    · have h₁ := (hexc.mp hE).2
      omega
    · omega

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

namespace TauCeti.AlgebraicGeometry.Chow

open TopologicalSpace Scheme.IdealSheafData
open scoped TensorProduct

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "B(" S ")" => realIntersectionBilinForm k S
local notation "b(" S ")" => classIntersectionNumber k S
local notation "K(" S ")" => LineBundleClass.mk (QPainleve.canonicalBundle k S 2)
local notation "ι" => (fun a : LineBundleClass _ ↦ (1 : ℝ) ⊗ₜ[ℤ] Additive.ofMul a)
local notation "c" => realPrimeDivisorClass k

variable [rational : Scheme.IsRationalOver (X ↘ Spec (.of k))] {D : X.IdealSheafData}
  (hD : D.IsEffectiveCartier)
  (hcan : LineBundleClass.mk hD.toInvertibleSheaf =
    LineBundleClass.mk (QPainleve.canonicalBundle k X 2))

include rational hD hcan in
/-- A negative prime class off an anticanonical boundary either has square and
canonical degree `-1`, or has square `-2` and closure disjoint from the boundary. -/
theorem negativePrimeDivisorClass_cases [IsIntegral X] (p : CodimensionOnePoint X)
    (hp : B(X) (c p) (c p) < 0) (hdis : (p : X) ∉ D.support) :
    (B(X) (c p) (c p) = -1 ∧ B(X) (c p) (ι K(X)) = -1) ∨
      (B(X) (c p) (c p) = -2 ∧ Disjoint
        ((vanishingIdeal ⟨closure {(p : X)}, isClosed_closure⟩).support : Set X) D.support) := by
  let I := vanishingIdeal (Closeds.mk (closure {(p : X)}) isClosed_closure)
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)
  have : IsProper (I.subscheme ↘ Spec (.of k)) := by
    rw [← comp_over I.subschemeι]
    infer_instance
  have : I.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, QPainleve.topologicalKrullDim_vanishingIdeal_subscheme k hX p⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hI : I.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  let a := (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
  have hp' : c p = ι a := by
    rw [realPrimeDivisorClass_def, primeDivisorClass_def]
  have hneg : b(X) a a < 0 := by
    rw [hp', realIntersectionBilinForm_tmul, one_mul, one_mul, toMul_ofMul, Int.cast_lt_zero] at hp
    exact hp
  have hoff : I.subschemeι (genericPoint I.subscheme) ∉ D.support := by
    simpa only [I, subschemeι_genericPoint_vanishingIdeal_closure_singleton] using hdis
  rcases (hI.classIntersectionNumber_self_neg_iff_of_anticanonical hD hcan hoff).mp hneg with
    ⟨he, hd⟩ | ⟨_, hsq, hdisjoint⟩
  · have hsq := ((hI.isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_classIntersectionNumber
      (k := k) hX.le).mp he).2
    have hc := (intersectionBilinForm k X (Additive.ofMul a)).map_neg (Additive.ofMul K(X))
    have hd' : b(X) a K(X) = -1 := by
      simp only [intersectionBilinForm_apply, toMul_neg, toMul_ofMul] at hc
      rw [hcan, classIntersectionNumber_comm] at hd
      have hdeg : b(X) a K(X)⁻¹ = 1 := hd
      exact neg_eq_iff_eq_neg.mp (hdeg.symm.trans hc).symm
    have hsq' : b(X) a a = -1 := hsq
    left
    simp [hp', hsq', hd']
  · have hsq' : b(X) a a = -2 := hsq
    exact Or.inr ⟨by simp [hp', hsq'], hdisjoint⟩

include rational hD hcan in
/-- On an anticanonical pair without internal `(-2)` curves, every prime
divisor of self-intersection `-2` is a boundary component. -/
theorem mem_boundary_of_primeDivisorClass_self_eq_neg_two [IsIntegral X]
    [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    (hroot : ∀ r : CodimensionOnePoint X, Disjoint (closure {(r : X)}) D.support →
      b(X) (primeDivisorClass r) (primeDivisorClass r) ≠ -2)
    (r : CodimensionOnePoint X)
    (hr : b(X) (primeDivisorClass r) (primeDivisorClass r) = -2) : (r : X) ∈ D.support := by
  by_contra hoff
  have hreal : B(X) (c r) (c r) = -2 := by
    simp [realPrimeDivisorClass_def, realIntersectionBilinForm_tmul, hr]
  rcases negativePrimeDivisorClass_cases k hD hcan r (by rw [hreal]; norm_num) hoff with
    ⟨hsq, _⟩ | ⟨_, hdis⟩
  · have : (-2 : ℝ) = -1 := hreal.symm.trans hsq
    norm_num at this
  · rw [coe_support_vanishingIdeal] at hdis
    exact hroot r hdis hr

include rational hD hcan in
/-- On an anticanonical pair without internal `(-2)` curves, a prime divisor whose
generic point lies off the boundary has real self-intersection different from `-2`. -/
theorem prime_self_intersection_ne_neg_two_off_boundary [IsIntegral X]
    [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    (hroot : ∀ r : CodimensionOnePoint X, Disjoint (closure {(r : X)}) D.support →
      b(X) (primeDivisorClass r) (primeDivisorClass r) ≠ -2)
    (r : CodimensionOnePoint X) (hr : (r : X) ∉ D.support) : B(X) (c r) (c r) ≠ -2 := by
  intro hsq
  apply hr (mem_boundary_of_primeDivisorClass_self_eq_neg_two k hD hcan hroot r ?_)
  simp only [realPrimeDivisorClass_def, realIntersectionBilinForm_tmul,
    one_mul, toMul_ofMul] at hsq
  exact_mod_cast hsq

include rational hD hcan in
/-- An anticanonical pair has a prime class of square `-2` off the boundary precisely
when it has an integral closed curve of square `-2` disjoint from the boundary. -/
theorem exists_realPrimeDivisorClass_self_eq_neg_two_iff [IsIntegral X] :
    (∃ p : CodimensionOnePoint X, (p : X) ∉ D.support ∧ B(X) (c p) (c p) = -2) ↔
      ∃ (C : Scheme.{u}) (i : C ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral C)
        (hi : i.ker.IsEffectiveCartier),
        topologicalKrullDim C = 1 ∧ Disjoint (Set.range i) D.support ∧
          b(X) (mk hi.toInvertibleSheaf)⁻¹ (mk hi.toInvertibleSheaf)⁻¹ = -2 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have := (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)
  have hreal (p : CodimensionOnePoint X) :
      B(X) (c p) (c p) = (b(X) (primeDivisorClass p) (primeDivisorClass p) : ℝ) := by
    rw [realPrimeDivisorClass_def k p, realIntersectionBilinForm_tmul, one_mul, one_mul,
      toMul_ofMul]
  constructor
  · rintro ⟨p, hp, hsq⟩
    let I := vanishingIdeal (Closeds.mk (closure {(p : X)}) isClosed_closure)
    have hI : I.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
    have hneg : B(X) (c p) (c p) < 0 := by rw [hsq]; norm_num
    obtain hE | ⟨_, hdis⟩ := negativePrimeDivisorClass_cases k hD hcan p hneg hp
    · linarith [hE.1]
    · have hi : I.subschemeι.ker.IsEffectiveCartier := (ker_subschemeι I).symm ▸ hI
      refine ⟨I.subscheme, I.subschemeι, inferInstance, inferInstance, hi,
        QPainleve.topologicalKrullDim_vanishingIdeal_subscheme k hX p,
        I.range_subschemeι.symm ▸ hdis, ?_⟩
      rw [mk_toInvertibleSheaf_congr hi hI (ker_subschemeι I)]
      rw [hreal, primeDivisorClass_def] at hsq
      exact_mod_cast hsq
  · rintro ⟨C, i, hi, _, hI, hdim, hdis, hsq⟩
    let : C.Over (Spec (.of k)) := ⟨i ≫ X ↘ Spec (.of k)⟩
    let : i.IsOver (Spec (.of k)) := ⟨rfl⟩
    let p : CodimensionOnePoint X :=
      ⟨i (genericPoint C), i.coheight_apply_genericPoint_eq_one_of_dim_eq_two k hX hdim⟩
    have hp : (p : X) ∉ D.support :=
      fun hp ↦ Set.disjoint_left.mp hdis (Set.mem_range_self (genericPoint C)) hp
    refine ⟨p, hp, ?_⟩
    rw [hreal, primeDivisorClass_def,
      ← mk_toInvertibleSheaf_congr hI _ i.ker_eq_vanishingIdeal_closure_genericPoint, hsq]
    norm_num

end TauCeti.AlgebraicGeometry.Chow
