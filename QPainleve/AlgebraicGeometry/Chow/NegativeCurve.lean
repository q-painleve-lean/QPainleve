/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic

import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Numerical

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
