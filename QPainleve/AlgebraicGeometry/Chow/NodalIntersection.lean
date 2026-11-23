/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.ProperIntersection
public import QPainleve.AlgebraicGeometry.Curves.Node.Intersection

/-!
# Intersection numbers of nodal divisor components

Two distinct prime components of a nodal Cartier divisor on a smooth projective
surface over an algebraically closed field intersect with multiplicity one at
each common point. Their intersection number therefore counts the common points.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry.Chow

/-- The intersection number of distinct components of a nodal Cartier divisor on
a smooth projective surface over an algebraically closed field counts their common points. -/
theorem classIntersectionNumber_eq_ncard_of_nodal
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subscheme ↘ Spec (.of k)))
    {p q : CodimensionOnePoint X} (hpq : p ≠ q)
    (hp : (p : X) ∈ D.support) (hq : (q : X) ∈ D.support) :
    let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    let : ∀ x : X, IsDomain (X.presheaf.stalk x) := fun x ↦
      letI := isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k)) x
      inferInstance
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    classIntersectionNumber k X (LineBundleClass.primeDivisorClass p)
      (LineBundleClass.primeDivisorClass q) = (closure {(p : X)} ∩ closure {(q : X)}).ncard := by
  intro _ _ _ _
  have : Nonempty X := ⟨p⟩
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)
  let P := vanishingIdeal ⟨closure {(p : X)}, isClosed_closure⟩
  let Q := vanishingIdeal ⟨closure {(q : X)}, isClosed_closure⟩
  have hP : P.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  have hQ : Q.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton q.property
  have hPQ := hP.comap_subschemeι_vanishingIdeal_closure_singleton_of_ne hpq.symm
  have hsupport : ((P ⊔ Q).support : Set X) = closure {(p : X)} ∩ closure {(q : X)} := by
    simp only [P, Q, support_sup, Closeds.coe_inf, coe_support_vanishingIdeal, Closeds.coe_mk]
  rw [LineBundleClass.primeDivisorClass_def, LineBundleClass.primeDivisorClass_def, ← hsupport]
  apply classIntersectionNumber_eq_ncard_of_stalkIdeal_sup_eq_maximalIdeal k hdim.le hP hQ hPQ
  intro x hx
  have hx' : x ∈ closure {(p : X)} ∩ closure {(q : X)} :=
    hsupport ▸ (SetLike.mem_coe.mpr hx)
  exact hD.stalkIdeal_sup_eq_maximalIdeal_of_nodal hnodal hpq hp hq
    (specializes_iff_mem_closure.mpr hx'.1) (specializes_iff_mem_closure.mpr hx'.2)

end TauCeti.AlgebraicGeometry.Chow
