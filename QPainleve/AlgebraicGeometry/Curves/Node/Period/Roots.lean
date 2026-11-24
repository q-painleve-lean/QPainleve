/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Period.Restriction

import QPainleve.AlgebraicGeometry.Chow.Ample
import QPainleve.AlgebraicGeometry.LineBundle.Ample

/-!
# Boundary periods and internal curves

An internal curve has trivial restriction to the boundary. In particular, a period
that avoids one on classes of square `-2` excludes internal curves of square `-2`,
as used in the period arguments of [Gross, Hacking and Keel, §2][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public section

open AlgebraicGeometry TopologicalSpace TauCeti TauCeti.AlgebraicGeometry LineBundleClass

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

section Period

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [IsIntegral X] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  (hD : D.IsEffectiveCartier)
  (hgenus : ∀ v : irreducibleComponents (D.subscheme.singularLocus k).blowup,
    (D.subscheme.blowupComponent (K := k) v).toScheme.genus k = 0)
  {ι : Type v} {p : ι → (D.subscheme ↘ Spec (.of k)).smoothLocus} {n : ℕ} [NeZero n]
  {e : ZMod n ≃ (D.subscheme.dualGraph p).Edge}
  {o : (D.subscheme.dualGraph p).Edge → Equiv.Perm (Fin 2)}
  {w : ZMod n ≃ (D.subscheme.dualGraph p).Vertex}
  (hw : ∀ i b, (D.subscheme.dualGraph p).endpoint (e i) (o (e i) b) =
    w ((DualGraph.cycle n).endpoint i b))

local notation "s" => (X ↘ Spec (CommRingCat.of k))

/-- The class of a prime curve disjoint from the boundary belongs to the boundary
orthogonal lattice and has period one. -/
theorem boundaryPeriod_eq_one_of_disjoint_primeDivisor (q : CodimensionOnePoint X)
    (hq : Disjoint (closure {(q : X)}) (D.support : Set X)) :
    let : IsNoetherian X := isNoetherian_of_finiteType s
    let := (s).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    ∃ hqK : Additive.ofMul (primeDivisorClass q) ∈ D.boundaryOrthogonal k,
      hD.boundaryPeriod hgenus hw (Multiplicative.ofAdd ⟨_, hqK⟩) = 1 := by
  intro _ _
  rw [primeDivisorClass_def]
  exact hD.boundaryPeriod_eq_one_of_disjoint hgenus hw
    (isEffectiveCartier_vanishingIdeal_closure_singleton q.property)
    (by simpa only [coe_support_vanishingIdeal, Closeds.coe_mk] using hq.symm)

/-- A boundary period avoiding one on all classes of square `-2` excludes internal
prime curves of square `-2`. -/
theorem primeDivisorClass_self_ne_neg_two_of_boundaryPeriod_ne_one
    (hroot : ∀ x : D.boundaryOrthogonal k,
      Chow.intersectionBilinForm k X x.val x.val = -2 →
        hD.boundaryPeriod hgenus hw (Multiplicative.ofAdd x) ≠ 1)
    (q : CodimensionOnePoint X) (hq : Disjoint (closure {(q : X)}) (D.support : Set X)) :
    let : IsNoetherian X := isNoetherian_of_finiteType s
    let := (s).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    Chow.classIntersectionNumber k X (primeDivisorClass q) (primeDivisorClass q) ≠ -2 := by
  intro _ _
  obtain ⟨hqK, hperiod⟩ := hD.boundaryPeriod_eq_one_of_disjoint_primeDivisor hgenus hw q hq
  exact fun hsq ↦ hroot ⟨_, hqK⟩
    (by simpa only [Chow.intersectionBilinForm_apply, toMul_ofMul] using hsq) hperiod

/-- If the boundary period is injective, the boundary meets every prime curve. -/
theorem not_disjoint_primeDivisor_of_boundaryPeriod_injective
    (hinj : Function.Injective (hD.boundaryPeriod hgenus hw)) (q : CodimensionOnePoint X) :
    ¬Disjoint (closure {(q : X)}) (D.support : Set X) := by
  intro hq
  let : IsNoetherian X := isNoetherian_of_finiteType s
  let := (s).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  obtain ⟨hqK, hperiod⟩ := hD.boundaryPeriod_eq_one_of_disjoint_primeDivisor hgenus hw q hq
  have heq := hinj (hperiod.trans ((hD.boundaryPeriod hgenus hw).map_one).symm)
  have hclass := congrArg (fun a : Multiplicative (D.boundaryOrthogonal k) ↦ a.toAdd.val.toMul) heq
  obtain ⟨H, hH⟩ := X.exists_isAmple_of_isProjectiveOver k
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension s (n := 2)
  have hpos := Chow.classIntersectionNumber_primeDivisorClass_pos_of_isAmple k hdim hH q
  have hqOne : primeDivisorClass q = 1 := hclass
  exact (ne_of_gt hpos) (by rw [hqOne, Chow.classIntersectionNumber_one_right])

end Period

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
