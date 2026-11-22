/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.XMutation.Chart

/-!
# Evaluation on X mutation charts

A tuple of units whose pivot binomial is also a unit defines evaluation on the
localized Laurent ring of a mutation chart. This allows specialization at fixed
centers even when evaluation on the entire X function field is unavailable.
-/

public noncomputable section

namespace QPainleve.Cluster

open TauCeti LaurentRing

variable {R A ι : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  (p : ι) (x : ι → Aˣ) (h : IsUnit (1 + (x p : A)))

/-- Evaluate an X mutation chart at a tuple of units with invertible pivot binomial. -/
def xMutationChartEval : XMutationChart R p →ₐ[R] A :=
  IsLocalization.Away.liftAlgHom (1 + (X p : LaurentRing R ι)) (f := aeval x)
    (by simpa only [map_add, map_one, aeval_X] using h)

/-- Chart evaluation extends Laurent evaluation. -/
@[simp]
theorem xMutationChartEval_algebraMap (f : LaurentRing R ι) :
    xMutationChartEval (R := R) p x h (algebraMap _ _ f) = aeval x f := by
  simp [xMutationChartEval]

end QPainleve.Cluster
