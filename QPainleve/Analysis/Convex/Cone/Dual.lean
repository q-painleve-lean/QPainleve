/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Analysis.Convex.Cone.Dual

/-!
# Dual cones under linear equivalences

Compatible changes of coordinates on the two sides of a continuous perfect pairing
identify the dual cones of corresponding sets.
-/

public section

namespace ProperCone

variable {R E F E' F' : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
  [TopologicalSpace R] [ClosedIciTopology R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F]
  [AddCommGroup E'] [Module R E'] [TopologicalSpace E']
  [AddCommGroup F'] [Module R F'] [TopologicalSpace F']
  {p : E →ₗ[R] F →ₗ[R] R} {q : E' →ₗ[R] F' →ₗ[R] R}
  [p.IsContPerfPair] [q.IsContPerfPair]

/-- For a linear map and a compatible equivalence on its paired space, the dual of the
image is the image of the dual. -/
theorem coe_dual_image_eq_image (e : E →ₗ[R] E') (f : F ≃ₗ[R] F')
    (h : ∀ x y, q (e x) (f y) = p x y) (s : Set E) :
    (dual q (e '' s) : Set F') = f '' (dual p s : Set F) := by
  ext y
  obtain ⟨y, rfl⟩ := f.surjective y
  simp only [SetLike.mem_coe, mem_dual, Set.forall_mem_image,
    f.injective.mem_set_image, h]

end ProperCone
