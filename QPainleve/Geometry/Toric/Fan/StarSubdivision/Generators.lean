/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ray
public import TauCeti.Geometry.Toric.Algebraic.Fan.StarSubdivision

/-!
# Primitive generators of a star subdivision

A star subdivision retains every old ray. A ray whose least cone contains the
subdivision center must be the ray through the sum of the center's generators.
-/

public section

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

/-- The rays of a star subdivision have the old primitive generators and the primitive
generator of the inserted ray. This also applies to subdivision along a ray, when the
inserted generator already belongs to the original range. -/
theorem range_primitiveGenerator_starSubdivisionAlong (hΦ : Φ.IsRegular) (σ : Φ.cones)
    (hσ : σ.val ≠ ⊥) :
    Set.range (Ray.primitiveGenerator (Phi := Φ.starSubdivisionAlong hΦ σ.property)) =
      insert (Φ.starSubdivisionAlongRay hΦ σ.property hσ).primitiveGenerator
        (Set.range (Ray.primitiveGenerator (Phi := Φ))) := by
  let r := Φ.starSubdivisionAlongRay hΦ σ.property hσ
  let h := Φ.starSubdivisionAlong_isSubdivision hΦ σ.property hσ
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨s, rfl⟩
    by_cases hs : s = r
    · exact Set.mem_insert_iff.mpr (Or.inl (congrArg Ray.primitiveGenerator hs))
    have hle : ¬ r.toCone ≤ s.toCone := by
      intro hle
      exact hs (Ray.primitiveGenerator_injective
        (r.primitiveGenerator_eq_of_toCone_le_hull s.toCone_eq_hull_primitiveGenerator
          s.isPrimitiveGenerator.isPrimitive hle).symm)
    have hleast := mt
      (Φ.starSubdivisionAlongRay_le_iff_le_leastCone hΦ σ.property hσ s.toCone).mpr hle
    have hsΦ := ((Φ.not_le_leastCone_starSubdivisionAlong_iff hΦ σ.property hσ
      s.toCone.property).mp hleast).1
    let t : Φ.Ray := ⟨⟨s.toCone.val, hsΦ⟩, s.property⟩
    exact Set.mem_insert_of_mem _ ⟨t,
      t.primitiveGenerator_eq_of_mem_of_isPrimitive s.primitiveGenerator_mem
        s.isPrimitiveGenerator.isPrimitive⟩
  · intro _ hx
    rcases Set.mem_insert_iff.mp hx with rfl | ⟨t, rfl⟩
    · exact Set.mem_range_self r
    · exact ⟨h.liftRay t, h.primitiveGenerator_liftRay t⟩

end TauCeti.Toric.Fan
