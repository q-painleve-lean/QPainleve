/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.ProjectivePlane

import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Ray

/-!
# Preparing the mutation at a plane boundary edge

Blowing up the vertex opposite a specified edge of the toric plane inserts the ray
opposite the edge ray. In the resulting Hirzebruch-one coordinates the old edge is
section two and the new exceptional ray is section zero. This identifies the pivot
section for the plane-edge link of Lutz's [Proposition 8.11][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open Module PointedCone

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (d : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)

local notation "Φ" => projectiveSpace d hi
local notation "reg" => isRegular_projectiveSpace d hi
local notation "σ(" k ")" => projectiveSpaceMaximalCone d hi k
local notation "Ψ(" k ")" => Fan.starSubdivisionAlong Φ reg (Subtype.property (σ(k)))
local notation "subdiv(" k "," h ")" =>
  Fan.starSubdivisionAlong_isSubdivision Φ reg (Subtype.property (σ(k))) h

/-- Subdividing at the vertex opposite the chosen plane ray makes its lift the
section on ray two of a Hirzebruch-one fan. The inserted ray is indexed by zero. -/
theorem exists_projectivePlane_starSubdivision_opposite_ray (ρ : (Φ).Ray) :
    ∃ (k : Option (Fin 2)) (hσ : (σ(k)).val ≠ ⊥) (b : Basis (Fin 2) ℤ N)
      (r : Fin 4 ≃ (Ψ(k)).Ray),
      (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (1 : ℤ) • b 0 - b 1] ∧
      (subdiv(k,hσ)).liftRay ρ = r 2 ∧
      (Φ).starSubdivisionAlongRay reg (Subtype.property (σ(k))) hσ = r 0 := by
  obtain ⟨k, hk⟩ := (range_primitiveGenerator_projectiveSpace d hi ▸ Set.mem_range_self ρ)
  obtain ⟨hσ, b, _, hrays, hnew, -, -, hb₀⟩ :=
    exists_blowup_projectivePlane_vertex_hirzebruchOne d hi k
  obtain ⟨r, hr⟩ := exists_rayEquiv_of_hirzebruch_ray_generators b 1
    (by simpa only [Nat.cast_one, one_smul] using hrays)
  refine ⟨k, hσ, b, r, by simpa only [Nat.cast_one] using hr, ?_, ?_⟩
  · have hb : b 0 = -ρ.primitiveGenerator :=
      hb₀.trans (congrArg Neg.neg hk)
    apply Ray.primitiveGenerator_injective
    rw [IsSubdivision.primitiveGenerator_liftRay]
    simpa [hb] using (congrFun hr 2).symm
  · exact Ray.primitiveGenerator_injective (hnew.trans (congrFun hr 0).symm)

end TauCeti.Toric.Fan
