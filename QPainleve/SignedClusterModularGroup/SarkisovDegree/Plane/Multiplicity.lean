/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.PlaneResolution
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.Isomorphism

/-!
# Proper high-multiplicity centers of plane maps

A specified plane resolution either has degree one or has a proper base point
of order greater than one third of the degree. This is the pivot selection in
the plane case of Proposition 8.11 in [Lutz's appendix to Hacking and Keating][HKL].
An infinitely near center that passes the numerical threshold gives a first
center over the same point that still passes it.

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=71
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry LineBundleClass Chow TauCeti.SymmetricAlgebra

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [IsAlgClosed k]

local notation "S" => Spec (CommRingCat.of k)
local notation "P" => Proj (homogeneousSubmodule k (Fin 3 → k))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) 1)
local notation "f" => (P ↘ S)
local notation "degree" => Module.Basis.picardTwistEquiv (Pi.basisFun k (Fin 3))

/-- The degree of a birational plane map is positive and all its base orders are
nonnegative on a specified point-blowup resolution. If the degree exceeds one,
there is a first blowup over a proper point whose order exceeds one third of
the degree. -/
theorem plane_degree_eq_one_or_exists_high_baseCenter {Y : Scheme.{u}} {n : ℕ}
    {T : BlowupTower P n Y} (hT : IsClosedPointTower P T)
    (g : Y ⟶ P) (hg : g ≫ f = T.toBase ≫ f) (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : IsNoetherian P := isNoetherian_of_finiteType f
    let v := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    0 < degree v.1 ∧ (∀ j, 0 ≤ -v.2 j) ∧
      (degree v.1 = 1 ∨ ∃ j : Fin n, degree v.1 < 3 * (-v.2 j) ∧
        ∀ i < j, hT.baseCenter i ≠ hT.baseCenter j) := by
  intro hNoeth v
  let := hNoeth
  obtain ⟨_, _, -, -, -, -, -, horder⟩ := hT.exists_moving_base_ideal_of_plane_resolution g hg
  have hm (j : Fin n) : 0 ≤ -v.2 j := by
    rw [horder j]
    exact Int.natCast_nonneg _
  have hsum := (hT.homaloidal_intersection_identities g hg hbir).2
  rw [classIntersectionNumber_projectivePlane, ofMul_toMul, mk_canonicalBundle_projectivePlane,
    Module.Basis.picardTwistEquiv_apply_twist] at hsum
  have hd : 0 < degree v.1 := by
    have hnonneg : 0 ≤ ∑ j, -v.2 j := Finset.sum_nonneg (fun j _ ↦ hm j)
    have he : (∑ j, -v.2 j) = -(degree v.1 * -3) - 3 := hsum
    omega
  refine ⟨hd, hm, ?_⟩
  by_cases hd₁ : degree v.1 = 1
  · exact Or.inl hd₁
  · right
    have hex : ∃ j : Fin n, degree v.1 < 3 * (-v.2 j) := by
      by_contra! h
      exact hd₁ (hT.plane_degree_eq_one_of_no_high_multiplicity g hg hbir hd
        (fun j ↦ ⟨hm j, h j⟩))
    obtain ⟨j, hj⟩ := hex
    obtain ⟨i, -, hi, hji⟩ := hT.exists_first_baseCenter_ge_of_plane_resolution g hg j
    have hle : -v.2 j ≤ -v.2 i := hji
    exact ⟨i, by omega, hi⟩

end QPainleve.BlowupTower.IsClosedPointTower
