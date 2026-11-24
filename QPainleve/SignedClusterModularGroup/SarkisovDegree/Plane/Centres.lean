/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Centres
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.PlaneEdge

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision

/-!
# Selecting the plane vertex or edge of a specified Sarkisov center

A logarithmic resolution of the toric plane places a projected center either at a
coordinate vertex or at a binomial point on an edge. In the edge case, blowing up
the opposite vertex makes the point a binomial point on section two of the
Hirzebruch-one fan. The projection maps that point to the specified original
center and is an isomorphism there. This selects the links in the plane case of
Lutz's [Proposition 8.11][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry TauCeti.Toric

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (d : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Φ" => projectiveSpace d hi
local notation "X" => Fan.algebraicRealization Φ
local notation "hc" => isComplete_projectiveSpace d hi
local notation "reg" => isRegular_projectiveSpace d hi
local notation "σ(" k ")" => projectiveSpaceMaximalCone d hi k
local notation "Ψ(" k ")" => Fan.starSubdivisionAlong Φ reg (Subtype.property (σ(k)))
local notation "subdiv(" k "," h ")" =>
  Fan.starSubdivisionAlong_isSubdivision Φ reg (Subtype.property (σ(k))) h
local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis d) (Fintype.card_fin 2))
local notation "point" => IsLocalRing.closedPoint ℂ

/-- Each projected center of a logarithmic point tower over the toric plane is one of
the specified coordinate vertices, or lifts through the opposite-vertex subdivision to
a binomial center on section two. In the latter case the subdivision projection carries
the reduced point ideal back to the binomial ideal and is an isomorphism at the center. -/
theorem projectivePlane_baseCenter_cases_of_totalTransform_le_ramification
    {Y : Scheme} {n : ℕ} {T : QPainleve.BlowupTower X n Y}
    (hT : QPainleve.BlowupTower.IsClosedPointTower X T) :
    letI : SmoothOfRelativeDimension 2 (X ↘ S) :=
      by
        have hdim : finrank ℤ N = 2 := rankTwo
        simpa only [hdim, Fan.algebraicRealization_over] using
          (Φ).smoothOfRelativeDimension_algebraicRealizationStructureMap reg
    let D := (Φ).boundaryIdeal (IsComplete.nonempty_cones hc)
    D.comap T.toBase ≤ hT.ramificationIdealSheafToBase ℂ →
    ∀ j : Fin n, let p := hT.baseCenter j
      (∃ k : Option (Fin 2), (Φ).distinguishedPointHom (σ(k)) point = p) ∨
      (∃ (k : Option (Fin 2)) (hσ : (σ(k)).val ≠ ⊥) (b : Basis (Fin 2) ℤ N)
          (r : Fin 4 ≃ (Ψ(k)).Ray) (c : ℂˣ),
        let ρ := r 2
        let π := (subdiv(k,hσ)).toFanHom.algebraicMap
        let q := ρ.binomialCenter rankTwo (b.detDualEquiv_self ρ.primitiveGenerator)
          (ρ.surjective_detCharacter b) c
        (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, (1 : ℤ) • b 0 - b 1] ∧
        (Φ).starSubdivisionAlongRay reg (Subtype.property (σ(k))) hσ = r 0 ∧
        π (q point) = p ∧ p ∈ π.isoLocus ∧
        (Scheme.fromSpecResidueField X p).ker.comap π = q.ker) := by
  intro D h j p
  let : Nonempty (Φ).cones := IsComplete.nonempty_cones hc
  have hdim : finrank ℤ N = 2 := rankTwo
  let : SmoothOfRelativeDimension 2 (X ↘ S) := by
    simpa only [hdim, Fan.algebraicRealization_over] using
      (Φ).smoothOfRelativeDimension_algebraicRealizationStructureMap reg
  rcases (Φ).baseCenter_cases_of_totalTransform_le_ramification d reg hc hT h j with
    ⟨σ, ⟨hσ, hp⟩, -⟩ | ⟨-, ⟨⟨ρ, c⟩, hI, -⟩⟩
  · obtain ⟨k, rfl⟩ := exists_eq_projectiveSpaceMaximalCone_of_card_toricRay_eq_two d hi σ hσ
    exact Or.inl ⟨k, hp⟩
  obtain ⟨k, hσ, b, r, hr, hρ, hnew⟩ :=
    exists_projectivePlane_starSubdivision_opposite_ray d hi ρ
  let u := ρ.binomialCenter rankTwo (d.detDualEquiv_self ρ.primitiveGenerator)
    (ρ.surjective_detCharacter d) c
  let x : S := point
  have hu : u x = p := by
    apply Scheme.ker_fromSpecResidueField_inj.mp
    rw [← u.ker_eq_ker_fromSpecResidueField, ← ρ.map_internalCenter_subschemeι d c]
    exact hI
  obtain ⟨a, ha⟩ := ρ.exists_binomialCenter_eq_of_basis b d c
  let π := (subdiv(k,hσ)).toFanHom.algebraicMap
  let v := (r 2).binomialCenter rankTwo (b.detDualEquiv_self (r 2).primitiveGenerator)
    ((r 2).surjective_detCharacter b) a
  have hcomp : v ≫ π = u := by
    refine Eq.trans ?_ ha
    dsimp only [v, π]
    rw [← hρ]
    exact (subdiv(k,hσ)).binomialCenter_liftRay_comp_algebraicMap ρ b a
  have hloc : p ∈ π.isoLocus := by
    have hp : (ρ.binomialCenter rankTwo (b.detDualEquiv_self ρ.primitiveGenerator)
        (ρ.surjective_detCharacter b) a) x = p :=
      (congrArg (fun g : S ⟶ X ↦ g x) ha).trans hu
    rw [← hp]
    exact (subdiv(k,hσ)).range_binomialCenter_subset_isoLocus ρ rankTwo
      (b.detDualEquiv_self ρ.primitiveGenerator) (ρ.surjective_detCharacter b) a
      (Set.mem_range_self x)
  have hpt : π (v x) = p := (congrArg (fun g : S ⟶ X ↦ g x) hcomp).trans hu
  have hp : IsClosed ({p} : Set X) := hT.isClosed_baseCenter j
  have hker := π.comap_ker_fromSpecResidueField_of_mem_isoLocus
    (hpt.symm ▸ hp) (hpt.symm ▸ hloc)
  rw [hpt, ← v.ker_eq_ker_fromSpecResidueField] at hker
  exact Or.inr ⟨k, hσ, b, r, a, hr, hnew, hpt, hloc, hker⟩

end TauCeti.Toric.Fan
