/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.Step

import QPainleve.Geometry.Toric.Fan.Logarithmic.Quadric.Factorization

/-!
# Resolved Sarkisov paths for a plane degree decrease

A decreasing plane block determines a path on its common nodal refinement.
The vertex case is a single toric blowup. The edge case continues after the
blowup with the specified mutation and quadric ruling exchange. The endpoint
projections are the prescribed maps, so the block can be concatenated with
other resolved blocks in the Sarkisov induction.

See [Lutz, Proposition 8.11 and Theorem 8.4][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=71
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry TauCeti.SymmetricAlgebra TauCeti.Toric
open Fan (LogarithmicProjection)
open Fan.LogarithmicProjection Scheme.IdealSheafData
open scoped Sarkisov

namespace QPainleve.BlowupTower.IsClosedPointTower

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "P" => Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))
local notation "X[" Φ "]" => Fan.finiteFanScheme k₀ Φ
local notation "f[" Φ "]" => (X[Φ] ↘ S)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

section Continuation

variable {W : Scheme} [W.Over (Spec (.of k₀))] [SmoothOfRelativeDimension 2 (W ↘ Spec (.of k₀))]
  {D : W.IdealSheafData}

local instance : Smooth (W ↘ S) := SmoothOfRelativeDimension.smooth 2 _

omit [IsAlgClosed k₀] in
private theorem exists_continuation_path [IsIntegral W] (A : LogarithmicProjection k₀ i D)
    {index : ℕ} {Ψ : Fan i} {p : W ⟶ X[Ψ]}
    (h : ResolvesPlaneSarkisovLink k₀ A.hom D index Ψ p) :
    ∃ (C : LogarithmicProjection k₀ i D) (path : SarkisovPath A C),
      C.fan = Ψ ∧ C.hom ≍ p ∧ path.length = if index = 0 then 2 else 0 := by
  cases h with
  | vertex => exact ⟨A, .nil, rfl, HEq.rfl, rfl⟩
  | edge b ρ c hOpp hΨ hcΨ b' r hr p hp hmap hpole =>
    let : p.IsOver S := hp
    exact A.exists_mutation_rulingExchange_path b ρ c hOpp hΨ hcΨ b' r hr p hmap hpole

end Continuation

variable {d : Basis (Fin 2) ℤ N} {hi : IsIntegralLattice i}
  {Y : Scheme} {n : ℕ} {T : BlowupTower (Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))) n Y}
    {hT : IsClosedPointTower (Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))) T}
  {g : Y ⟶ (Proj (homogeneousSubmodule k₀ (Fin 3 → k₀)))} {D : Y.IdealSheafData}

local notation "Π" => Fan.projectiveSpace d hi
local notation "eP" =>
  Fan.projectivePlaneIso k₀ d hi ≪≫ Module.Basis.polynomialProjIso (Pi.basisFun k₀ (Fin 3))
local notation "σ" => Fan.projectiveSpaceMaximalCone d hi
local notation "reg" => Fan.isRegular_projectiveSpace d hi
local notation "Φ[" v "]" => Fan.starSubdivisionAlong Π reg (Subtype.property (σ v))

/-- A decreasing Sarkisov block of a specified logarithmic plane resolution gives a
path of resolved links on its common nodal refinement. The source projection is
the refined original plane map in toric coordinates, and the target projection
is the one identified by the returned point tower. The path consists of the vertex
blowup alone or the blowup, binomial mutation and ruling exchange. -/
theorem PlaneSarkisovDecrease.exists_path (R : PlaneSarkisovDecrease k₀ d hi hT g D) :
    let : R.resolving.Over S := ⟨R.first ≫ f[Φ[R.vertexIndex]]⟩
    let : SmoothOfRelativeDimension 2 (R.resolving ↘ S) := R.smooth
    let : IsIntegral R.resolving := R.integral
    ∃ (A C : LogarithmicProjection k₀ i (D.comap R.refinement).radical) (path : SarkisovPath A C),
      A.fan = Π ∧ A.hom ≍ R.refinement ≫ T.toBase ≫ (eP).inv ∧
      C.fan = R.fan ∧ C.hom ≍ R.modelIso.hom ≫ R.modelTower.toBase ∧
      path.length = if R.index = 0 then 3 else 1 := by
  intro hOver hSmooth hIntegral
  let := hOver
  let := hSmooth
  let := hIntegral
  let hstar : Π.IsTwoRayStarSubdivision (Φ[R.vertexIndex]) :=
    .along reg (σ R.vertexIndex) (Fan.card_toricRay_projectiveSpaceMaximalCone d hi R.vertexIndex)
  let B : LogarithmicProjection k₀ i (D.comap R.refinement).radical :=
    { fan := Φ[R.vertexIndex]
      isRegular := Fan.isRegular_starSubdivisionAlong Π reg (σ R.vertexIndex).property
      isComplete := hstar.isSubdivision.isComplete_iff.mpr (Fan.isComplete_projectiveSpace d hi)
      hom := R.first
      isOver := ⟨rfl⟩
      isDominant := R.first_dominant
      comap_boundaryIdeal := R.first_pole }
  have hRank := (finrank_eq_card_basis d).trans (Fintype.card_fin 2)
  let A := B.coarsen hstar.isSubdivision reg hRank
  have start : StarStep A B := by
    have step := B.coarsenBlowup hRank reg B.isRegular hstar (.refl B.fan)
    rwa [B.coarsen_refl hRank] at step
  obtain ⟨C, path, hfan, hhom, hlength⟩ := exists_continuation_path k₀ B R.link
  let p : SarkisovPath A B := Quiver.Hom.toPath start.toSarkisovStep
  refine ⟨A, C, p.comp path, coarsen_fan .., ?_, hfan, hhom, ?_⟩
  · refine (coarsen_hom ..).trans (heq_of_eq ?_)
    have h := congrArg (fun k ↦ k ≫ (eP).inv) R.first_comp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
  · rw [Quiver.Path.length_comp, Quiver.Path.length_toPath, hlength]
    split <;> rfl

end QPainleve.BlowupTower.IsClosedPointTower
