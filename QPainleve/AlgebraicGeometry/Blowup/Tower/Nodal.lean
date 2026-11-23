/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Refinement
public import QPainleve.AlgebraicGeometry.Curves.Node.Locus

/-!
# Common refinements of nodal boundary blowups

Nodal boundary towers blow up nonsmooth nodal points of the reduced total
transform on each successive scheme. Two such towers admit a common nodal
refinement, and the same holds for a finite family. The final isomorphisms
respect the morphisms to the base scheme and identify the reduced boundaries.
-/

public section

open AlgebraicGeometry CategoryTheory

universe u

namespace QPainleve.BlowupTower

variable {S K X Y Z : Scheme.{u}} {m n : ℕ}

/-- The reduced total transform of `D` has a node at every blowup center of the tower. -/
abbrev IsNodalBoundaryTower (D : S.IdealSheafData) (s : S ⟶ K) (π : X ⟶ S)
    (T : BlowupTower X n Y) : Prop :=
  IsPointTowerWith (fun {_} g p ↦ (D.comap g).IsNodeOfReducedBoundary (g ≫ s) p) π T

private theorem isLocal_node (D : S.IdealSheafData) (s : S ⟶ K) :
    PointCondition.IsLocal (fun {_} g p ↦ (D.comap g).IsNodeOfReducedBoundary (g ≫ s) p) := by
  constructor
  intro A B f g x hx hn
  rw [D.comap_comp, Category.assoc]
  exact ((D.comap g).isNodeOfReducedBoundary_comap_iff_of_mem_isoLocus (g ≫ s) f hx).mpr hn

/-- Two nodal boundary towers admit a common refinement through nodal centers.
Each extension has length at most that of the opposite tower. The final isomorphism
lies over the original scheme and matches the reduced total transforms of the boundary. -/
theorem IsNodalBoundaryTower.exists_common_nodal_boundary_tower_refinement
    {D : S.IdealSheafData} {s : S ⟶ K} {π : X ⟶ S}
    {T : BlowupTower X m Y} {U : BlowupTower X n Z}
    (hT : IsNodalBoundaryTower D s π T) (hU : IsNodalBoundaryTower D s π U) :
    ∃ (a b : ℕ) (A B : Scheme.{u}) (L : BlowupTower Y a A)
      (R : BlowupTower Z b B) (e : A ≅ B),
      a ≤ n ∧ b ≤ m ∧ IsNodalBoundaryTower D s (T.toBase ≫ π) L ∧
      IsNodalBoundaryTower D s (U.toBase ≫ π) R ∧
      L.toBase ≫ T.toBase = e.hom ≫ R.toBase ≫ U.toBase ∧
      ((D.comap (R.toBase ≫ U.toBase ≫ π)).radical).comap e.hom =
        (D.comap (L.toBase ≫ T.toBase ≫ π)).radical := by
  obtain ⟨a, b, A, B, L, R, e, ha, hb, hL, hR, h⟩ :=
    IsPointTowerWith.exists_common_point_tower_refinement hT hU (isLocal_node D s)
  refine ⟨a, b, A, B, L, R, e, ha, hb, hL, hR, h, ?_⟩
  rw [← Scheme.IdealSheafData.radical_comap_of_isOpenImmersion, ← D.comap_comp,
    ← reassoc_of% h]

/-- A finite family of nodal boundary towers admits a common nodal boundary refinement.
The comparisons commute with the projections and identify the final reduced boundaries. -/
theorem exists_common_nodal_boundary_tower_refinement_finset
    (D : S.IdealSheafData) (s : S ⟶ K) (π : X ⟶ S)
    {ι : Type*} (F : Finset ι) {n : ι → ℕ} {Y : ι → Scheme.{u}}
    (T : ∀ i, BlowupTower X (n i) (Y i)) (hT : ∀ i ∈ F, IsNodalBoundaryTower D s π (T i)) :
    ∃ (m : ℕ) (Z : Scheme.{u}) (U : BlowupTower X m Z), IsNodalBoundaryTower D s π U ∧
      ∀ i ∈ F, ∃ (a : ℕ) (A : Scheme.{u}) (L : BlowupTower (Y i) a A) (e : Z ≅ A),
        IsNodalBoundaryTower D s ((T i).toBase ≫ π) L ∧
        U.toBase = e.hom ≫ L.toBase ≫ (T i).toBase ∧
        ((D.comap (L.toBase ≫ (T i).toBase ≫ π)).radical).comap e.hom =
          (D.comap (U.toBase ≫ π)).radical := by
  obtain ⟨m, Z, U, hU, h⟩ :=
    IsPointTowerWith.exists_common_point_tower_refinement_finset F T hT (isLocal_node D s)
  refine ⟨m, Z, U, hU, fun i hi ↦ ?_⟩
  obtain ⟨a, A, L, e, hL, hbase⟩ := h i hi
  refine ⟨a, A, L, e, hL, hbase, ?_⟩
  rw [← Scheme.IdealSheafData.radical_comap_of_isOpenImmersion, ← D.comap_comp,
    reassoc_of% hbase]

end QPainleve.BlowupTower
