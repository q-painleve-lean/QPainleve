/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction
public import QPainleve.Geometry.Toric.Fan.Boundary.DualGraph

/-!
# Ray coordinates for a numbered toric boundary

A numbering inherited from a surface boundary determines an order on the rays of
its toric model. In one of the two lattice orientations, consecutive rays have
determinant one and the numbered nodes are their distinguished intersection
points. This allows reconstruction from ordered boundary classes as in
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
Remark 2.4 and the proof of Theorem 1.8](https://arxiv.org/html/1211.6367v5#S2).
-/

public noncomputable section

open AlgebraicGeometry DihedralGroup TauCeti.AlgebraicGeometry
open Scheme (NodalCycleNumbering)
open Scheme.IdealSheafData
open Module (Basis)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]

local notation "D[" Φ "]" => Fan.boundaryIdeal Φ inferInstance
local notation "C[" Φ "]" => Scheme.IdealSheafData.subscheme D[Φ]
local notation "S" => Spec (CommRingCat.of ℂ)

variable [PrestableFamily (C[Φ] ↘ S)]
  {ι : Type*} {p : ι → (C[Φ] ↘ S).smoothLocus} {n : ℕ} [NeZero n]

private theorem exists_dihedral_of_same_initial_vertex (A B : NodalCycleNumbering p n)
    (h₀ : A.vertex 0 = B.vertex 0) :
    ∃ g : DihedralGroup n, (g = .r 0 ∨ g = .sr 0) ∧
      (∀ j, A.vertex j = B.vertex (cycleVertexPerm g j)) ∧
      ∀ j, A.edge j = B.edge (cycleBranchPerm g (j, 0)).1 := by
  let coordinates (P : NodalCycleNumbering p n) :=
    (P.edge.prodCongr (Equiv.refl (Fin 2))).trans (Equiv.prodCongrRight P.order)
  have hcoordinates (P : NodalCycleNumbering p n) (z : ZMod n × Fin 2) :
      coordinates P z = (P.edge z.1, P.order (P.edge z.1) z.2) := by
    obtain ⟨j, a⟩ := z
    simp only [coordinates, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply,
      Equiv.refl_apply, Equiv.prodCongrRight_apply]
  let f := (coordinates A).trans (coordinates B).symm
  have hf (j : ZMod n) (a : Fin 2) :
      (B.edge (f (j, a)).1, B.order (B.edge (f (j, a)).1) (f (j, a)).2) =
        (A.edge j, A.order (A.edge j) a) := by
    rw [← hcoordinates B (f (j, a)), ← hcoordinates A (j, a)]
    exact (coordinates B).apply_symm_apply (coordinates A (j, a))
  have he (j : ZMod n) (a : Fin 2) : (f (j, a)).1 = B.edge.symm (A.edge j) :=
    B.edge.eq_symm_apply.mpr (congrArg Prod.fst (hf j a))
  have hv (j : ZMod n) (a : Fin 2) :
      (TauCeti.DualGraph.cycle n).endpoint (f (j, a)).1 (f (j, a)).2 =
        B.vertex.symm (A.vertex ((TauCeti.DualGraph.cycle n).endpoint j a)) := by
    apply B.vertex.eq_symm_apply.mpr
    obtain ⟨hedge, horder⟩ := Prod.mk.inj (hf j a)
    rw [← B.endpoint_eq, horder, hedge, A.endpoint_eq]
  obtain ⟨g, hg⟩ := (existsUnique_cycleBranchPerm f
    (fun j ↦ B.edge.symm (A.edge j)) (fun j ↦ B.vertex.symm (A.vertex j)) he hv).exists
  have hvertex (j : ZMod n) : A.vertex j = B.vertex (cycleVertexPerm g j) := by
    have h := (cycle_endpoint_cycleBranchPerm g j 0).symm.trans (hg ▸ hv j 0)
    simpa [TauCeti.DualGraph.cycle] using (B.vertex.eq_symm_apply.mp h).symm
  have hzero : cycleVertexPerm g 0 = 0 := B.vertex.injective ((hvertex 0).symm.trans h₀)
  refine ⟨g, ?_, hvertex, fun j ↦ (congrArg Prod.fst (hg ▸ hf j 0)).symm⟩
  cases g with
  | r a =>
    rw [cycleVertexPerm_r_apply, zero_add] at hzero
    exact Or.inl (congrArg DihedralGroup.r hzero)
  | sr a =>
    rw [cycleVertexPerm_sr_apply, sub_zero, neg_eq_zero] at hzero
    exact Or.inr (congrArg DihedralGroup.sr hzero)

variable (Φ) in
/-- Read each numbered normalized component of the toric boundary as a ray. -/
def rayEquivOfNodalCycleNumbering (hΦ : Φ.IsRegular) (A : NodalCycleNumbering p n) :
    ZMod n ≃ Φ.Ray :=
  A.component.trans (Φ.boundaryNormalizationComponentEquiv hΦ).symm

/-- The ray read from a numbered component has that component as its normalization. -/
@[simp]
theorem boundaryNormalizationComponentEquiv_rayEquivOfNodalCycleNumbering
    (hΦ : Φ.IsRegular) (A : NodalCycleNumbering p n) (j : ZMod n) :
    Φ.boundaryNormalizationComponentEquiv hΦ (Φ.rayEquivOfNodalCycleNumbering hΦ A j) =
      A.component j :=
  Equiv.apply_symm_apply _ _

variable (Φ) in
/-- Every numbering of the reduced boundary of a complete regular rank-two fan
determines a numbering of its rays. With the original basis or its transposition,
successive rays have determinant one. The common two-ray cone represents the
actual numbered node, and the ray order agrees with the numbered branch endpoints. -/
theorem exists_positive_ray_numbering_of_nodalCycleNumbering
    (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (A : NodalCycleNumbering p n) :
    let u := Φ.rayEquivOfNodalCycleNumbering hΦ A
    ∃ b' : Basis (Fin 2) ℤ N,
      (b' = b ∨ b' = b.reindex (Equiv.swap 0 1)) ∧
      (∀ j, b'.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1) ∧
      ∀ j, ∃ σ : {σ : Φ.cones // Nat.card (ToricRay σ.val) = 2},
        (u j).toCone ≤ σ.val ∧ (u (j + 1)).toCone ≤ σ.val ∧
        (D[Φ]).subschemeι ((C[Φ]).dualGraphEdgeEquiv p (A.edge j)).val =
          Φ.distinguishedPointHom σ.val (IsLocalRing.closedPoint ℂ) := by
  intro u
  let v := Φ.boundaryNormalizationComponentEquiv hΦ
  have hu (j : ZMod n) : A.component j = v (u j) :=
    (boundaryNormalizationComponentEquiv_rayEquivOfNodalCycleNumbering hΦ A j).symm
  have hn : n = Nat.card Φ.Ray := (Nat.card_zmod n).symm.trans (Nat.card_congr u)
  have hnumbering :
      ∃ r : ZMod n ≃ Φ.Ray, r 0 = u 0 ∧
        ∀ j, b.detDualEquiv (r j).primitiveGenerator (r (j + 1)).primitiveGenerator = 1 ∧
          ∃ σ : Φ.cones, (r j).toCone ≤ σ ∧ (r (j + 1)).toCone ≤ σ := by
    generalize u 0 = ρ
    rw [hn]
    exact (Φ.existsUnique_cyclicRayNumbering b hΦ hc ρ).exists
  obtain ⟨r, hr₀, hr⟩ := hnumbering
  obtain ⟨e, o, w, hw, hcomp, hnode⟩ :=
    Φ.exists_toric_boundary_dualGraph_cycle hΦ hc p b r hr
  let B : NodalCycleNumbering p n := ⟨w, e, o, hw⟩
  have hB (j : ZMod n) : B.component j = v (r j) := by
    rw [B.component_apply]
    exact hcomp j
  have h₀ : A.vertex 0 = B.vertex 0 := by
    apply ((C[Φ]).dualGraphVertexEquiv p).injective
    rw [← A.component_apply, ← B.component_apply, hu]
    exact (congrArg v hr₀).symm.trans (hB 0).symm
  obtain ⟨g, hg, hAg, hEg⟩ := exists_dihedral_of_same_initial_vertex A B h₀
  have hRay (j : ZMod n) : u j = r (cycleVertexPerm g j) := by
    apply v.injective
    rw [← hu, A.component_apply, hAg]
    exact hcomp _
  rcases hg with h | h
  · have hEq (j : ZMod n) : u j = r j := by
      simpa only [h, cycleVertexPerm_r_apply, add_zero] using hRay j
    refine ⟨b, Or.inl rfl, fun j ↦ ?_, fun j ↦ ?_⟩
    · simpa only [hEq] using (hr j).1
    · simpa only [hEq, hEg, h, cycleBranchPerm_r_apply, add_zero] using hnode j
  · have hEq (j : ZMod n) : u j = r (-j) := by
      simpa only [h, cycleVertexPerm_sr_apply, neg_zero, zero_sub] using hRay j
    refine ⟨b.reindex (Equiv.swap 0 1), Or.inr rfl, fun j ↦ ?_, fun j ↦ ?_⟩
    · simpa only [hEq] using (cyclicRayNumbering_neg b r hr j).1
    · have hj : -1 - j + 1 = -j := by abel
      have hj' : -(j + 1) = -1 - j := by abel
      obtain ⟨σ, h₁, h₂, hpoint⟩ := hnode (-1 - j)
      exact ⟨σ, by simpa only [hEq, hj] using h₂, by simpa only [hEq, hj'] using h₁,
        by simpa only [hEg, h, cycleBranchPerm_sr_apply, neg_zero, zero_sub] using hpoint⟩

end TauCeti.Toric.Fan
