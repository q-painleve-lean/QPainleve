/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Subdivision
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime

/-!
# Dihedral reindexing of nodal cycles

Reindexing a numbered nodal cycle by a dihedral element acts on its components,
nodes, and ordered branches. In particular, a reflection exchanges the ordered
branches of a self-node even though its component number is fixed.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory DihedralGroup TauCeti TauCeti.AlgebraicGeometry
open Scheme (NodalCycleNumbering)

universe u v

namespace AlgebraicGeometry.Scheme.NodalCycleNumbering

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [PrestableFamily (X ↘ Spec (.of k))]
  {ι : Type v} {p : ι → (X ↘ Spec (.of k)).smoothLocus} {n : ℕ} [NeZero n]
  (A : NodalCycleNumbering p n)

private def rotate (t : ZMod n) : NodalCycleNumbering p n where
  vertex := (Equiv.addRight t).trans A.vertex
  edge := (Equiv.addRight t).trans A.edge
  order := A.order
  endpoint_eq j b := by
    have h := cycle_endpoint_cycleBranchPerm (.r t) j b
    simp only [cycleBranchPerm_r_apply, cycleVertexPerm_r_apply] at h
    simp only [Equiv.trans_apply, Equiv.coe_addRight, A.endpoint_eq, h]

private theorem rotate_component (t j : ZMod n) :
    (A.rotate t).component j = A.component (j + t) := by
  simp only [component_apply, rotate, Equiv.trans_apply, Equiv.coe_addRight]

private theorem rotate_node (t j : ZMod n) :
    (A.rotate t).node j = A.node (j + t) := by
  simp only [node_apply, rotate, Equiv.trans_apply, Equiv.coe_addRight]

private theorem rotate_branch (t j : ZMod n) (b : Fin 2) :
    (A.rotate t).branch (j, b) = A.branch (j + t, b) := by
  rw [(A.rotate t).branch_eq_branchOrderOfDualGraph, A.rotate_node,
    A.branch_eq_branchOrderOfDualGraph]
  rfl

/-- Read the original numbering at the image of each index under a dihedral element. -/
def reindex (g : DihedralGroup n) : NodalCycleNumbering p n :=
  match g with
  | .r t => A.rotate t
  | .sr t => A.reverse.rotate t

/-- Reindexing acts on the components by the vertex permutation. -/
@[simp] theorem reindex_component (g : DihedralGroup n) (j : ZMod n) :
    (A.reindex g).component j = A.component (cycleVertexPerm g j) := by
  cases g with
  | r t => simpa only [reindex, cycleVertexPerm_r_apply] using A.rotate_component t j
  | sr t =>
    have h : -(j + t) = -t - j := by abel
    simp only [reindex, rotate_component, reverse_component, cycleVertexPerm_sr_apply, h]

/-- Reindexing acts on the points of the branch scheme by the branch permutation. -/
@[simp] theorem reindex_branch (g : DihedralGroup n) (j : ZMod n) (b : Fin 2) :
    (A.reindex g).branch (j, b) = A.branch (cycleBranchPerm g (j, b)) := by
  cases g with
  | r t => simpa only [reindex, cycleBranchPerm_r_apply] using A.rotate_branch t j b
  | sr t =>
    have h : -1 - (j + t) = -t - 1 - j := by abel
    simp only [reindex, rotate_branch, reverse_branch, cycleBranchPerm_sr_apply, h]

/-- Reindexing acts on the nodes by the edge coordinate of the branch permutation. -/
@[simp] theorem reindex_node (g : DihedralGroup n) (j : ZMod n) :
    (A.reindex g).node j = A.node (cycleBranchPerm g (j, 0)).1 := by
  cases g with
  | r t => simpa only [reindex, cycleBranchPerm_r_apply] using A.rotate_node t j
  | sr t =>
    have h : -1 - (j + t) = -t - 1 - j := by abel
    simp only [reindex, rotate_node, reverse_node, cycleBranchPerm_sr_apply, h]

/-- The generic point of a reindexed component is the original generic point at
the corresponding vertex. -/
@[simp] theorem reindex_componentGenericPoint (g : DihedralGroup n) (j : ZMod n) :
    (A.reindex g).componentGenericPoint j = A.componentGenericPoint (cycleVertexPerm g j) := by
  simp only [componentGenericPoint_def, reindex_component]

/-- The numbering of the actual branches determines the whole cycle numbering. -/
@[ext] theorem ext_of_branch {A B : NodalCycleNumbering p n}
    (h : ∀ j b, A.branch (j, b) = B.branch (j, b)) : A = B := by
  have hcoords (j : ZMod n) (b : Fin 2) :
      (A.edge j, A.order (A.edge j) b) = (B.edge j, B.order (B.edge j) b) := by
    apply (X.dualGraphBranchEquiv p).injective
    have hb := h j b
    rw [A.branch_eq_branchOrderOfDualGraph j b, B.branch_eq_branchOrderOfDualGraph j b,
      A.node_apply, B.node_apply, X.branchOrderOfDualGraph_apply_val,
      X.branchOrderOfDualGraph_apply_val] at hb
    exact hb
  have hedge : A.edge = B.edge := Equiv.ext fun j ↦ congrArg Prod.fst (hcoords j 0)
  have horder : A.order = B.order := by
    funext z
    obtain ⟨j, rfl⟩ := A.edge.surjective z
    exact Equiv.ext fun b ↦ by
      simpa only [hedge] using congrArg Prod.snd (hcoords j b)
  have hvertex : A.vertex = B.vertex := Equiv.ext fun j ↦ by
    simpa only [DualGraph.cycle, ite_true, hedge, horder] using
      (A.endpoint_eq j 0).symm.trans (by rw [hedge, horder]; exact B.endpoint_eq j 0)
  cases A
  cases B
  exact mk.injEq .. |>.mpr ⟨hvertex, hedge, horder⟩

/-- Reindexing by the identity preserves the numbering. -/
@[simp] theorem reindex_one : A.reindex 1 = A := by
  ext j b
  simp

/-- Reindexing first by `g` and then by `h` reads the original indices at `g * h`. -/
theorem reindex_mul (g h : DihedralGroup n) : A.reindex (g * h) = (A.reindex g).reindex h := by
  ext j b
  simp only [reindex_branch, map_mul, Equiv.Perm.mul_apply]
  cases cycleBranchPerm h (j, b)
  rw [reindex_branch]

end AlgebraicGeometry.Scheme.NodalCycleNumbering

namespace CategoryTheory.Iso

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [PrestableFamily (X ↘ Spec (.of k))]
  {ι : Type v} {p : ι → (X ↘ Spec (.of k)).smoothLocus} {n : ℕ} [NeZero n]
  (A : NodalCycleNumbering p n)

local instance : (Iso.refl X).hom.IsOver (Spec (.of k)) := by
  rw [Iso.refl_hom]
  infer_instance

/-- The identity from the reindexed cycle to the original cycle realizes the
specified dihedral element on the ordered branches. -/
@[simp] theorem boundaryCycleAction_reindex (g : DihedralGroup n) :
    (Iso.refl X).boundaryCycleAction (A.reindex g) A = g := by
  refine (existsUnique_boundaryCycleAction (Iso.refl X) (A.reindex g) (D := A)).unique
    (branch_boundaryCycleAction _ _ _) ?_
  simp

end CategoryTheory.Iso

namespace AlgebraicGeometry.Scheme.NodalCycleNumbering

open CategoryTheory.Iso

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [PrestableFamily (X ↘ Spec (.of k))]
  {ι : Type v} {p : ι → (X ↘ Spec (.of k)).smoothLocus} {n : ℕ} [NeZero n]
  (A : NodalCycleNumbering p n)

/-- A dihedral reindexing has the same branch orientation as the original cycle
for a rotation, and as the reversed cycle for a reflection. -/
theorem isOrientedCycleSubdivision_reindex (g : DihedralGroup n) :
    (𝟙 X : X ⟶ X).IsOrientedCycleSubdivision (A.reindex g)
      (if cycleOrientationSign g = -1 then A.reverse else A) := by
  let e := Iso.refl X
  let : e.hom.IsOver (Spec (.of k)) := ⟨Category.id_comp _⟩
  have rotation (B : NodalCycleNumbering p n) (t : ZMod n) :
      (𝟙 X : X ⟶ X).IsOrientedCycleSubdivision (B.reindex (.r t)) B :=
    e.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one (B.reindex (.r t)) B
      ((congrArg cycleOrientationSign (boundaryCycleAction_reindex B (.r t))).trans
        (cycleOrientationSign_r t))
  cases g with
  | r t =>
    simpa only [cycleOrientationSign_r, ite_eq_right (by decide : (1 : ℤˣ) ≠ -1)] using
      rotation A t
  | sr t => simpa only [cycleOrientationSign_sr, ite_true, reindex] using rotation A.reverse t

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] {D : Y.IdealSheafData}
  [D.subscheme.Over (Spec (.of k))] [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  {κ : Type v} {q : κ → (D.subscheme ↘ Spec (.of k)).smoothLocus}

/-- The prime of a reindexed Cartier boundary is the original prime at the
corresponding vertex. -/
@[simp] theorem reindex_boundaryPrimeEquiv_apply (B : NodalCycleNumbering q n)
    (hD : D.IsEffectiveCartier) (g : DihedralGroup n) (j : ZMod n) :
    (B.reindex g).boundaryPrimeEquiv hD j = B.boundaryPrimeEquiv hD (cycleVertexPerm g j) := by
  apply Subtype.ext
  simp only [boundaryPrimeEquiv_apply_val, reindex_componentGenericPoint]

end AlgebraicGeometry.Scheme.NodalCycleNumbering
