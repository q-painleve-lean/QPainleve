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

Reindexing a numbered cycle precomposes its vertex and branch labels with the same
dihedral symmetry. The order of the two branches over an actual node depends only on
the sign. Thus an oriented subdivision can be retargeted from a reindexed numbering
to the original numbering or its reversal.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory DihedralGroup TauCeti TauCeti.AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Scheme.NodalCycleNumbering

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [PrestableFamily (X ↘ Spec (.of k))]
  {ι : Type v} {p : ι → (X ↘ Spec (.of k)).smoothLocus} {n : ℕ} [NeZero n]
  (A : NodalCycleNumbering p n)

/-- Start the cycle at the old component `a`, keeping its branch orientation. -/
def rotate (a : ZMod n) : NodalCycleNumbering p n where
  vertex := (Equiv.addRight a).trans A.vertex
  edge := (Equiv.addRight a).trans A.edge
  order := A.order
  endpoint_eq j b := by
    simpa only [Equiv.trans_apply, Equiv.coe_addRight, cycleBranchPerm_r_apply,
      cycleVertexPerm_r_apply, A.endpoint_eq] using
      congrArg A.vertex (cycle_endpoint_cycleBranchPerm (.r a) j b)

/-- Precompose the numbering with a dihedral symmetry of the labelled cycle. -/
def reindex : DihedralGroup n → NodalCycleNumbering p n
  | .r a => A.rotate a
  | .sr a => (A.rotate (-a)).reverse

@[simp]
theorem reindex_r (a : ZMod n) : A.reindex (.r a) = A.rotate a := (rfl)

@[simp]
theorem reindex_sr (a : ZMod n) : A.reindex (.sr a) = (A.rotate (-a)).reverse := (rfl)

@[simp]
theorem rotate_component (a j : ZMod n) : (A.rotate a).component j = A.component (j + a) := by
  rw [component_apply, component_apply]
  rfl

@[simp]
theorem rotate_node (a j : ZMod n) : (A.rotate a).node j = A.node (j + a) := by
  rw [node_apply, node_apply]
  rfl

@[simp]
theorem rotate_branch (a j : ZMod n) (b : Fin 2) :
    (A.rotate a).branch (j, b) = A.branch (j + a, b) := by
  rw [branch_eq_branchOrderOfDualGraph, branch_eq_branchOrderOfDualGraph, rotate_node]
  rfl

/-- Agreement on all numbered branches determines the vertex, node and branch labels. -/
@[ext]
theorem ext {A B : NodalCycleNumbering p n}
    (h : ∀ j b, A.branch (j, b) = B.branch (j, b)) : A = B := by
  have flag (C : NodalCycleNumbering p n) (j : ZMod n) (b : Fin 2) :
      C.branch (j, b) = X.dualGraphBranchEquiv p (C.edge j, C.order (C.edge j) b) := by
    rw [C.branch_eq_branchOrderOfDualGraph]
    -- Evaluate the node before applying the dependent branch ordering.
    exact (congrArg (fun z ↦ (X.branchOrderOfDualGraph p C.order z b).val)
      (C.node_apply j)).trans (X.branchOrderOfDualGraph_apply_val p C.order (C.edge j) b)
  have flags (j : ZMod n) (b : Fin 2) :
      (A.edge j, A.order (A.edge j) b) = (B.edge j, B.order (B.edge j) b) :=
    (X.dualGraphBranchEquiv p).injective (by simpa only [flag] using h j b)
  have he : A.edge = B.edge := Equiv.ext fun j ↦ congrArg Prod.fst (flags j 0)
  have ho : A.order = B.order := funext fun e ↦ Equiv.ext fun b ↦ by
    obtain ⟨j, rfl⟩ := A.edge.surjective e
    simpa only [← he] using congrArg Prod.snd (flags j b)
  have hv : A.vertex = B.vertex := Equiv.ext fun j ↦ by
    have hA := A.endpoint_eq j 0
    have hB := B.endpoint_eq j 0
    rw [← he, ← ho] at hB
    simpa only [DualGraph.cycle, reduceIte] using hA.symm.trans hB
  cases A
  cases B
  cases he
  cases ho
  cases hv
  rfl

/-- The old index of a component is its image under the vertex permutation. -/
@[simp]
theorem reindex_component (g : DihedralGroup n) (j : ZMod n) :
    (A.reindex g).component j = A.component (cycleVertexPerm g j) := by
  cases g <;> simp [sub_eq_add_neg, add_comm]

/-- The old index of an ordered branch is its image under the branch permutation. -/
@[simp]
theorem reindex_branch (g : DihedralGroup n) (j : ZMod n) (b : Fin 2) :
    (A.reindex g).branch (j, b) = A.branch (cycleBranchPerm g (j, b)) := by
  cases g <;> simp
  abel

@[simp]
theorem reindex_one : A.reindex 1 = A := by
  apply ext
  simp

/-- Successive reindexings compose in the order of precomposition. -/
theorem reindex_reindex (g h : DihedralGroup n) :
    (A.reindex g).reindex h = A.reindex (g * h) := by
  apply ext
  intro j b
  simp only [map_mul, Equiv.Perm.mul_apply, reindex_branch]
  let a := cycleBranchPerm h (j, b)
  exact A.reindex_branch g a.1 a.2

/-- The new node label is obtained by forgetting the branch of the relabelled flag. -/
@[simp]
theorem reindex_node (g : DihedralGroup n) (j : ZMod n) :
    (A.reindex g).node j = A.node (cycleBranchPerm g (j, 0)).1 := by
  rw [← (A.reindex g).branchSchemeToSingularLocus_branch j 0, reindex_branch]
  exact A.branchSchemeToSingularLocus_branch _ _

/-- Rotations preserve the order at every actual node. Reflections exchange the branches. -/
theorem reindex_order (g : DihedralGroup n) :
    (A.reindex g).order = (if cycleOrientationSign g = -1 then A.reverse else A).order := by
  cases g <;> simp only [reindex_r, reindex_sr, cycleOrientationSign_r, cycleOrientationSign_sr,
    (by decide : (1 : ℤˣ) ≠ -1), ite_false, ite_true] <;> rfl

/-- The generic point of a reindexed component is the generic point at its old index. -/
@[simp]
theorem reindex_componentGenericPoint (g : DihedralGroup n) (j : ZMod n) :
    (A.reindex g).componentGenericPoint j = A.componentGenericPoint (cycleVertexPerm g j) := by
  simp only [componentGenericPoint_def, reindex_component]

/-- The component reindexing also describes the ambient prime divisors. -/
@[simp]
theorem reindex_boundaryPrimeEquiv {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {D : Y.IdealSheafData} [D.subscheme.Over (Spec (.of k))]
    [PrestableFamily (D.subscheme ↘ Spec (.of k))]
    {ι' : Type w} {p' : ι' → (D.subscheme ↘ Spec (.of k)).smoothLocus}
    (C : NodalCycleNumbering p' n) (hD : D.IsEffectiveCartier) (g : DihedralGroup n) (j : ZMod n) :
    (C.reindex g).boundaryPrimeEquiv hD j = C.boundaryPrimeEquiv hD (cycleVertexPerm g j) := by
  apply Subtype.ext
  simp only [boundaryPrimeEquiv_apply_val, reindex_componentGenericPoint]

local instance : (Iso.refl X).hom.IsOver (Spec (.of k)) := by
  rw [Iso.refl_hom]
  infer_instance

/-- Reindexing the source of the identity induces precisely the chosen dihedral action
on the labelled branches. -/
@[simp]
theorem boundaryCycleAction_refl_reindex (g : DihedralGroup n) :
    (Iso.refl X).boundaryCycleAction (A.reindex g) A = g := by
  refine (Iso.existsUnique_boundaryCycleAction (Iso.refl X) (A.reindex g)).unique
    (Iso.branch_boundaryCycleAction _ _ _) ?_
  simp

end AlgebraicGeometry.Scheme.NodalCycleNumbering

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] [IsSepClosed k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [PrestableFamily (X ↘ Spec (.of k))] [PrestableFamily (Y ↘ Spec (.of k))]
  {ι : Type v} {κ : Type w}
  {p : ι → (X ↘ Spec (.of k)).smoothLocus} {q : κ → (Y ↘ Spec (.of k)).smoothLocus}
  {n m : ℕ} [NeZero n] [NeZero m]

/-- Retargeting a subdivision uses the original target numbering for a rotation and
the reversed target numbering for a reflection. The normalization lift and retained
nodes are unchanged. -/
theorem isOrientedCycleSubdivision_reindex_target_iff {f : X ⟶ Y}
    {A : NodalCycleNumbering p n} {C : NodalCycleNumbering q m} (g : DihedralGroup m) :
    f.IsOrientedCycleSubdivision A (C.reindex g) ↔
      f.IsOrientedCycleSubdivision A (if cycleOrientationSign g = -1 then C.reverse else C) := by
  constructor <;> rintro ⟨fν, hν, hnodes, keep, hkeep, hcollapse⟩
  · exact ⟨fν, hν, hnodes, keep, C.reindex_order g ▸ hkeep, hcollapse⟩
  · exact ⟨fν, hν, hnodes, keep, (C.reindex_order g).symm ▸ hkeep, hcollapse⟩

end AlgebraicGeometry.Scheme.Hom
