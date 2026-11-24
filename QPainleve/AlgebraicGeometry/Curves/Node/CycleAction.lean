/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.DualGraph.CycleAction
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Coordinates
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Isomorphism

/-!
# Isomorphisms of numbered nodal cycles

A curve isomorphism induces a dihedral symmetry between two numbered nodal cycles.
The action is read on the actual branch schemes of the conductor squares and gives
the induced permutation of the normalized components. Using the ordered branches
distinguishes the two orientations for a self-node or a pair of parallel nodes.
The numbering uses the native dual graph and its branch coordinates
`AlgebraicGeometry.Scheme.dualGraphBranchEquiv`.
-/

public noncomputable section

open CategoryTheory TopologicalSpace TauCeti
open TauCeti.AlgebraicGeometry

universe u v w z

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [PrestableFamily (X ↘ Spec (.of k))]
  {ι : Type v} {p : ι → (X ↘ Spec (.of k)).smoothLocus} {n : ℕ} [NeZero n]

/-- A numbering of the components, nodes and ordered branches of a nodal cycle.
The second branch at node `j` is on component `j + 1`. -/
structure NodalCycleNumbering (p : ι → (X ↘ Spec (.of k)).smoothLocus) (n : ℕ) [NeZero n] where
  /-- The numbering of the components. -/
  vertex : ZMod n ≃ (X.dualGraph p).Vertex
  /-- The numbering of the nodes. -/
  edge : ZMod n ≃ (X.dualGraph p).Edge
  /-- The order of the branches at each node. -/
  order : (X.dualGraph p).Edge → Equiv.Perm (Fin 2)
  /-- The ordered branches have the endpoints of the numbered cycle. -/
  endpoint_eq (j : ZMod n) (b : Fin 2) :
    (X.dualGraph p).endpoint (edge j) (order (edge j) b) =
      vertex ((DualGraph.cycle n).endpoint j b)

namespace NodalCycleNumbering

variable (C : NodalCycleNumbering p n)

/-- The numbering of the irreducible components of the normalized curve. -/
def component : ZMod n ≃ irreducibleComponents (X.singularLocus k).blowup :=
  C.vertex.trans (X.dualGraphVertexEquiv p)

/-- The component is the normalized component at the corresponding dual graph vertex. -/
theorem component_apply (j : ZMod n) : C.component j = X.dualGraphVertexEquiv p (C.vertex j) :=
  (rfl)

/-- The numbering of the points of the singular subscheme. -/
def node : ZMod n ≃ (X.singularLocus k).subscheme :=
  C.edge.trans (X.dualGraphNodeEquiv p)

/-- The numbering of the points of the branch scheme by node and ordered endpoint. -/
def branch : (ZMod n × Fin 2) ≃ X.branchScheme k :=
  ((C.edge.prodCongr (.refl _)).trans (Equiv.prodCongrRight C.order)).trans
    (X.dualGraphBranchEquiv p)

/-- The ordered branch over a numbered node agrees with the conductor branch ordering. -/
theorem branch_eq_branchOrderOfDualGraph (j : ZMod n) (b : Fin 2) :
    C.branch (j, b) = (X.branchOrderOfDualGraph p C.order (C.node j) b).val := by
  rw [node, Equiv.trans_apply, X.branchOrderOfDualGraph_apply_val p]
  rfl

/-- The projection of a numbered branch to the singular subscheme forgets the endpoint. -/
@[simp]
theorem branchSchemeToSingularLocus_branch (j : ZMod n) (b : Fin 2) :
    X.branchSchemeToSingularLocus k (C.branch (j, b)) = C.node j := by
  simp [node, branch]

/-- The normalized point of a branch belongs to the component at its numbered endpoint. -/
theorem branchSchemeToBlowup_branch_mem_component_iff (j : ZMod n) (b : Fin 2)
    (a : irreducibleComponents (X.singularLocus k).blowup) :
    X.branchSchemeToBlowup k (C.branch (j, b)) ∈ (a : Set (X.singularLocus k).blowup) ↔
      C.component ((DualGraph.cycle n).endpoint j b) = a := by
  simpa [branch, component, C.endpoint_eq] using
    (X.dualGraphVertexEquiv_endpoint_eq_iff p (C.edge j) (C.order (C.edge j) b) a).symm

/-- Reverse the orientation of the numbering, keeping component zero fixed. Node `j`
becomes the old node `-1 - j` with its two branches exchanged. -/
@[expose]
def reverse : NodalCycleNumbering p n where
  vertex := (DihedralGroup.cycleVertexPerm (.sr 0)).trans C.vertex
  edge := (Equiv.subLeft (-1 : ZMod n)).trans C.edge
  order q := Fin.revPerm.trans (C.order q)
  endpoint_eq j b := by
    have h := DihedralGroup.cycle_endpoint_cycleBranchPerm (.sr (0 : ZMod n)) j b
    simp only [DihedralGroup.cycleBranchPerm_sr_apply, neg_zero, zero_sub] at h
    simp only [Equiv.trans_apply, Equiv.subLeft_apply, Fin.revPerm_apply, C.endpoint_eq, h]

@[simp]
theorem reverse_component (j : ZMod n) : C.reverse.component j = C.component (-j) := by
  simp only [component, reverse, Equiv.trans_apply, DihedralGroup.cycleVertexPerm_sr_apply,
    neg_zero, zero_sub]

@[simp]
theorem reverse_node (j : ZMod n) : C.reverse.node j = C.node (-1 - j) :=
  (rfl)

@[simp]
theorem reverse_branch (j : ZMod n) (b : Fin 2) :
    C.reverse.branch (j, b) = C.branch (-1 - j, b.rev) :=
  (rfl)

end NodalCycleNumbering

end AlgebraicGeometry.Scheme

namespace CategoryTheory.Iso

open AlgebraicGeometry DihedralGroup
open Scheme (NodalCycleNumbering)

variable {k : Type u} [Field k] [IsSepClosed k] {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [PrestableFamily (X ↘ Spec (.of k))] [PrestableFamily (Y ↘ Spec (.of k))]
  {ι : Type v} {p : ι → (X ↘ Spec (.of k)).smoothLocus}
  {ι' : Type w} {q : ι' → (Y ↘ Spec (.of k)).smoothLocus} {n m : ℕ} [NeZero n] [NeZero m]
  (f : X ≅ Y) [f.hom.IsOver (Spec (.of k))]
  (C : NodalCycleNumbering p n)

local notation "fN" => Iso.hom (singularLocusIso (R := k) f)
local notation "fB" => Iso.hom (branchSchemeIso (R := k) f)
local notation "fV" => Iso.hom (singularLocusBlowupIso (R := k) f)
local notation "π[" Z "]" => Scheme.branchSchemeToSingularLocus k Z

omit [IsSepClosed k] in
include f in
private theorem branchSchemeIso_mem_fiber_iff (z : (X.singularLocus k).subscheme)
    (b : X.branchScheme k) : π[X] b = z ↔ π[Y] (fB b) = fN z := by
  rw [← Scheme.Hom.comp_apply, f.branchSchemeIso_hom_branchSchemeToSingularLocus,
    Scheme.Hom.comp_apply, (fN).injective.eq_iff]

private def mappedEdge : ZMod n ≃ (Y.dualGraph q).Edge :=
  (C.node.trans (fN).homeomorph.toEquiv).trans (Y.dualGraphNodeEquiv q).symm

private def mappedOrderAt (j : ZMod n) : Equiv.Perm (Fin 2) :=
  (X.branchOrderOfDualGraph p C.order (C.node j)).trans <|
    ((fB).homeomorph.toEquiv.subtypeEquiv (branchSchemeIso_mem_fiber_iff f (C.node j))).trans <|
      (Y.branchOrderOfDualGraph q (fun _ ↦ Equiv.refl _) (fN (C.node j))).symm

private def mappedOrder (a : (Y.dualGraph q).Edge) : Equiv.Perm (Fin 2) :=
  mappedOrderAt f C (q := q) ((mappedEdge f C (q := q)).symm a)

include f C in
private theorem mappedOrder_branch (j : ZMod n) (b : Fin 2) :
    Y.dualGraphBranchEquiv q
      (mappedEdge f C (q := q) j, mappedOrder f C (q := q) (mappedEdge f C (q := q) j) b) =
      fB (C.branch (j, b)) := by
  have hn : Y.dualGraphNodeEquiv q (mappedEdge f C j) = fN (C.node j) := by
    simp [mappedEdge]
  have hb := Y.branchOrderOfDualGraph_apply_val q (fun _ ↦ Equiv.refl _) (mappedEdge f C j)
    (mappedOrder f C (q := q) (mappedEdge f C (q := q) j) b)
  simp only [Equiv.refl_apply] at hb
  rw [← hb, C.branch_eq_branchOrderOfDualGraph]
  rw [hn, mappedOrder, Equiv.symm_apply_apply]
  simp only [mappedOrderAt, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

private def mappedComponent :
    irreducibleComponents (X.singularLocus k).blowup ≃
      irreducibleComponents (Y.singularLocus k).blowup :=
  (irreducibleComponentsEquivOfIsPreirreducibleFiber fV (fV).continuous (fV).isOpenMap
    (fun _ ↦ (Set.subsingleton_singleton.preimage (fV).injective).isPreirreducible)
    (fV).surjective).symm.toEquiv

/-- Transport the nodes and ordered branches of a cycle along an isomorphism over the
ground field. The target may use any marking in its native dual graph. -/
def mapNodalCycleNumbering : Scheme.NodalCycleNumbering q n where
  vertex := (C.component.trans (mappedComponent f)).trans (Y.dualGraphVertexEquiv q).symm
  edge := mappedEdge f C
  order := mappedOrder f C
  endpoint_eq j b := by
    let a := C.component ((DualGraph.cycle n).endpoint j b)
    apply (Y.dualGraphVertexEquiv q).injective
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    apply (Y.dualGraphVertexEquiv_endpoint_eq_iff q _ _ (mappedComponent f a)).mpr
    rw [← Y.branchSchemeToBlowup_dualGraphBranchEquiv, mappedOrder_branch f C,
      ← Scheme.Hom.comp_apply, f.branchSchemeIso_hom_branchSchemeToBlowup,
      Scheme.Hom.comp_apply]
    exact Set.mem_image_of_mem fV ((C.branchSchemeToBlowup_branch_mem_component_iff j b a).mpr rfl)

include f C in
/-- The component of a transported numbering is the image of the original component
under the normalization isomorphism. -/
@[simp]
theorem coe_component_mapNodalCycleNumbering (j : ZMod n) :
    ((f.mapNodalCycleNumbering C (q := q)).component j : Set _) =
      fV '' (C.component j : Set _) := by
  simp only [Scheme.NodalCycleNumbering.component, mapNodalCycleNumbering, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rfl

include f C in
/-- The node of a transported numbering is the image under the singular-locus isomorphism. -/
@[simp]
theorem node_mapNodalCycleNumbering (j : ZMod n) :
    (f.mapNodalCycleNumbering C (q := q)).node j = fN (C.node j) := by
  simp [Scheme.NodalCycleNumbering.node, mapNodalCycleNumbering, mappedEdge]

include f C in
/-- The ordered branch of a transported numbering is the image under the branch-scheme
isomorphism, with its index preserved. -/
@[simp]
theorem branch_mapNodalCycleNumbering (j : ZMod n) (b : Fin 2) :
    (f.mapNodalCycleNumbering C (q := q)).branch (j, b) = fB (C.branch (j, b)) :=
  mappedOrder_branch f C j b

include f C in
/-- Isomorphic nodal cycles have the same number of nodes. -/
theorem nodalCycleNumbering_length_eq (D : NodalCycleNumbering q m) : n = m := by
  let e := (C.node.trans (f.singularLocusIso (R := k)).schemeIsoToHomeo.toEquiv).trans D.node.symm
  simpa only [ZMod.card] using Fintype.card_congr e

private def numberedBranchEquiv {D : NodalCycleNumbering q m} :
    (ZMod n × Fin 2) ≃ (ZMod m × Fin 2) :=
  (C.branch.trans (f.branchSchemeIso (R := k)).schemeIsoToHomeo.toEquiv).trans D.branch.symm

private theorem numberedBranchEquiv_spec {D : NodalCycleNumbering q m} (j : ZMod n) (b : Fin 2) :
    D.branch (numberedBranchEquiv f C (D := D) (j, b)) =
      (f.branchSchemeIso (R := k)).hom (C.branch (j, b)) := by
  simp only [numberedBranchEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact Scheme.homeoOfIso_apply _ _

private theorem numberedBranchEquiv_fst {D : NodalCycleNumbering q m} (j : ZMod n) (b : Fin 2) :
    (numberedBranchEquiv f C (D := D) (j, b)).1 =
      D.node.symm ((f.singularLocusIso (R := k)).hom (C.node j)) := by
  apply D.node.injective
  have h := congrArg (Y.branchSchemeToSingularLocus k) (numberedBranchEquiv_spec f C (D := D) j b)
  rw [← Scheme.Hom.comp_apply, branchSchemeIso_hom_branchSchemeToSingularLocus,
    Scheme.Hom.comp_apply] at h
  cases ha : numberedBranchEquiv f C (D := D) (j, b) with
  | mk l a =>
    simpa only [ha, Equiv.apply_symm_apply, NodalCycleNumbering.branchSchemeToSingularLocus_branch]
      using h

private theorem image_component_mem_irreducibleComponents (j : ZMod n) :
    (f.singularLocusBlowupIso (R := k)).hom ''
        (C.component j : Set (X.singularLocus k).blowup) ∈
      irreducibleComponents (Y.singularLocus k).blowup := by
  exact (mappedComponent f (C.component j)).property

private theorem image_component_endpoint {D : NodalCycleNumbering q m}
    (j : ZMod n) (b : Fin 2) :
    let a := numberedBranchEquiv f C (D := D) (j, b)
    (D.component ((DualGraph.cycle m).endpoint a.1 a.2) : Set (Y.singularLocus k).blowup) =
      (f.singularLocusBlowupIso (R := k)).hom ''
        (C.component ((DualGraph.cycle n).endpoint j b) : Set (X.singularLocus k).blowup) := by
  intro a
  let V := C.component ((DualGraph.cycle n).endpoint j b)
  let A := (f.singularLocusBlowupIso (R := k)).hom
  let W : irreducibleComponents (Y.singularLocus k).blowup :=
    ⟨A '' (V : Set (X.singularLocus k).blowup),
      image_component_mem_irreducibleComponents f C _⟩
  have hV := (C.branchSchemeToBlowup_branch_mem_component_iff j b V).mpr rfl
  have hA : Y.branchSchemeToBlowup k (D.branch a) =
      A (X.branchSchemeToBlowup k (C.branch (j, b))) := by
    rw [numberedBranchEquiv_spec, ← Scheme.Hom.comp_apply,
      branchSchemeIso_hom_branchSchemeToBlowup, Scheme.Hom.comp_apply]
  have hW : Y.branchSchemeToBlowup k (D.branch a) ∈ (W : Set _) :=
    hA.symm ▸ Set.mem_image_of_mem A hV
  rcases a with ⟨l, c⟩
  exact congrArg Subtype.val ((D.branchSchemeToBlowup_branch_mem_component_iff l c W).mp hW)

variable {D : NodalCycleNumbering q n} in
/-- The map on the actual ordered branches of two numbered nodal cycles is given by a
unique dihedral element. -/
theorem existsUnique_boundaryCycleAction :
    ∃! g : DihedralGroup n, ∀ j b, D.branch (cycleBranchPerm g (j, b)) =
      (f.branchSchemeIso (R := k)).hom (C.branch (j, b)) := by
  let F := numberedBranchEquiv f C (D := D)
  let e (j : ZMod n) := D.node.symm ((f.singularLocusIso (R := k)).hom (C.node j))
  let v (j : ZMod n) := D.component.symm
    ⟨(f.singularLocusBlowupIso (R := k)).hom '' (C.component j : Set (X.singularLocus k).blowup),
      image_component_mem_irreducibleComponents f C j⟩
  have hv (j : ZMod n) (b : Fin 2) : (DualGraph.cycle n).endpoint (F (j, b)).1 (F (j, b)).2 =
      v ((DualGraph.cycle n).endpoint j b) := by
    apply D.component.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext (image_component_endpoint f C (D := D) j b)
  obtain ⟨g, hg, hu⟩ := existsUnique_cycleBranchPerm F e v (numberedBranchEquiv_fst f C) hv
  refine ⟨g, fun j b ↦ hg.symm ▸ numberedBranchEquiv_spec f C j b, ?_⟩
  intro g' h
  apply hu
  refine Equiv.ext fun ⟨j, b⟩ ↦ ?_
  exact D.branch.injective ((h j b).trans (numberedBranchEquiv_spec f C j b).symm)

variable (D : NodalCycleNumbering q n)

/-- The dihedral element induced by a curve isomorphism on the numbered boundary cycle. -/
def boundaryCycleAction : DihedralGroup n :=
  (existsUnique_boundaryCycleAction f C (D := D)).exists.choose

/-- The induced dihedral element computes the map on the actual numbered branches. -/
@[simp]
theorem branch_boundaryCycleAction (j : ZMod n) (b : Fin 2) :
    D.branch (cycleBranchPerm (f.boundaryCycleAction C D) (j, b)) =
      (f.branchSchemeIso (R := k)).hom (C.branch (j, b)) :=
  (existsUnique_boundaryCycleAction f C (D := D)).exists.choose_spec j b

/-- Transporting the numbering along an isomorphism gives identity on numbered branches. -/
@[simp]
theorem boundaryCycleAction_mapNodalCycleNumbering :
    f.boundaryCycleAction C (f.mapNodalCycleNumbering C (q := q)) = 1 := by
  refine (existsUnique_boundaryCycleAction f C).unique (branch_boundaryCycleAction _ _ _) ?_
  simp

private theorem numberedBranchEquiv_eq_cycleBranchPerm (j : ZMod n) (b : Fin 2) :
    numberedBranchEquiv f C (D := D) (j, b) =
      cycleBranchPerm (f.boundaryCycleAction C D) (j, b) :=
  D.branch.injective ((numberedBranchEquiv_spec f C j b).trans
    (branch_boundaryCycleAction f C D j b).symm)

/-- The action on the components of the normalized cycle is the vertex action
of the same dihedral element. -/
theorem component_boundaryCycleAction (j : ZMod n) :
    (D.component (cycleVertexPerm (f.boundaryCycleAction C D) j) :
        Set (Y.singularLocus k).blowup) =
      (f.singularLocusBlowupIso (R := k)).hom ''
        (C.component j : Set (X.singularLocus k).blowup) := by
  have hzero : (DualGraph.cycle n).endpoint j 0 = j := by simp [DualGraph.cycle]
  have hv := cycle_endpoint_cycleBranchPerm (f.boundaryCycleAction C D) j 0
  rw [hzero] at hv
  have hi := image_component_endpoint f C (D := D) j 0
  rw [numberedBranchEquiv_eq_cycleBranchPerm f C D, hzero] at hi
  exact (congrArg (fun t : ZMod n ↦ (D.component t : Set (Y.singularLocus k).blowup))
    hv.symm).trans hi

/-- The first coordinate of the branch action computes the induced map on nodes. -/
@[simp]
theorem node_boundaryCycleAction (j : ZMod n) (b : Fin 2) :
    D.node (cycleBranchPerm (f.boundaryCycleAction C D) (j, b)).1 =
      (f.singularLocusIso (R := k)).hom (C.node j) := by
  rw [← numberedBranchEquiv_eq_cycleBranchPerm f C D, numberedBranchEquiv_fst f C,
    Equiv.apply_symm_apply]

/-- The sign of the boundary action tells whether the isomorphism respects the
chosen orders in every branch fiber or reverses them all. -/
theorem branchOrder_boundaryCycleAction (x : (X.singularLocus k).subscheme) (b : Fin 2) :
    (f.branchSchemeIso (R := k)).hom (X.branchOrderOfDualGraph p C.order x b).val =
      (Y.branchOrderOfDualGraph q D.order ((f.singularLocusIso (R := k)).hom x)
        (if cycleOrientationSign (f.boundaryCycleAction C D) = -1 then b.rev else b)).val := by
  obtain ⟨j, rfl⟩ := C.node.surjective x
  have hn := node_boundaryCycleAction f C D j b
  have hb := cycleBranchPerm_snd (f.boundaryCycleAction C D) j b
  have ha := branch_boundaryCycleAction f C D j b
  cases h : cycleBranchPerm (f.boundaryCycleAction C D) (j, b) with
  | mk l c =>
    rw [h] at hn hb ha
    rw [← C.branch_eq_branchOrderOfDualGraph, ← hn, ← hb, ← D.branch_eq_branchOrderOfDualGraph]
    exact ha.symm

local instance : (Iso.refl X).hom.IsOver (Spec (.of k)) := by
  rw [Iso.refl_hom]
  infer_instance

/-- The identity isomorphism induces the identity dihedral element. -/
@[simp]
theorem boundaryCycleAction_refl :
    (Iso.refl X).boundaryCycleAction C C = 1 := by
  refine (existsUnique_boundaryCycleAction (Iso.refl X) C (D := C)).unique
    (branch_boundaryCycleAction _ _ _) fun j b ↦ ?_
  simp

/-- The identity of the underlying curve induces the reflection fixing component zero
when its target is numbered in the opposite orientation. -/
@[simp]
theorem boundaryCycleAction_refl_reverse :
    (Iso.refl X).boundaryCycleAction C C.reverse = .sr 0 := by
  refine (existsUnique_boundaryCycleAction (Iso.refl X) C (D := C.reverse)).unique
    (branch_boundaryCycleAction _ _ _) fun j b ↦ ?_
  have hj : -1 - (-1 - j) = j := by abel
  simp [hj]

variable [Z.Over (Spec (.of k))] [PrestableFamily (Z ↘ Spec (.of k))]
  {ι'' : Type z} {r : ι'' → (Z ↘ Spec (.of k)).smoothLocus}
  (g : Y ≅ Z) [g.hom.IsOver (Spec (.of k))] (E : NodalCycleNumbering r n)

local instance : (f ≪≫ g).hom.IsOver (Spec (.of k)) := by
  rw [Iso.trans_hom]
  infer_instance

/-- Dihedral actions compose in the same order as the underlying point maps. -/
theorem boundaryCycleAction_trans :
    (f ≪≫ g).boundaryCycleAction C E = g.boundaryCycleAction D E * f.boundaryCycleAction C D := by
  refine (existsUnique_boundaryCycleAction (f ≪≫ g) C (D := E)).unique
    (branch_boundaryCycleAction _ _ _) fun j b ↦ ?_
  rw [map_mul, Equiv.Perm.mul_apply]
  cases h : cycleBranchPerm (f.boundaryCycleAction C D) (j, b) with
  | mk l c =>
    simp only [branch_boundaryCycleAction, branchSchemeIso_trans, Iso.trans_hom,
      Scheme.Hom.comp_apply]
    rw [← h, branch_boundaryCycleAction]

local instance : f.symm.hom.IsOver (Spec (.of k)) :=
  ⟨by rw [Iso.symm_hom, ← comp_over f.hom (Spec (.of k)), f.inv_hom_id_assoc]⟩

/-- The action of an inverse isomorphism is the inverse dihedral element. -/
@[simp]
theorem boundaryCycleAction_symm :
    f.symm.boundaryCycleAction D C = (f.boundaryCycleAction C D)⁻¹ := by
  have h := boundaryCycleAction_trans f C D f.symm C
  simp only [Iso.self_symm_id, boundaryCycleAction_refl] at h
  exact eq_inv_of_mul_eq_one_left h.symm

end CategoryTheory.Iso
