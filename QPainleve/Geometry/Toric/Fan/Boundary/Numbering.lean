/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Reindex
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

universe u

variable (k : Type u) [Field k] [IsSepClosed k] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]

local notation "D[" Φ "]" => Fan.toricBoundaryIdeal k Φ inferInstance
local notation "C[" Φ "]" => Scheme.IdealSheafData.subscheme D[Φ]
local notation "S" => Spec (CommRingCat.of k)

variable [PrestableFamily ((Φ.toricBoundaryIdeal k inferInstance).subscheme ↘ Spec (.of k))]
  {ι : Type*}
  {p : ι → ((Φ.toricBoundaryIdeal k inferInstance).subscheme ↘ Spec (.of k)).smoothLocus}
  {n : ℕ} [NeZero n]

variable (Φ) in
/-- Read each numbered normalized component of the toric boundary as a ray. -/
def rayEquivOfNodalCycleNumbering (hΦ : Φ.IsRegular)
    (A : NodalCycleNumbering (k := k) (X := C[Φ]) p n) :
    ZMod n ≃ Φ.Ray :=
  A.component.trans (Φ.boundaryNormalizationComponentEquiv k hΦ).symm

/-- The ray read from a numbered component has that component as its normalization. -/
@[simp]
theorem boundaryNormalizationComponentEquiv_rayEquivOfNodalCycleNumbering
    (hΦ : Φ.IsRegular) (A : NodalCycleNumbering (k := k) (X := C[Φ]) p n)
    (j : ZMod n) :
    Φ.boundaryNormalizationComponentEquiv k hΦ (Φ.rayEquivOfNodalCycleNumbering k hΦ A j) =
      A.component j :=
  Equiv.apply_symm_apply _ _

/-- Rotating the boundary numbering translates the ray labels by the same offset. -/
@[simp]
theorem rayEquivOfNodalCycleNumbering_rotate_apply
    (hΦ : Φ.IsRegular) (A : NodalCycleNumbering (k := k) (X := C[Φ]) p n)
    (origin j : ZMod n) :
    Φ.rayEquivOfNodalCycleNumbering k hΦ (A.rotate origin) j =
      Φ.rayEquivOfNodalCycleNumbering k hΦ A (j + origin) := by
  apply (Φ.boundaryNormalizationComponentEquiv k hΦ).injective
  simp

variable (Φ) in
/-- Enumerate the rays in boundary order by finite offsets from the component at `origin`. -/
def rayFinEquivOfNodalCycleNumbering (hΦ : Φ.IsRegular)
    (A : NodalCycleNumbering (k := k) (X := C[Φ]) p n)
    (origin : ZMod n) : Fin n ≃ Φ.Ray :=
  (ZMod.finEquiv n).toEquiv.trans (Φ.rayEquivOfNodalCycleNumbering k hΦ (A.rotate origin))

/-- A finite offset reads the ray of the rotated cycle at the corresponding cyclic index. -/
@[simp]
theorem rayFinEquivOfNodalCycleNumbering_apply
    (hΦ : Φ.IsRegular) (A : NodalCycleNumbering (k := k) (X := C[Φ]) p n)
    (origin : ZMod n) (j : Fin n) :
    Φ.rayFinEquivOfNodalCycleNumbering k hΦ A origin j =
      Φ.rayEquivOfNodalCycleNumbering k hΦ (A.rotate origin) (ZMod.finEquiv n j) :=
  (rfl)

/-- The offset of a ray is the finite representative of its cyclic index minus the origin. -/
@[simp]
theorem rayFinEquivOfNodalCycleNumbering_symm_apply
    (hΦ : Φ.IsRegular) (A : NodalCycleNumbering (k := k) (X := C[Φ]) p n)
    (origin : ZMod n) (ρ : Φ.Ray) :
    (Φ.rayFinEquivOfNodalCycleNumbering k hΦ A origin).symm ρ =
      (ZMod.finEquiv n).symm ((Φ.rayEquivOfNodalCycleNumbering k hΦ A).symm ρ - origin) := by
  apply (Φ.rayFinEquivOfNodalCycleNumbering k hΦ A origin).injective
  simp

variable (Φ) in
/-- Every numbering of the reduced boundary of a complete regular rank-two fan
determines a numbering of its rays. With the original basis or its transposition,
successive rays have determinant one. The common two-ray cone represents the
actual numbered node, and the ray order agrees with the numbered branch endpoints. -/
theorem exists_positive_ray_numbering_of_nodalCycleNumbering
    (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (A : NodalCycleNumbering (k := k) (X := C[Φ]) p n) :
    let u := Φ.rayEquivOfNodalCycleNumbering k hΦ A
    ∃ b' : Basis (Fin 2) ℤ N,
      (b' = b ∨ b' = b.reindex (Equiv.swap 0 1)) ∧
      (∀ j, b'.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1) ∧
      ∀ j, ∃ σ : {σ : Φ.cones // Nat.card (ToricRay σ.val) = 2},
        (u j).toCone ≤ σ.val ∧ (u (j + 1)).toCone ≤ σ.val ∧
        (D[Φ]).subschemeι ((C[Φ]).dualGraphEdgeEquiv p (A.edge j)).val =
          Φ.distinguishedSection (R := k) σ.val (IsLocalRing.closedPoint k) := by
  intro u
  let v := Φ.boundaryNormalizationComponentEquiv k hΦ
  have hu (j : ZMod n) : A.component j = v (u j) :=
    (boundaryNormalizationComponentEquiv_rayEquivOfNodalCycleNumbering k hΦ A j).symm
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
    Φ.exists_toric_boundary_dualGraph_cycle k hΦ hc p b r hr
  let B : NodalCycleNumbering (k := k) (X := C[Φ]) p n := ⟨w, e, o, hw⟩
  have hB (j : ZMod n) : B.component j = v (r j) := by
    rw [B.component_apply]
    exact hcomp j
  have h₀ : A.vertex 0 = B.vertex 0 := by
    apply ((C[Φ]).dualGraphVertexEquiv p).injective
    rw [← A.component_apply, ← B.component_apply, hu]
    exact (congrArg v hr₀).symm.trans (hB 0).symm
  obtain ⟨g, hg, hAg, hEg⟩ := A.exists_dihedral_of_same_initial_vertex B h₀
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
