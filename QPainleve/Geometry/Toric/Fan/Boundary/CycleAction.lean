/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.GenericPoint
public import QPainleve.AlgebraicGeometry.Curves.Node.Period.Orientation
public import QPainleve.Geometry.Toric.Fan.Boundary.Orientation

/-!
# The boundary cycle action of a fan equivalence

In positive cyclic numberings, the orientation of a toric boundary isomorphism is
the sign of the determinant of its lattice map. Its action on components is the
map of rays. For a comparison on oriented nodal refinements, the sign descends
and a surviving ray computes the image of its component on the original boundary.

The branch comparison uses `FanEquiv.branchSchemeIso_branchOrderOfDualGraph`.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Module TauCeti.AlgebraicGeometry
open Scheme (NodalCycleNumbering)

namespace TauCeti.Toric.FanEquiv

universe u

variable (K : Type u) [Field K] [IsSepClosed K]

variable {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'} (e : FanEquiv Φ Ψ)
  [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]
  (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)

local notation "S" => Spec (CommRingCat.of K)
local notation "C[" Φ "]" =>
  Scheme.IdealSheafData.subscheme (Fan.toricBoundaryIdeal K Φ inferInstance)
local notation "g" => e.boundaryIso K hΦ₀ hΨ₀

variable [PrestableFamily ((Φ.toricBoundaryIdeal K hΦ₀).subscheme ↘ Spec (.of K))]
  [PrestableFamily ((Ψ.toricBoundaryIdeal K hΨ₀).subscheme ↘ Spec (.of K))]
  {m : ℕ} [NeZero m] {ι ι' : Type*}
  {p : ι → ((Φ.toricBoundaryIdeal K hΦ₀).subscheme ↘ Spec (.of K)).smoothLocus}
  {q : ι' → ((Ψ.toricBoundaryIdeal K hΨ₀).subscheme ↘ Spec (.of K)).smoothLocus}
  (A : NodalCycleNumbering (k := K) (X := (Φ.toricBoundaryIdeal K hΦ₀).subscheme) p m)
  (B : NodalCycleNumbering (k := K) (X := (Ψ.toricBoundaryIdeal K hΨ₀).subscheme) q m)
  {u : ZMod m ≃ Φ.Ray} {v : ZMod m ≃ Ψ.Ray}
  (hu : ∀ j, A.component j = Φ.boundaryNormalizationComponentEquiv K hΦ (u j))
  (hv : ∀ j, B.component j = Ψ.boundaryNormalizationComponentEquiv K hΨ (v j))

include hu hv in
/-- The component permutation of the toric boundary isomorphism is its map on rays. -/
theorem boundaryIso_cycleVertexPerm (j : ZMod m) :
    v (cycleVertexPerm ((g).boundaryCycleAction A B) j) = e.rayEquiv (u j) := by
  have h := (g).component_boundaryCycleAction A B j
  rw [hu, hv, e.image_singularLocusBlowupIso_boundaryNormalizationComponent K hΦ hΨ] at h
  exact (Ψ.boundaryNormalizationComponentEquiv K hΨ).injective (Subtype.ext h)

variable (b : Basis (Fin 2) ℤ N) (b' : Basis (Fin 2) ℤ N')
  (hpos : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1)
  (hpos' : ∀ j, b'.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1)
  (swap : Bool)
  (hdet : ∀ x y, b'.detDualEquiv (e.latticeEquiv x) (e.latticeEquiv y) =
    if swap then -b.detDualEquiv x y else b.detDualEquiv x y)

include hu hv hpos hpos' hdet in
/-- Relative to positive ray numberings, a toric boundary isomorphism reverses the
ordered branches exactly when the lattice equivalence negates the determinant. -/
theorem cycleOrientationSign_boundaryIso :
    cycleOrientationSign ((g).boundaryCycleAction A B) = if swap then -1 else 1 := by
  let z := A.node 0
  have h := ((g).branchOrder_boundaryCycleAction A B z 0).symm.trans
    (e.branchSchemeIso_branchOrderOfDualGraph K hΦ hΨ A.endpoint_eq B.endpoint_eq
      (by simpa only [NodalCycleNumbering.component_apply] using hu)
      (by simpa only [NodalCycleNumbering.component_apply] using hv) b b' hpos hpos' swap hdet z 0)
  have he := ((C[Ψ]).branchOrderOfDualGraph q B.order
    ((Iso.singularLocusIso (R := K) g).hom z)).injective (Subtype.ext h)
  rcases Int.units_eq_one_or (cycleOrientationSign ((g).boundaryCycleAction A B)) with h₁ | h₁
  all_goals
    cases swap <;> simp_all only [Bool.false_eq_true, ↓reduceIte,
      show (1 : ℤˣ) ≠ -1 by decide, show (0 : Fin 2).rev ≠ 0 by decide,
      show (0 : Fin 2) ≠ (0 : Fin 2).rev by decide]

include hu hv hpos hpos' hdet in
/-- The full dihedral action is determined by the lattice orientation and the image
of ray zero. The reflection index uses the convention `sr a` sends `j` to `-a - j`. -/
theorem boundaryIso_boundaryCycleAction :
    let j := v.symm (e.rayEquiv (u 0))
    (g).boundaryCycleAction A B = if swap then sr (-j) else r j := by
  intro j
  have hsign := e.cycleOrientationSign_boundaryIso K hΦ hΨ A B hu hv b b' hpos hpos' swap hdet
  have hzero : cycleVertexPerm ((g).boundaryCycleAction A B) 0 = j :=
    v.eq_symm_apply.mpr (e.boundaryIso_cycleVertexPerm K hΦ hΨ A B hu hv 0)
  cases swap with
  | false => exact (eq_r_iff_cycleVertexPerm_zero_eq hsign).mpr hzero
  | true =>
    rcases h : (g).boundaryCycleAction A B with l | l
    · simp [h] at hsign
    · simp only [h, cycleVertexPerm_sr_apply, sub_zero] at hzero
      simpa only [↓reduceIte, neg_neg] using congrArg sr (congrArg Neg.neg hzero)

variable {X Y : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
  [PrestableFamily (X ↘ Spec (.of K))] [PrestableFamily (Y ↘ Spec (.of K))]
  {n : ℕ} [NeZero n] {α β : Type*}
  {pX : α → (X ↘ Spec (.of K)).smoothLocus} {pY : β → (Y ↘ Spec (.of K)).smoothLocus}

include hu hv in
/-- In a commuting boundary comparison, the image of a component represented by a
surviving source ray is computed by projecting the image ray to the target boundary.
The hypothesis identifies the source component by its generic point. -/
theorem cycleVertexPerm_eq_iff_of_boundaryIso_descends
    (D : NodalCycleNumbering (k := K) (X := X) pX n)
    (E : NodalCycleNumbering (k := K) (X := Y) pY n)
    (d : X ≅ Y) [d.hom.IsOver S] {f : C[Φ] ⟶ X} {f' : C[Ψ] ⟶ Y}
    (h : CommSq (g).hom f f' d.hom) (a : ZMod m) (j l : ZMod n)
    (ha : f (A.componentGenericPoint a) = D.componentGenericPoint j) :
    cycleVertexPerm (d.boundaryCycleAction D E) j = l ↔
      f' (B.componentGenericPoint (v.symm (e.rayEquiv (u a)))) = E.componentGenericPoint l := by
  have hvertex : v.symm (e.rayEquiv (u a)) = cycleVertexPerm ((g).boundaryCycleAction A B) a :=
    (v.eq_symm_apply.mpr (e.boundaryIso_cycleVertexPerm K hΦ hΨ A B hu hv a)).symm
  have hpoint := congrArg (fun t : C[Φ] ⟶ Y ↦ t (A.componentGenericPoint a)) h.w
  simp only [Scheme.Hom.comp_apply, ha, (g).apply_componentGenericPoint A B,
    d.apply_componentGenericPoint D E] at hpoint
  rw [hvertex, hpoint, E.componentGenericPoint_injective.eq_iff]

variable [IsAlgClosed K] in
include hu hv hpos hpos' hdet in
/-- When the boundary comparison is made on toric refinements of two numbered cycles,
the lattice orientation determines the order of the branches of the descended
isomorphism, including on self-nodes and cycles with two components. -/
theorem cycleOrientationSign_of_boundaryIso_descends
    (D : NodalCycleNumbering (k := K) (X := X) pX n)
    (E : NodalCycleNumbering (k := K) (X := Y) pY n)
    (d : X ≅ Y) [d.hom.IsOver S]
    {f : C[Φ] ⟶ X} {f' : C[Ψ] ⟶ Y} [f.IsOver S] [f'.IsOver S]
    (hf : f.IsOrientedCycleSubdivision A D) (hf' : f'.IsOrientedCycleSubdivision B E)
    (h : CommSq (g).hom f f' d.hom) :
    cycleOrientationSign (d.boundaryCycleAction D E) = if swap then -1 else 1 :=
  (d.cycleOrientationSign_eq_of_orientedCycleSubdivisions D E A B g hf hf' h).trans
    (e.cycleOrientationSign_boundaryIso K hΦ hΨ A B hu hv b b' hpos hpos' swap hdet)

end TauCeti.Toric.FanEquiv
