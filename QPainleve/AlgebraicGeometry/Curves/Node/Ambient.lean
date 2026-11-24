/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.GenericPoint
public import QPainleve.AlgebraicGeometry.Curves.Node.Locus
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic

import QPainleve.AlgebraicGeometry.Curves.Node.BoundaryRestriction
import QPainleve.AlgebraicGeometry.Curves.Node.PointBlowup
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Numbered nodes and components in the ambient scheme

The numbering of a Cartier boundary cycle enumerates its ambient prime divisors.
Incidence at a numbered node is determined by the endpoints of its two ordered
branches, including when both branches lie on the same component.
-/

public noncomputable section

open CategoryTheory TopologicalSpace TauCeti TauCeti.AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.NodalCycleNumbering

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} {D : X.IdealSheafData}
  [D.subscheme.Over (Spec (.of k))] [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  {ι : Type v} {p : ι → (D.subscheme ↘ Spec (.of k)).smoothLocus} {n : ℕ} [NeZero n]
  (A : NodalCycleNumbering p n)

section Primes

variable [IsLocallyNoetherian X]

/-- The numbering of a nodal effective Cartier divisor enumerates the
codimension-one points of its support in the ambient scheme. -/
def boundaryPrimesEquiv (hD : D.IsEffectiveCartier) : ZMod n ≃ D.boundaryPrimes := by
  let f (j : ZMod n) : D.boundaryPrimes :=
    ⟨D.subschemeι (A.componentGenericPoint j), IdealSheafData.mem_boundaryPrimes.mpr
      ⟨D.range_subschemeι.le (Set.mem_range_self _),
        hD.coheight_subschemeι_of_coheight_eq_zero (by
          rw [A.componentGenericPoint_def]
          exact D.subscheme.coheight_blowupComponentGeneric (A.component j))⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro j l h
    exact A.componentGenericPoint_injective (D.subschemeι.injective
      (congrArg (fun a : D.boundaryPrimes ↦ a.val) h))
  · intro a
    obtain ⟨v, hv⟩ := hD.exists_subschemeι_blowupComponentGeneric_eq (k := k)
      (p := D.boundaryPrimeEmbedding a) (by
        rw [IdealSheafData.coe_boundaryPrimeEmbedding]
        exact (IdealSheafData.mem_boundaryPrimes.mp a.property).1)
    obtain ⟨j, rfl⟩ := A.component.surjective v
    exact ⟨j, Subtype.ext (by
      simpa only [f, A.componentGenericPoint_def, IdealSheafData.coe_boundaryPrimeEmbedding]
        using hv)⟩

/-- The prime at a numbered component is the ambient image of its generic point. -/
@[simp]
theorem boundaryPrimesEquiv_apply_val (hD : D.IsEffectiveCartier) (j : ZMod n) :
    (A.boundaryPrimesEquiv hD j).val = D.subschemeι (A.componentGenericPoint j) :=
  (rfl)

/-- A numbered component contains the ambient node exactly when one of its
branches has that component as endpoint. -/
theorem subschemeι_node_mem_closure_boundaryPrimesEquiv_iff (hD : D.IsEffectiveCartier)
    (i j : ZMod n) :
    D.subschemeι ((D.subscheme.singularLocus k).subschemeι (A.node i)) ∈
      closure {(A.boundaryPrimesEquiv hD j).val} ↔
    ∃ b : Fin 2, (DualGraph.cycle n).endpoint i b = j := by
  rw [boundaryPrimesEquiv_apply_val, ← Set.image_singleton,
    D.subschemeι.isClosedEmbedding.closure_image_eq]
  exact (D.subschemeι.injective.mem_set_image).trans
    (A.node_mem_closure_componentGenericPoint_iff i j)

end Primes

/-- A numbered node is a closed point of the ambient scheme. -/
theorem isClosed_singleton_subschemeι_node (i : ZMod n) :
    IsClosed ({D.subschemeι ((D.subscheme.singularLocus k).subschemeι (A.node i))} : Set X) := by
  rw [← Set.image_singleton]
  exact D.subschemeι.isClosedMap _ (D.subscheme.isClosed_singleton_of_mem_singularLocus
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
    ((D.subscheme.singularLocus k).range_subschemeι.le (Set.mem_range_self _)))

/-- The point of the ambient scheme at a numbered node satisfies the node
condition for the reduced boundary. -/
theorem isNodeOfReducedBoundary_subschemeι_node (f : X ⟶ Spec (.of k))
    (hf : D.subscheme ↘ Spec (.of k) = D.subschemeι ≫ f)
    (i : ZMod n) :
    D.IsNodeOfReducedBoundary f
      (D.subschemeι ((D.subscheme.singularLocus k).subschemeι (A.node i))) := by
  have hN := PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := D.subscheme ↘ Spec (.of k))
  have := hN.isReduced
  let z := (D.subscheme.singularLocus k).subschemeι (A.node i)
  refine (D.isNodeOfReducedBoundary_iff_of_isReduced _ _).mpr ⟨z, rfl, ?_⟩
  rw [← hf]
  exact ((D.subscheme ↘ Spec (.of k)).isNodeAt_iff_notMem_smoothLocus hN z).mpr
    ((D.subscheme.mem_support_singularLocus_iff_notMem_smoothLocus z).mp
      ((D.subscheme.singularLocus k).range_subschemeι.le (Set.mem_range_self _)))

end AlgebraicGeometry.Scheme.NodalCycleNumbering
