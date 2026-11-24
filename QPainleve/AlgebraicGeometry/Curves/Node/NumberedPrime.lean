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
# Ambient primes of numbered nodal cycles

The component numbering of a nodal Cartier boundary numbers its ambient prime
divisors. The incidence of each numbered node is read from its two ordered
branches, including when both branches lie on the same component.
-/

public noncomputable section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u v

namespace AlgebraicGeometry.Scheme.NodalCycleNumbering

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} {D : X.IdealSheafData}
  [D.subscheme.Over (Spec (.of k))] [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  {ι : Type v} {p : ι → (D.subscheme ↘ Spec (.of k)).smoothLocus} {n : ℕ} [NeZero n]

local notation "C" => D.subscheme
local notation "J" => Scheme.singularLocus k C

variable (A : NodalCycleNumbering p n)

/-- The point of the ambient scheme at the specified node of the boundary cycle. -/
def ambientNode (j : ZMod n) : X := D.subschemeι ((J).subschemeι (A.node j))

/-- The ambient image of the corresponding point of the singular subscheme. -/
theorem ambientNode_def (j : ZMod n) :
    A.ambientNode j = D.subschemeι ((J).subschemeι (A.node j)) := (rfl)

/-- A numbered node is a closed point of the ambient scheme. -/
theorem isClosed_ambientNode (j : ZMod n) : IsClosed ({A.ambientNode j} : Set X) := by
  rw [ambientNode_def, ← Set.image_singleton]
  exact (D.subschemeι).isClosedMap _ ((C).isClosed_singleton_of_mem_singularLocus
    PrestableFamily.atWorstNodalOfRelativeDimensionOne ((J).range_subschemeι.le ⟨_, rfl⟩))

/-- The numbered point is a node of the reduced boundary in the ambient scheme. -/
theorem isNodeOfReducedBoundary_ambientNode [X.Over (Spec (.of k))] (j : ZMod n)
    (hOver : C ↘ Spec (.of k) = D.subschemeι ≫ X ↘ Spec (.of k)) :
    D.IsNodeOfReducedBoundary (X ↘ Spec (.of k)) (A.ambientNode j) := by
  have hn : AtWorstNodalOfRelativeDimensionOne (C ↘ Spec (.of k)) :=
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have := hn.isReduced
  have := hn.syntomic
  apply (D.isNodeOfReducedBoundary_iff_of_isReduced _ _).mpr
  refine ⟨(J).subschemeι (A.node j), A.ambientNode_def j |>.symm, ?_⟩
  rw [← hOver]
  exact ((C ↘ Spec (.of k)).isNodeAt_iff_notMem_smoothLocus hn _).mpr
    (((C).mem_support_singularLocus_iff_notMem_smoothLocus _).mp
      ((J).range_subschemeι.le ⟨_, rfl⟩))

variable [IsLocallyNoetherian X]

/-- The numbered normalized components give exactly the prime divisors of a Cartier boundary. -/
def boundaryPrimeEquiv (hD : D.IsEffectiveCartier) : ZMod n ≃ D.boundaryPrimes := by
  let f : ZMod n → D.boundaryPrimes := fun j ↦
    ⟨D.subschemeι (A.componentGenericPoint j), mem_boundaryPrimes.mpr
      ⟨D.range_subschemeι.le ⟨_, rfl⟩, hD.coheight_subschemeι_of_coheight_eq_zero
        (by rw [componentGenericPoint_def]; exact
          (C).coheight_blowupComponentGeneric (A.component j))⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b h
    exact A.componentGenericPoint_injective
      ((D.subschemeι).injective (congrArg (fun q : D.boundaryPrimes ↦ q.val) h))
  · intro q
    obtain ⟨v, hv⟩ := hD.exists_subschemeι_blowupComponentGeneric_eq (k := k)
      (p := D.boundaryPrimeEmbedding q) (by
        simpa only [coe_boundaryPrimeEmbedding] using (mem_boundaryPrimes.mp q.property).1)
    obtain ⟨j, rfl⟩ := A.component.surjective v
    exact ⟨j, Subtype.ext (by
      simpa only [f, componentGenericPoint_def, coe_boundaryPrimeEmbedding] using hv)⟩

/-- The ambient prime is the image of the numbered component's generic point. -/
@[simp]
theorem boundaryPrimeEquiv_apply_val (hD : D.IsEffectiveCartier) (j : ZMod n) :
    (A.boundaryPrimeEquiv hD j).val = D.subschemeι (A.componentGenericPoint j) := (rfl)

/-- The components through node `j` are the endpoints of its two ordered branches. -/
theorem ambientNode_mem_closure_boundaryPrime_iff (hD : D.IsEffectiveCartier) (j l : ZMod n) :
    A.ambientNode j ∈ closure {(A.boundaryPrimeEquiv hD l).val} ↔
      ∃ b : Fin 2, (TauCeti.DualGraph.cycle n).endpoint j b = l := by
  rw [ambientNode_def, boundaryPrimeEquiv_apply_val, ← Set.image_singleton,
    D.subschemeι.isClosedEmbedding.closure_image_eq]
  exact (D.subschemeι.injective.mem_set_image).trans
    (A.node_mem_closure_componentGenericPoint_iff j l)

end AlgebraicGeometry.Scheme.NodalCycleNumbering
