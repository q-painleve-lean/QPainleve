/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Boundary.Node

/-!
# Binomial coordinates of smooth toric boundary points

A smooth closed point of a complete regular toric surface boundary lies on a ray orbit.
In its determinant character coordinate, the reduced point ideal is the internal center
with parameter minus the reciprocal of the orbit coordinate.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

variable (b : Module.Basis (Fin 2) ℤ N)

local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "χ(" ρ ")" => LinearMap.toAddMonoidHom (b.detDualEquiv (Ray.primitiveGenerator ρ))

/-- The reduced ideal of a smooth closed point of a complete regular toric boundary
is a binomial center ideal in any chosen oriented lattice basis. -/
theorem exists_internalCenter_eq_ker_fromSpecResidueField
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (p : (Φ.boundaryIdeal hc.nonempty_cones).subscheme) (hp : IsClosed ({p} : Set _))
    (hs : (((Φ.boundaryIdeal hc.nonempty_cones).subschemeι ≫
      Φ.algebraicRealizationStructureMap).stalkMap p).hom.FormallySmooth) :
    let := hc.nonempty_cones
    ∃ (ρ : Φ.Ray) (a : ℂˣ),
      (ρ.internalCenter b a).val =
        ((Φ.boundaryIdeal hc.nonempty_cones).subscheme.fromSpecResidueField p).ker := by
  let := hc.nonempty_cones
  let D := Φ.boundaryIdeal hc.nonempty_cones
  let s := D.subschemeι ≫ Φ.algebraicRealizationStructureMap
  have hnodal := Φ.atWorstNodalOfRelativeDimensionOne_boundary hΦ hc rankTwo
  have := hnodal.syntomic
  have : IsReduced D.subscheme := by
    dsimp only [D]
    rw [Φ.boundaryIdeal_def]
    infer_instance
  have hnot : ¬ D.IsNodeOfReducedBoundary Φ.algebraicRealizationStructureMap (D.subschemeι p) := by
    rw [D.isNodeOfReducedBoundary_iff_of_isReduced]
    rintro ⟨z, hz, hn⟩
    exact hn.not_formallySmooth_stalkMap ((D.subschemeι.isClosedEmbedding.injective hz).symm ▸ hs)
  obtain ⟨ρ, hρ⟩ := Φ.exists_rayChart_of_not_isNodeOfReducedBoundary hΦ hc rankTwo hnot
  have hm : χ(ρ) ρ.primitiveGenerator = 0 := b.detDualEquiv_self _
  let f := pointOfClosedPoint s p hp
  have hf : D.subschemeι (f (IsLocalRing.closedPoint ℂ)) ∈
      Set.range (Φ.affineToricChartι ρ.toCone) := by
    rw [show f (IsLocalRing.closedPoint ℂ) = p from pointOfClosedPoint_apply s p hp _]
    exact hρ
  obtain ⟨a, ha⟩ := ρ.exists_binomialCenterOnBoundary_eq_of_mem_rayChart rankTwo hm
    (ρ.surjective_detCharacter b) f (pointOfClosedPoint_comp s p hp) hf
  refine ⟨ρ, a, ?_⟩
  rw [Ray.internalCenter_val, ha, f.ker_eq_ker_fromSpecResidueField]
  exact congrArg (fun x ↦ (D.subscheme.fromSpecResidueField x).ker)
    (pointOfClosedPoint_apply s p hp (IsLocalRing.closedPoint ℂ))

end TauCeti.Toric.Fan
