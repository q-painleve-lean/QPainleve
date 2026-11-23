/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
public import TauCeti.AlgebraicGeometry.Scheme.LocalDimension
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic

/-!
# Dimension of curves on surfaces

On an irreducible surface locally of finite type over a field, the generic point of a
closed integral curve has codimension one, and the reduced closure of a codimension-one
point has dimension one.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The generic point of a closed integral curve on an irreducible surface of finite type
over a field maps to a point of codimension one. -/
public theorem coheight_apply_genericPoint_eq_one_of_dim_eq_two
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C]
    (k : Type u) [Field k] [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [IrreducibleSpace X] (hX : topologicalKrullDim X = 2)
    (hC : topologicalKrullDim C = 1) : Order.coheight (i (genericPoint C)) = 1 := by
  have hdim := coheight_add_height_eq_topologicalKrullDim k (i (genericPoint C))
  rw [i.height_apply_eq_height, height_eq_topologicalKrullDim_closure_singleton,
    (genericPoint_spec C).def, (Homeomorph.Set.univ C).isHomeomorph.topologicalKrullDim_eq,
    hC, hX] at hdim
  apply ENat.add_left_injective_of_ne_top (n := 1) (by simp)
  exact WithBot.coe_injective (by
    simpa only [WithBot.coe_add, WithBot.coe_one] using hdim.trans
      (by decide : (2 : WithBot ℕ∞) = 1 + 1))

end AlgebraicGeometry.Scheme.Hom

namespace QPainleve

open Scheme.IdealSheafData

/-- The reduced closure of a codimension-one point on an irreducible surface of finite type
over a field is a curve. -/
public theorem topologicalKrullDim_vanishingIdeal_subscheme
    (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IrreducibleSpace X]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (hX : topologicalKrullDim X = 2)
    (p : CodimensionOnePoint X) :
    topologicalKrullDim
      (vanishingIdeal ⟨closure {(p : X)}, isClosed_closure⟩).subscheme = 1 := by
  let I := vanishingIdeal (X := X) ⟨closure {(p : X)}, isClosed_closure⟩
  have hrange : Set.range I.subschemeι = closure {(p : X)} := by
    rw [I.range_subschemeι, coe_support_vanishingIdeal, Closeds.coe_mk]
  have hdim := coheight_add_height_eq_topologicalKrullDim k (p : X)
  rw [p.property, hX] at hdim
  have hheight : Order.height (p : X) = 1 := by
    apply ENat.add_right_injective_of_ne_top (n := 1) (by simp)
    exact WithBot.coe_injective (by
      simpa only [WithBot.coe_add, WithBot.coe_one] using hdim.trans
        (by decide : (2 : WithBot ℕ∞) = 1 + 1))
  rw [← topologicalKrullDim_range_of_isPreimmersion I.subschemeι, hrange,
    ← height_eq_topologicalKrullDim_closure_singleton, hheight]
  rfl

end QPainleve
