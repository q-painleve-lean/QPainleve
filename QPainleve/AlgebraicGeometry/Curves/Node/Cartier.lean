/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Relative
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.PureDimension
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.PureRelativeDimension
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Nodal curves on smooth surfaces

A closed nodal curve of finite type on a smooth integral surface is an effective Cartier divisor
with its given scheme structure. In particular its ideal defines the boundary line bundle,
also when the curve has several components or a self-node.
-/

public section

open CategoryTheory TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A closed nodal curve of finite type on a smooth integral surface is effective Cartier. -/
theorem isEffectiveCartier_ker_of_atWorstNodalOfRelativeDimensionOne
    {k : Type u} [Field k] {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    [CompactSpace C] [IsIntegral X] [X.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    (hC : AtWorstNodalOfRelativeDimensionOne (i ≫ X ↘ Spec (.of k))) :
    i.ker.IsEffectiveCartier := by
  let : IsReduced C := hC.isReduced
  let : SyntomicOfRelativeDimension 1 (i ≫ X ↘ Spec (.of k)) := hC.syntomic
  let : IsNoetherian C := isNoetherian_of_finiteType (i ≫ X ↘ Spec (.of k))
  let : Finite (irreducibleComponents C) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hpure : IsPureDimensional 1 C :=
    ((pureRelativeDimension_iff_of_field (d := 1) (i ≫ X ↘ Spec (.of k))).mp
      inferInstance).2
  exact i.isEffectiveCartier_ker_of_isPureDimensional k
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)) hpure

end AlgebraicGeometry.Scheme.Hom
