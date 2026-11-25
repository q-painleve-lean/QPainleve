/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.Topology.PureDimension

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Reduced
import QPainleve.AlgebraicGeometry.IdealSheaf.ClosedImmersion
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Factorial
import TauCeti.AlgebraicGeometry.IdealSheaf.Product
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint.Basic
import TauCeti.AlgebraicGeometry.Scheme.LocalDimension

/-!
# Reduced closed subschemes of codimension one

In a locally factorial variety, a reduced closed subscheme of pure codimension one
is effective Cartier. Its ideal is the radical of the product of the ideals of its
prime components.
-/

public section

open CategoryTheory Order TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A reduced closed subscheme of pure codimension one with finitely many components in
a locally factorial irreducible scheme locally of finite type over a field is effective Cartier. -/
theorem isEffectiveCartier_ker_of_isPureDimensional
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] [IsReduced C]
    (k : Type u) [Field k] [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [Finite (irreducibleComponents C)] [IrreducibleSpace X] [∀ x : X, IsDomain (X.presheaf.stalk x)]
    [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    {d : ℕ} (hX : topologicalKrullDim X = d + 1) (hC : IsPureDimensional d C) :
    i.ker.IsEffectiveCartier := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : Fintype (irreducibleComponents C) := Fintype.ofFinite _
  let p (Z : irreducibleComponents C) : X := i (genericPoints.ofComponent Z)
  let J (Z : irreducibleComponents C) : X.IdealSheafData :=
    IdealSheafData.vanishingIdeal ⟨closure {p Z}, isClosed_closure⟩
  have hclosure (Z : irreducibleComponents C) : closure {p Z} = i '' (Z : Set C) := by
    rw [← (genericPoints.isGenericPoint_ofComponent Z).def,
      ← i.isClosedEmbedding.closure_image_eq, Set.image_singleton]
  have hcodim (Z : irreducibleComponents C) : coheight (p Z) = 1 := by
    have hdim := coheight_add_height_eq_topologicalKrullDim k (p Z)
    have hheight : height (p Z) = d := by
      simp only [p, i.height_apply_eq_height]
      rw [← WithBot.coe_inj, height_eq_topologicalKrullDim_closure_singleton,
        (genericPoints.isGenericPoint_ofComponent Z).def]
      exact isPureDimensional_iff.mp hC Z Z.property
    rw [hheight, hX] at hdim
    exact ENat.add_right_injective_of_ne_top (n := (d : ℕ∞)) (by simp)
      (WithBot.coe_injective (by simpa [add_comm] using hdim))
  have hcartier : (∏ Z, J Z).IsEffectiveCartier :=
    isEffectiveCartier_prod fun Z _ ↦
      IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton (hcodim Z)
  have hsupport : ((∏ Z, J Z).support : Set X) = (i.ker.support : Set X) := by
    rw [IdealSheafData.coe_support_prod, i.support_ker,
      i.isClosedEmbedding.isClosed_range.closure_eq]
    simp only [J, IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_mk, hclosure]
    rw [← Set.image_iUnion, ← Set.sUnion_eq_iUnion, sUnion_irreducibleComponents, Set.image_univ]
  rw [i.ker_eq_vanishingIdeal_support, ← SetLike.coe_injective hsupport,
    IdealSheafData.vanishingIdeal_support]
  exact hcartier.radical

end AlgebraicGeometry.Scheme.Hom
