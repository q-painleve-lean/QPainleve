/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Point.Basic
public import QPainleve.AlgebraicGeometry.Morphisms.Modification.ExceptionalDivisors

import QPainleve.AlgebraicGeometry.Blowup.Integral
import QPainleve.AlgebraicGeometry.Blowup.Point.Fiber
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Extracting a point blowup decreases the exceptional divisor count

The exceptional projective line contains a codimension-one point of the blowup.
It gives a prime divisor which is counted before the factor is extracted and disappears
from the count once the factor is removed. This is the descent step in the induction
on exceptional curves in [Stacks Project, Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R).
-/

public section

open CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

open Scheme.IdealSheafData

universe u

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
variable {p : Y} (hp : IsClosed ({p} : Set Y))

local notation "Iₚ" => vanishingIdeal (Closeds.mk (Set.singleton p) hp)
local notation "b" => blowupToBase Iₚ

attribute [local instance] specializationOrder

/-- Extracting the blowup of a closed point of a smooth integral surface strictly decreases
the exceptional divisor count if the remaining morphism is an isomorphism in codimension one
on the blowup. -/
theorem ncard_exceptional_divisors_lt_comp_pointBlowup [IsIntegral Y] [IsNoetherian Y]
    (π : Y ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 π]
    (f : X ⟶ (Iₚ).blowup) [Surjective f] [IsModification (f ≫ b)]
    [IsNoetherian X] [IrreducibleSpace X]
    (hiso : ∀ y : (Iₚ).blowup, Order.coheight y = 1 → y ∈ f.isoLocus) :
    {x : X | f x ∈ f.centre ∧ Order.coheight x = 1}.ncard <
      {x : X | (f ≫ b) x ∈ (f ≫ b).centre ∧ Order.coheight x = 1}.ncard := by
  let β := b
  let E := (Iₚ).comap β
  have hs : ((Iₚ).support : Set Y) = {p} := coe_support_vanishingIdeal _
  have hE : (E.support : Set (Iₚ).blowup) = β ⁻¹' {p} := by
    dsimp only [E]
    rw [support_comap, Closeds.coe_preimage, hs]
  have : Smooth π := SmoothOfRelativeDimension.smooth 2 π
  let : IsRegularLocalRing (Y.presheaf.stalk p) :=
    isRegularLocalRing_stalk_of_smooth π p
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq π 2).mp
    inferInstance).2 p hp
  have hclosure : (⟨closure (Set.singleton p), isClosed_closure⟩ : Closeds Y) =
      ⟨Set.singleton p, hp⟩ := SetLike.coe_injective hp.closure_eq
  have hcentre : β.centre = {p} := by
    dsimp only [β]
    rw [← hclosure]
    exact centre_blowupToBase_closed_point hp hdim
  have : IsIntegral (Iₚ).blowup := by
    rw [← hclosure]
    exact isIntegral_blowup_closed_point π hp
  have : IsLocallyNoetherian (Iₚ).blowup := LocallyOfFiniteType.isLocallyNoetherian β
  have : Surjective β := by
    dsimp only [β]
    rw [← hclosure]
    exact surjective_blowupToBase_point hp hdim
  obtain ⟨x, hx⟩ := β.surjective p
  have hmem : x ∈ E.support := by
    rw [← SetLike.mem_coe, hE]
    exact hx
  obtain ⟨y, hy, _⟩ :=
    (Iₚ).isEffectiveCartier_comap_blowupToBase.mem_support_iff_exists_codimensionOnePoint.mp hmem
  have hy' : (y : (Iₚ).blowup) ∈ β ⁻¹' {p} := hE ▸ (SetLike.mem_coe.mpr hy)
  have hyimage : β (y : (Iₚ).blowup) = p := hy'
  have hycentre : β (y : (Iₚ).blowup) ∈ β.centre := by
    simp only [hyimage, hcentre, Set.mem_singleton_iff]
  exact f.ncard_exceptional_divisors_lt_comp β (hiso y y.property) hycentre y.property

end AlgebraicGeometry.Scheme.Hom
