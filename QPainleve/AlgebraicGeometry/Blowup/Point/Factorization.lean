/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Point.Basic
public import QPainleve.AlgebraicGeometry.Morphisms.Modification.ExceptionalDivisors

import QPainleve.AlgebraicGeometry.Blowup.Integral
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor

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

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
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
  obtain ⟨e, _⟩ :=
    SmoothOfRelativeDimension.exists_iso_projectiveLine_exceptional_blowup_closedPoint π p hp
  let j : projectiveLine k ⟶ (Iₚ).blowup := e.hom ≫ E.subschemeι
  have hpoint (z : projectiveLine k) : β (j z) = p := by
    have hmem : E.subschemeι (e.hom z) ∈ (E.support : Set (Iₚ).blowup) :=
      E.range_subschemeι ▸ Set.mem_range_self _
    rw [hE] at hmem
    exact hmem
  have hpcentre : p ∈ β.centre := by
    rw [centre_def, Set.mem_compl_iff]
    intro hpi
    let a := projectiveLine.infinity k
    let c := projectiveLine.polynomialChartι k 0 (genericPoint (Spec (.of (Polynomial k))))
    have ha : β (j a) ∈ (β.isoLocus : Set Y) := by
      rw [hpoint a]
      exact hpi
    have hc : β (j c) ∈ (β.isoLocus : Set Y) := by
      rw [hpoint c]
      exact hpi
    have heq := β.injOn_preimage_isoLocus ha hc ((hpoint a).trans (hpoint c).symm)
    have : IsClosedImmersion j := inferInstance
    have hac : a = c := j.isClosedEmbedding.injective heq
    have hne : a ∉ Set.range (projectiveLine.polynomialChartι k 0) :=
      projectiveLine.infinity_notMem_range_polynomialChartι k
    exact hne ⟨_, hac.symm⟩
  have : IsIntegral (Iₚ).blowup := by
    have hclosure : (⟨closure (Set.singleton p), isClosed_closure⟩ : Closeds Y) =
        ⟨Set.singleton p, hp⟩ := SetLike.coe_injective hp.closure_eq
    have h := isIntegral_blowup_closed_point π hp
    rwa [hclosure] at h
  have : IsLocallyNoetherian (Iₚ).blowup := LocallyOfFiniteType.isLocallyNoetherian β
  have hmem : j (projectiveLine.infinity k) ∈ E.support :=
    SetLike.mem_coe.mp (hE.symm ▸ (hpoint _ : j (projectiveLine.infinity k) ∈ β ⁻¹' {p}))
  obtain ⟨y, hy, _⟩ :=
    (Iₚ).isEffectiveCartier_comap_blowupToBase.mem_support_iff_exists_codimensionOnePoint.mp hmem
  have hy' : (y : (Iₚ).blowup) ∈ β ⁻¹' {p} := hE ▸ (SetLike.mem_coe.mpr hy)
  have hyimage : β (y : (Iₚ).blowup) = p := hy'
  have hycentre : β (y : (Iₚ).blowup) ∈ β.centre := by
    rw [hyimage]
    exact hpcentre
  exact f.ncard_exceptional_divisors_lt_comp β (hiso y y.property) hycentre y.property

end AlgebraicGeometry.Scheme.Hom
