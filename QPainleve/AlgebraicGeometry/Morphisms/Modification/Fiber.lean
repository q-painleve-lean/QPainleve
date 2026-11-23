/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus

import QPainleve.AlgebraicGeometry.Morphisms.Modification.ExceptionalDivisors
import Mathlib.Topology.Connected.TotallyDisconnected
import TauCeti.AlgebraicGeometry.Birational.Irreducible
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
import TauCeti.Topology.KrullDimension.Basic

/-!
# Fibers of surface modifications

Every irreducible component of a fiber above the centre of a surface modification is
a curve. In particular the exceptional divisor count detects when there is no centre
left to blow up in the factorization of a proper birational morphism.

## References

* [The Stacks Project, Lemma 33.17.3](https://stacks.math.columbia.edu/tag/0BFP).
* [The Stacks Project, Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R).
-/

public section

open CategoryTheory Order TopologicalSpace TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [IsReduced X] [IsIntegral Y] [IsNormalScheme Y] [IsModification f]

attribute [local instance] specializationOrder

section NoetherianSpace

variable [NoetherianSpace X]

/-- The generic point of each irreducible component of an exceptional fiber has
codimension one in the source, provided the source has dimension at most two. -/
theorem coheight_fiberι_eq_one_of_isGenericPoint (hX : topologicalKrullDim X ≤ 2)
    {y : Y} (hy : y ∈ f.centre) {C : Set (f.fiber y)}
    (hC : C ∈ irreducibleComponents (f.fiber y)) {z : f.fiber y} (hz : IsGenericPoint z C) :
    coheight (f.fiberι y z) = 1 := by
  have : IrreducibleSpace X := (IsModification.birational f).irreducibleSpace
  have hzImage : f (f.fiberι y z) = y := by
    rw [← fiberHomeo_apply]
    exact (f.fiberHomeo y z).property
  have hy' : y ∉ f.isoLocus := by
    simpa only [centre_def, Set.mem_compl_iff, SetLike.mem_coe] using hy
  have hz0 : coheight (f.fiberι y z) ≠ 0 := by
    intro h
    have he := Scheme.eq_genericPoint_of_isMax (coheight_eq_zero.mp h)
    rw [he, f.genericPoint_eq_of_isDominant] at hzImage
    obtain ⟨w, hw⟩ := (IsModification.dense_isoLocus f).nonempty
    exact hy' (hzImage ▸ (genericPoint_specializes w).mem_open f.isoLocus.isOpen hw)
  by_contra! hz1
  have hle (a : X) : coheight a ≤ 2 :=
    WithBot.coe_le_coe.mp ((TauCeti.coheight_le_topologicalKrullDim a).trans hX)
  have hz2 : 2 ≤ coheight (f.fiberι y z) :=
    (ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mpr
      (lt_of_le_of_ne (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hz0)) hz1.symm)
  -- A point of codimension two is closed, so this component would be a singleton.
  have hsingle : C = {z} := by
    refine Set.Subset.antisymm (fun a ha ↦ Set.mem_singleton_iff.mpr ?_) ?_
    · apply (f.fiberι y).isEmbedding.injective
      by_contra hne
      have hle' := Scheme.le_iff_specializes.mpr
        ((hz.specializes_iff_mem.mpr ha).map (f.fiberι y).continuous)
      have hstep := coheight_add_one_le (lt_of_le_of_ne hle' hne)
      exact (by decide : ¬ (2 : ℕ∞) + 1 ≤ 2)
        ((add_le_add_left hz2 1).trans (hstep.trans (hle _)))
    · simpa only [Set.singleton_subset_iff] using hz.mem
  have : NoetherianSpace (f.fiber y) := (f.fiberι y).isEmbedding.isInducing.noetherianSpace
  obtain ⟨U, hU, hne, hUC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  have hOpen : IsOpen ({z} : Set (f.fiber y)) :=
    (hne.subset_singleton_iff.mp (hUC.trans hsingle.le)) ▸ hU
  have hq (x : X) (he : f x = y) (hx : f.fiberι y z = x) : f.QuasiFiniteAt x := by
    -- Identify the chosen point of the fiber with the point used in the quasi-finite criterion.
    subst y
    have heq : z = f.asFiber x :=
      (f.fiberι (f x)).isEmbedding.injective (hx.trans (f.fiberι_asFiber x).symm)
    exact quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (heq ▸ hOpen)
  exact hy' (hzImage ▸ f.mem_isoLocus_of_quasiFiniteAt (hq _ hzImage rfl))

/-- Every point over the centre of a surface modification is a specialization of an
exceptional prime divisor's generic point in the same fiber. -/
theorem exists_coheight_one_specializes_of_mem_centre (hX : topologicalKrullDim X ≤ 2)
    {x : X} (hx : f x ∈ f.centre) :
    ∃ z : X, coheight z = 1 ∧ f z = f x ∧ z ⤳ x := by
  let a := f.asFiber x
  let C := irreducibleComponent a
  have hC : C ∈ irreducibleComponents (f.fiber (f x)) :=
    irreducibleComponent_mem_irreducibleComponents a
  obtain ⟨z, hz⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents _ hC)
  refine ⟨f.fiberι (f x) z, f.coheight_fiberι_eq_one_of_isGenericPoint hX hx hC hz, ?_, ?_⟩
  · rw [← fiberHomeo_apply]
    exact (f.fiberHomeo (f x) z).property
  · have hza := hz.specializes_iff_mem.mpr (mem_irreducibleComponent : a ∈ C)
    simpa only [a, fiberι_asFiber] using hza.map (f.fiberι (f x)).continuous

end NoetherianSpace

/-- If the exceptional prime divisors of a surface modification `f` are also exceptional
for `g`, and the exceptional fibers of `f` are preconnected, then `g` is constant on the
fibers of `f`. -/
theorem factorsThrough_of_exceptional_divisors_subset {Z : Scheme.{u}} (g : X ⟶ Z)
    [NoetherianSpace X] [IsNoetherian Z] [IsIntegral Z] [IsNormalScheme Z] [IsModification g]
    (hX : topologicalKrullDim X ≤ 2) (hZ : topologicalKrullDim Z ≤ 2)
    (hsub : {x : X | f x ∈ f.centre ∧ coheight x = 1} ⊆
      {x : X | g x ∈ g.centre ∧ coheight x = 1})
    (hconn : ∀ y ∈ f.centre, _root_.IsPreconnected (f ⁻¹' {y})) :
    Function.FactorsThrough g f := by
  intro x y hxy
  by_cases hx : f x ∈ f.centre
  · have hclosed := g.centre_subset_closedPoints hZ
    have hmap : Set.MapsTo g (f ⁻¹' {f x}) g.centre := by
      intro w hw
      have hw' : f w = f x := hw
      obtain ⟨z, hz, hzw, hsp⟩ :=
        f.exists_coheight_one_specializes_of_mem_centre hX (hw'.symm ▸ hx)
      have hz' := (hsub ⟨(hzw.trans hw').symm ▸ hx, hz⟩).1
      have hzg := (hsp.map g.continuous).mem_closed (mem_closedPoints_iff.mp (hclosed hz'))
        (Set.mem_singleton (g z))
      exact (Set.mem_singleton_iff.mp hzg).symm ▸ hz'
    exact (hconn _ hx).constant_of_mapsTo
      ((g.finite_centre hZ).isDiscrete_of_subset_closedPoints hclosed)
      g.continuous.continuousOn hmap rfl hxy.symm
  · have hx' : f x ∈ f.isoLocus := by
      simpa only [centre_def, Set.mem_compl_iff, SetLike.mem_coe, not_not] using hx
    have hy' : f y ∈ f.isoLocus := hxy ▸ hx'
    exact congrArg g (f.injOn_preimage_isoLocus hx' hy' hxy)

/-- A surface modification has no exceptional prime divisors exactly when it is an
isomorphism. -/
theorem ncard_exceptional_divisors_eq_zero_iff [IsNoetherian X] (hX : topologicalKrullDim X ≤ 2) :
    {x : X | f x ∈ f.centre ∧ coheight x = 1}.ncard = 0 ↔ IsIso f := by
  have : IrreducibleSpace X := (IsModification.birational f).irreducibleSpace
  have hfinite : {x : X | f x ∈ f.centre ∧ coheight x = 1}.Finite :=
    f.finite_coheight_one_preimage_centre
  rw [← f.centre_eq_empty_iff, Set.ncard_eq_zero hfinite]
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨x, rfl⟩ := f.surjective y
    obtain ⟨z, hz, he, _⟩ := f.exists_coheight_one_specializes_of_mem_centre hX hy
    exact Set.eq_empty_iff_forall_notMem.mp h z ⟨he.symm ▸ hy, hz⟩
  · intro h
    simp [h]

end AlgebraicGeometry.Scheme.Hom
