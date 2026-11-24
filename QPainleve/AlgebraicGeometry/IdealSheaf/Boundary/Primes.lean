/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
public import TauCeti.AlgebraicGeometry.Scheme.Normal

import Mathlib.Data.Set.Card
import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus

/-!
# Boundary primes of ideal sheaves

Boundary primes are the codimension-one points in the support of an ideal sheaf.
-/

public section

open CategoryTheory Order TopologicalSpace
open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme}

/-- The generic points of the prime divisors supported on a closed subscheme. -/
def boundaryPrimes (D : X.IdealSheafData) : Set X :=
  {x | x ∈ D.support ∧ Order.coheight x = 1}

/-- Boundary primes are the codimension-one points of the ambient scheme in the support. -/
@[simp]
theorem mem_boundaryPrimes {D : X.IdealSheafData} {x : X} :
    x ∈ D.boundaryPrimes ↔ x ∈ D.support ∧ Order.coheight x = 1 :=
  (Iff.rfl)

/-- The inclusion of boundary primes into the codimension-one points of the ambient scheme. -/
def boundaryPrimeEmbedding (D : X.IdealSheafData) :
    D.boundaryPrimes ↪ CodimensionOnePoint X where
  toFun p := ⟨p.val, (mem_boundaryPrimes.mp p.property).2⟩
  inj' _ _ h := Subtype.ext (congrArg (fun q : CodimensionOnePoint X ↦ (q : X)) h)

/-- The boundary prime and its image have the same underlying point. -/
@[simp]
theorem coe_boundaryPrimeEmbedding (D : X.IdealSheafData) (p : D.boundaryPrimes) :
    (D.boundaryPrimeEmbedding p : X) = p.val := (rfl)

/-- The image of the inclusion of boundary primes consists of the codimension-one points
in the support of the ideal sheaf. -/
theorem range_boundaryPrimeEmbedding (D : X.IdealSheafData) :
    Set.range D.boundaryPrimeEmbedding = {p : CodimensionOnePoint X | (p : X) ∈ D.support} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact (mem_boundaryPrimes.mp q.property).1
  · intro hp
    exact ⟨⟨p.val, mem_boundaryPrimes.mpr ⟨hp, p.property⟩⟩, Subtype.ext rfl⟩

/-- If the support is the union of closures of specified codimension-one points,
those points are exactly its boundary primes. -/
theorem boundaryPrimes_eq_range_of_iUnion_closure {ι : Type*} (D : X.IdealSheafData)
    (η : ι → CodimensionOnePoint X)
    (hD : (D.support : Set X) = ⋃ j, closure {(η j : X)}) :
    D.boundaryPrimes = Set.range fun j ↦ (η j : X) := by
  ext x
  rw [mem_boundaryPrimes]
  constructor
  · rintro ⟨hx, hc⟩
    have hx' : x ∈ ⋃ j, closure {(η j : X)} := hD ▸ hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx'
    have he : η j = (⟨x, hc⟩ : CodimensionOnePoint X) :=
      CodimensionOnePoint.eq_of_specializes (specializes_iff_mem_closure.mpr hj)
    exact ⟨j, congrArg Subtype.val he⟩
  · rintro ⟨j, rfl⟩
    have hj : (η j : X) ∈ (D.support : Set X) := by
      rw [hD]
      exact Set.mem_iUnion.mpr ⟨j, subset_closure (Set.mem_singleton _)⟩
    exact ⟨hj, (η j).property⟩

/-- A boundary covered by the closures of distinct codimension-one points has one
prime divisor per index. -/
theorem ncard_boundaryPrimes_eq_of_iUnion_closure {ι : Type*} (D : X.IdealSheafData)
    (η : ι → CodimensionOnePoint X) (hη : Function.Injective η)
    (hD : (D.support : Set X) = ⋃ j, closure {(η j : X)}) :
    D.boundaryPrimes.ncard = Nat.card ι := by
  rw [D.boundaryPrimes_eq_range_of_iUnion_closure η hD]
  exact Set.ncard_range_of_injective (Subtype.val_injective.comp hη)

/-- Ideal sheaves with identical support have the same boundary prime set. -/
theorem boundaryPrimes_eq_of_support_eq {D E : X.IdealSheafData} (h : D.support = E.support) :
    D.boundaryPrimes = E.boundaryPrimes := by
  simp only [boundaryPrimes, h]

/-- A scheme isomorphism matches the primes of a pulled-back boundary with their images. -/
noncomputable def boundaryPrimesEquivOfIso (D : Y.IdealSheafData) (e : X ≅ Y) :
    (D.comap e.hom).boundaryPrimes ≃ D.boundaryPrimes :=
  Set.BijOn.equiv e.hom (by
    have h (x : X) : e.hom x ∈ D.boundaryPrimes ↔ x ∈ (D.comap e.hom).boundaryPrimes := by
      rw [mem_boundaryPrimes, mem_boundaryPrimes, support_comap,
        coheight_eq_of_isOpenImmersion e.hom]
      rfl
    refine ⟨fun x hx ↦ (h x).mpr hx, e.hom.isOpenEmbedding.injective.injOn, ?_⟩
    intro y hy
    obtain ⟨x, rfl⟩ := e.hom.surjective y
    exact ⟨x, (h x).mp hy, rfl⟩)

/-- The prime correspondence of an isomorphism acts by the underlying point map. -/
@[simp]
theorem boundaryPrimesEquivOfIso_apply_val (D : Y.IdealSheafData) (e : X ≅ Y)
    (x : (D.comap e.hom).boundaryPrimes) :
    (D.boundaryPrimesEquivOfIso e x).val = e.hom x.val := (rfl)

/-- The inverse prime correspondence acts by the inverse point map. -/
@[simp]
theorem boundaryPrimesEquivOfIso_symm_apply_val (D : Y.IdealSheafData) (e : X ≅ Y)
    (y : D.boundaryPrimes) :
    ((D.boundaryPrimesEquivOfIso e).symm y).val = e.inv y.val := by
  have h := congrArg Subtype.val ((D.boundaryPrimesEquivOfIso e).apply_symm_apply y)
  rw [boundaryPrimesEquivOfIso_apply_val] at h
  rw [← h, ← Scheme.Hom.comp_apply, e.hom_inv_id]
  rfl

/-- Pullback along a scheme isomorphism preserves the number of boundary primes. -/
@[simp]
theorem ncard_boundaryPrimes_eq_of_iso (e : X ≅ Y) (D : Y.IdealSheafData) :
    (D.comap e.hom).boundaryPrimes.ncard = D.boundaryPrimes.ncard :=
  Nat.card_congr (D.boundaryPrimesEquivOfIso e)

/-- Over a subset of the isomorphism locus, taking inverse images of points gives a
bijection on the boundary primes. -/
theorem bijOn_boundaryPrimes_comap_of_subset_isoLocus (D : X.IdealSheafData) (π : Y ⟶ X)
    {U : Set X} (hU : U ⊆ π.isoLocus) :
    Set.BijOn π ((D.comap π).boundaryPrimes ∩ π ⁻¹' U) (D.boundaryPrimes ∩ U) := by
  refine ⟨?_, π.injOn_preimage_isoLocus.mono (fun _ hy ↦ hU hy.2), ?_⟩
  · intro y hy
    obtain ⟨h, hc⟩ := mem_boundaryPrimes.mp hy.1
    rw [support_comap] at h
    exact ⟨mem_boundaryPrimes.mpr
      ⟨h, (π.coheight_eq_of_apply_mem_isoLocus (hU hy.2)).trans hc⟩, hy.2⟩
  · intro x hx
    obtain ⟨hxD, hxc⟩ := mem_boundaryPrimes.mp hx.1
    let W := π.isoLocus
    obtain ⟨y, hy⟩ := (π ∣_ W).surjective ⟨x, hU hx.2⟩
    have hxy : π ((π ⁻¹ᵁ W).ι y) = x := by
      rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hy]
      rfl
    have hyU : π ((π ⁻¹ᵁ W).ι y) ∈ U := hxy.symm ▸ hx.2
    have hyD : π ((π ⁻¹ᵁ W).ι y) ∈ D.support := hxy.symm ▸ hxD
    refine ⟨_, ⟨mem_boundaryPrimes.mpr ⟨?_,
      (π.coheight_eq_of_apply_mem_isoLocus (hU hyU)).symm.trans (hxy.symm ▸ hxc)⟩, hyU⟩, hxy⟩
    simpa only [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage] using hyD

/-- A boundary prime of the inverse image under a modification projects to a
boundary prime exactly when its image lies in the isomorphism locus. -/
theorem mem_boundaryPrimes_iff_mem_isoLocus_of_mem_boundaryPrimes_comap
    (D : X.IdealSheafData) (π : Y ⟶ X) [IsIntegral X] [IsNormalScheme X]
    [IsLocallyNoetherian X] [IsReduced Y] [IsModification π] {y : Y}
    (hy : y ∈ (D.comap π).boundaryPrimes) :
    π y ∈ D.boundaryPrimes ↔ π y ∈ π.isoLocus := by
  have h := D.bijOn_boundaryPrimes_comap_of_subset_isoLocus π
    (U := π.isoLocus) Set.Subset.rfl
  exact ⟨fun hp ↦ π.mem_isoLocus_of_coheight_eq_one (mem_boundaryPrimes.mp hp).2,
    fun hp ↦ (h.mapsTo (Set.mem_inter hy hp)).1⟩

/-- If a morphism is an isomorphism away from a point of coheight other than one,
its point map bijects the pulled-back boundary primes away from that point with the
original boundary primes. -/
theorem bijOn_boundaryPrimes_comap_off_point (D : X.IdealSheafData) (π : Y ⟶ X)
    {p : X} (hp : Order.coheight p ≠ 1) (hIso : ∀ x : X, x ≠ p → x ∈ π.isoLocus) :
    Set.BijOn π ((D.comap π).boundaryPrimes ∩ {y | π y ≠ p}) D.boundaryPrimes := by
  have hsub : D.boundaryPrimes ⊆ {x | x ≠ p} :=
    fun _ hx h ↦ hp (h ▸ (mem_boundaryPrimes.mp hx).2)
  have hpreimage : π ⁻¹' {x | x ≠ p} = {y | π y ≠ p} := (rfl)
  simpa only [Set.inter_eq_left.mpr hsub, hpreimage] using
    D.bijOn_boundaryPrimes_comap_of_subset_isoLocus (U := {x | x ≠ p}) π (fun _ ↦ hIso _)

end AlgebraicGeometry.Scheme.IdealSheafData
