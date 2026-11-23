/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint

import Mathlib.Data.Set.Card
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus

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

/-- A boundary covered by the closures of distinct codimension-one points has one
prime divisor per index. -/
theorem ncard_boundaryPrimes_eq_of_iUnion_closure {ι : Type*} (D : X.IdealSheafData)
    (η : ι → CodimensionOnePoint X) (hη : Function.Injective η)
    (hD : (D.support : Set X) = ⋃ j, closure {(η j : X)}) :
    D.boundaryPrimes.ncard = Nat.card ι := by
  have h : D.boundaryPrimes = Set.range fun j ↦ (η j : X) := by
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
  rw [h]
  exact Set.ncard_range_of_injective (Subtype.val_injective.comp hη)

/-- Ideal sheaves with identical support have the same boundary prime set. -/
theorem boundaryPrimes_eq_of_support_eq {D E : X.IdealSheafData} (h : D.support = E.support) :
    D.boundaryPrimes = E.boundaryPrimes := by
  simp only [boundaryPrimes, h]

/-- Pullback along a scheme isomorphism preserves the number of boundary primes. -/
@[simp]
theorem ncard_boundaryPrimes_eq_of_iso (e : X ≅ Y) (D : Y.IdealSheafData) :
    (D.comap e.hom).boundaryPrimes.ncard = D.boundaryPrimes.ncard := by
  have h (x : X) : e.hom x ∈ D.boundaryPrimes ↔ x ∈ (D.comap e.hom).boundaryPrimes := by
    rw [mem_boundaryPrimes, mem_boundaryPrimes, support_comap, coheight_eq_of_isOpenImmersion e.hom]
    rfl
  apply Set.BijOn.ncard_eq (f := e.hom)
  refine ⟨fun x hx ↦ (h x).mpr hx, e.hom.isOpenEmbedding.injective.injOn, ?_⟩
  intro y hy
  obtain ⟨x, rfl⟩ := e.hom.surjective y
  exact ⟨x, (h x).mp hy, rfl⟩

/-- If a morphism is an isomorphism away from a point of coheight other than one,
its point map bijects the pulled-back boundary primes away from that point with the
original boundary primes. -/
theorem bijOn_boundaryPrimes_comap_off_point (D : X.IdealSheafData) (π : Y ⟶ X)
    {p : X} (hp : Order.coheight p ≠ 1) (hIso : ∀ x : X, x ≠ p → x ∈ π.isoLocus) :
    Set.BijOn π ((D.comap π).boundaryPrimes ∩ {y | π y ≠ p}) D.boundaryPrimes := by
  refine ⟨?_, π.injOn_preimage_isoLocus.mono (fun y hy ↦ hIso (π y) hy.2), ?_⟩
  · intro y hy
    obtain ⟨h, hc⟩ := mem_boundaryPrimes.mp hy.1
    rw [support_comap] at h
    exact mem_boundaryPrimes.mpr
      ⟨h, (π.coheight_eq_of_apply_mem_isoLocus (hIso (π y) hy.2)).trans hc⟩
  · intro x hx
    obtain ⟨hxD, hxc⟩ := mem_boundaryPrimes.mp hx
    have hne : x ≠ p := fun he ↦ hp (he ▸ hxc)
    let U := π.isoLocus
    obtain ⟨y, hy⟩ := (π ∣_ U).surjective ⟨x, hIso x hne⟩
    have hxy : π ((π ⁻¹ᵁ U).ι y) = x := by
      rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hy]
      rfl
    exact ⟨_, ⟨mem_boundaryPrimes.mpr
      ⟨by
        rw [support_comap]
        exact (show π ((π ⁻¹ᵁ U).ι y) ∈ D.support from hxy.symm ▸ hxD),
        (π.coheight_eq_of_apply_mem_isoLocus (hxy.symm ▸ hIso x hne)).symm.trans
          (hxy.symm ▸ hxc)⟩,
      (show π ((π ⁻¹ᵁ U).ι y) ≠ p from hxy.symm ▸ hne)⟩, hxy⟩

end AlgebraicGeometry.Scheme.IdealSheafData
