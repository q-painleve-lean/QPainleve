/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic
public import TauCeti.AlgebraicGeometry.Scheme.Normal

import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
import QPainleve.Topology.KrullDimension
import QPainleve.Topology.NoetherianSpace
import TauCeti.AlgebraicGeometry.Birational.Irreducible
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Centre
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition
import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint.Basic

/-!
# Exceptional divisors of a composite

Over the isomorphism locus of the first map, the additional exceptional prime divisors
of the composite are in bijection with the exceptional prime divisors of the second map
meeting that locus at their generic point. For modifications this yields the strict
decrease in the number of exceptional curves used when factoring a surface morphism
through a point blowup. A modification with irreducible Noetherian source has finitely
many exceptional prime divisors. For a modification of surfaces with normal target,
the count vanishes exactly when the morphism is an isomorphism.

## References

* [Stacks Project, Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R).
-/

public section

open CategoryTheory Order TopologicalSpace
open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y Z : Scheme.{u}}

attribute [local instance] specializationOrder

/-- The prime divisors over the centre of a composite split into those already over the first
centre and those lying over the second centre where the first map is a local isomorphism.
The latter are counted on the intermediate scheme. -/
theorem encard_exceptional_divisors_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [Surjective f] [IsReduced Y] [IsSeparated g] [UniversallyClosed g] :
    {x : X | (f ≫ g) x ∈ (f ≫ g).centre ∧ Order.coheight x = 1}.encard =
      {x : X | f x ∈ f.centre ∧ Order.coheight x = 1}.encard +
      {y : Y | y ∈ f.isoLocus ∧ g y ∈ g.centre ∧ Order.coheight y = 1}.encard := by
  classical
  let A := {x : X | f x ∈ f.centre ∧ Order.coheight x = 1}
  let B := {x : X | f x ∈ f.isoLocus ∧ g (f x) ∈ g.centre ∧ Order.coheight x = 1}
  let C := {y : Y | y ∈ f.isoLocus ∧ g y ∈ g.centre ∧ Order.coheight y = 1}
  have hdecomp : {x : X | (f ≫ g) x ∈ (f ≫ g).centre ∧ Order.coheight x = 1} = A ∪ B := by
    ext x
    simp only [Set.mem_ofPred_eq, comp_apply, centre_comp, Set.mem_union, A, B]
    constructor
    · rintro ⟨h, hc⟩
      by_cases hfx : f x ∈ f.isoLocus
      · refine Or.inr ⟨hfx, ?_, hc⟩
        rcases h with hg | ⟨y, hy, heq⟩
        · exact hg
        · -- Away from the second centre, its fiber is a singleton.
          by_contra hgy
          have hgIso : g (f x) ∈ g.isoLocus := by simpa [centre_def] using hgy
          have heq' : g y = g (f x) := heq
          have hyIso : g y ∈ g.isoLocus := heq' ▸ hgIso
          have hyfx := g.injOn_preimage_isoLocus hyIso hgIso heq'
          have hy' : y ∉ f.isoLocus := by simpa [centre_def] using hy
          exact hy' (hyfx ▸ hfx)
      · exact Or.inl ⟨by simpa [centre_def] using hfx, hc⟩
    · rintro (⟨hx, hc⟩ | ⟨_, hg, hc⟩)
      · exact ⟨Or.inr ⟨f x, hx, rfl⟩, hc⟩
      · exact ⟨Or.inl hg, hc⟩
  have hd : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro x ⟨ha, _⟩ ⟨hb, _, _⟩
    exact (by simpa [centre_def] using ha : f x ∉ f.isoLocus) hb
  have hb : Set.BijOn f B C := by
    refine ⟨?_, ?_, ?_⟩
    · rintro x ⟨hx, hg, hc⟩
      exact ⟨hx, hg, (f.coheight_eq_of_apply_mem_isoLocus hx).trans hc⟩
    · exact f.injOn_preimage_isoLocus.mono fun _ hx ↦ hx.1
    · rintro y ⟨hy, hg, hc⟩
      obtain ⟨x, rfl⟩ := f.surjective y
      exact ⟨x, ⟨hy, hg, (f.coheight_eq_of_apply_mem_isoLocus hy).symm.trans hc⟩, rfl⟩
  rw [hdecomp, Set.encard_union_eq hd]
  exact congrArg (A.encard + ·)
    (hb.injOn.encard_image.symm.trans (congrArg Set.encard hb.image_eq))

/-- A modification with irreducible Noetherian source has finitely many codimension-one
points mapping into its centre. -/
theorem finite_coheight_one_preimage_centre (f : X ⟶ Y) [IrreducibleSpace X] [IsNoetherian X]
    [IsModification f] : {x ∈ f ⁻¹' f.centre | Order.coheight x = 1}.Finite := by
  let U := f ⁻¹ᵁ f.isoLocus
  have hd : Dense (U : Set X) :=
    IsModification.dense_preimage ‹IsModification f› (IsModification.dense_isoLocus f)
  have : Nonempty U := hd.nonempty.to_subtype
  have h := CodimensionOnePoint.finite_setOfPred_notMem U
  apply (h.image (fun x : CodimensionOnePoint X ↦ (x : X))).subset
  rintro x ⟨hx, hcx⟩
  refine ⟨⟨x, hcx⟩, ?_, rfl⟩
  have hnot : f x ∉ (f.isoLocus : Set Y) := by
    simpa only [centre_def, Set.mem_compl_iff] using (Set.mem_preimage.mp hx)
  exact fun hxU ↦ hnot (f.mem_preimage.mp hxU)

/-- In a factorization of a modification, the exceptional prime divisor count strictly
decreases when the first map is an isomorphism over a codimension-one point mapping into
the centre of the second map. -/
theorem ncard_exceptional_divisors_lt_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [Surjective f] [IsReduced Y] [IsSeparated g] [UniversallyClosed g]
    [IsModification (f ≫ g)] [IsNoetherian X] [IrreducibleSpace X]
    {y : Y} (hy : y ∈ f.isoLocus) (hg : g y ∈ g.centre) (hc : Order.coheight y = 1) :
    {x : X | f x ∈ f.centre ∧ Order.coheight x = 1}.ncard <
      {x : X | (f ≫ g) x ∈ (f ≫ g).centre ∧ Order.coheight x = 1}.ncard := by
  have hT := (f ≫ g).finite_coheight_one_preimage_centre
  have hsum := f.encard_exceptional_divisors_comp g
  have ⟨hA, hC⟩ := ENat.add_lt_top.mp (hsum ▸ hT.encard_lt_top)
  have hpos : 0 < {y : Y | y ∈ f.isoLocus ∧ g y ∈ g.centre ∧ Order.coheight y = 1}.encard :=
    Set.encard_pos.mpr ⟨y, hy, hg, hc⟩
  simp only [Set.ncard_def, hsum, ENat.toNat_add hA.ne hC.ne]
  exact Nat.lt_add_of_pos_right (ENat.toNat_pos hpos.ne' hC.ne)

/-- Over a closed point of the centre, a modification with reduced source of dimension at most two
and normal integral target has a codimension-one point in the fiber if the source space is
Noetherian. -/
theorem exists_preimage_coheight_eq_one_of_mem_centre (f : X ⟶ Y) [IsReduced X]
    [NoetherianSpace X] [IsIntegral Y] [IsNormalScheme Y] [IsModification f]
    (hX : topologicalKrullDim X ≤ 2) {y : Y} (hy : y ∈ f.centre)
    (hyClosed : IsClosed ({y} : Set Y)) : ∃ x : X, f x = y ∧ coheight x = 1 := by
  have : IrreducibleSpace X := (IsModification.birational f).irreducibleSpace
  have hyIso : y ∉ f.isoLocus := by
    simpa only [centre_def, Set.mem_compl_iff, SetLike.mem_coe] using hy
  let U := f ⁻¹ᵁ f.isoLocus
  have hU : Dense (U : Set X) :=
    IsModification.dense_preimage ‹IsModification f› (IsModification.dense_isoLocus f)
  obtain ⟨z, hz⟩ := hU.nonempty
  have hη : f (genericPoint X) ∈ f.isoLocus :=
    f.mem_preimage.mp ((genericPoint_specializes z).mem_open U.isOpen hz)
  by_contra! h
  apply hyIso
  apply f.mem_isoLocus_of_finite_preimage_singleton
  refine (hyClosed.preimage f.continuous).finite_of_subset_closedPoints ?_
  intro x hx
  have he : f x = y := Set.mem_singleton_iff.mp hx
  have hxη : x ≠ genericPoint X := fun hEq ↦ hyIso (he ▸ hEq.symm ▸ hη)
  have hxPos := coheight_pos.mpr (hxη ∘ TauCeti.AlgebraicGeometry.Scheme.eq_genericPoint_of_isMax)
  have hxOne : 1 < coheight x := lt_of_le_of_ne (Order.one_le_iff_pos.mpr hxPos) (h x he).symm
  have hxTwo : 2 ≤ coheight x :=
    (ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mpr hxOne
  exact mem_closedPoints_iff.mpr
    (QPainleve.isClosed_singleton_of_le_coheight_of_topologicalKrullDim_le hX hxTwo)

/-- A modification with reduced Noetherian source of dimension at most two and normal integral
target is an isomorphism exactly when there are no exceptional prime divisors. -/
theorem ncard_exceptional_divisors_eq_zero_iff_isIso (f : X ⟶ Y) [IsReduced X]
    [IsNoetherian X] [IsIntegral Y] [IsNormalScheme Y] [IsModification f]
    (hX : topologicalKrullDim X ≤ 2) :
    {x : X | f x ∈ f.centre ∧ coheight x = 1}.ncard = 0 ↔ IsIso f := by
  have : IrreducibleSpace X := (IsModification.birational f).irreducibleSpace
  have hfinite : {x : X | f x ∈ f.centre ∧ coheight x = 1}.Finite :=
    f.finite_coheight_one_preimage_centre
  rw [Set.ncard_eq_zero hfinite, ← f.centre_eq_empty_iff]
  constructor
  · intro h
    by_contra hC
    have : CompactSpace Y := f.surjective.compactSpace f.continuous
    obtain ⟨y, hy, hyClosed⟩ := f.isClosed_centre.exists_closed_singleton
      (Set.ne_empty_iff_nonempty.mp hC)
    obtain ⟨x, hx, hcx⟩ := f.exists_preimage_coheight_eq_one_of_mem_centre hX hy hyClosed
    exact Set.eq_empty_iff_forall_notMem.mp h x ⟨hx.symm ▸ hy, hcx⟩
  · intro h
    simp [h]

end AlgebraicGeometry.Scheme.Hom
