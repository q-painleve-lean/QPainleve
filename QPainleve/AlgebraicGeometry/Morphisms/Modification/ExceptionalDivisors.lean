/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic

import TauCeti.AlgebraicGeometry.Morphisms.Modification.Centre
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition
import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint

/-!
# Exceptional divisors of a composite

Over the isomorphism locus of the first map, the additional exceptional prime divisors
of the composite are in bijection with the exceptional prime divisors of the second map
meeting that locus at their generic point. For modifications this yields the strict
decrease in the number of exceptional curves used when factoring a surface morphism
through a point blowup.

## References

* [Stacks Project, Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R).
-/

public section

open CategoryTheory TopologicalSpace
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

open IsModification in
/-- In a factorization of a modification, the exceptional prime divisor count strictly
decreases when the first map is an isomorphism over a codimension-one point mapping into
the centre of the second map. -/
theorem ncard_exceptional_divisors_lt_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [Surjective f] [IsReduced Y] [IsSeparated g] [UniversallyClosed g]
    [IsModification (f ≫ g)] [IsNoetherian X] [IrreducibleSpace X]
    {y : Y} (hy : y ∈ f.isoLocus) (hg : g y ∈ g.centre) (hc : Order.coheight y = 1) :
    {x : X | f x ∈ f.centre ∧ Order.coheight x = 1}.ncard <
      {x : X | (f ≫ g) x ∈ (f ≫ g).centre ∧ Order.coheight x = 1}.ncard := by
  let T := {x : X | (f ≫ g) x ∈ (f ≫ g).centre ∧ Order.coheight x = 1}
  have hT : T.Finite := by
    let U := (f ≫ g) ⁻¹ᵁ (f ≫ g).isoLocus
    have hd : Dense (U : Set X) := dense_preimage ‹IsModification (f ≫ g)› (dense_isoLocus (f ≫ g))
    have : Nonempty U := hd.nonempty.to_subtype
    have h := CodimensionOnePoint.finite_setOfPred_notMem U
    apply (h.image (fun x : CodimensionOnePoint X ↦ (x : X))).subset
    rintro x ⟨hx, hcx⟩
    refine ⟨⟨x, hcx⟩, ?_, rfl⟩
    have hnot : (f ≫ g) x ∉ ((f ≫ g).isoLocus : Set Z) := by
      simpa only [centre_def, Set.mem_compl_iff] using hx
    exact fun hxU ↦ hnot ((f ≫ g).mem_preimage.mp hxU)
  have hsum := f.encard_exceptional_divisors_comp g
  have ⟨hA, hC⟩ := ENat.add_lt_top.mp (hsum ▸ hT.encard_lt_top)
  have hpos : 0 < {y : Y | y ∈ f.isoLocus ∧ g y ∈ g.centre ∧ Order.coheight y = 1}.encard :=
    Set.encard_pos.mpr ⟨y, hy, hg, hc⟩
  simp only [Set.ncard_def, hsum, ENat.toNat_add hA.ne hC.ne]
  exact Nat.lt_add_of_pos_right (ENat.toNat_pos hpos.ne' hC.ne)

end AlgebraicGeometry.Scheme.Hom
