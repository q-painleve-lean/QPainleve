/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Orders of vanishing over the isomorphism locus

Orders of rational functions agree on the opens where a birational morphism is an isomorphism.
-/

public section

open CategoryTheory
open TauCeti.AlgebraicGeometry.Scheme (ord_functionFieldMap)

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- A dominant morphism preserves the order of a rational function at every point over
its isomorphism locus. -/
theorem ord_functionFieldMap_of_mem_isoLocus (f : X ⟶ Y) [IsDominant f]
    {x : X} (hx : f x ∈ f.isoLocus) (a : Y.functionField) :
    X.ord (f.functionFieldMap a) x = Y.ord a (f x) := by
  let U := f ⁻¹ᵁ f.isoLocus
  let z : U := ⟨x, f.mem_preimage.mpr hx⟩
  let : Nonempty U := ⟨z⟩
  let : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨x, z.property⟩)
  have : IsOpenImmersion (U.ι ≫ f) := by
    rw [← morphismRestrict_ι]
    have : IsIso (f ∣_ f.isoLocus) := f.le_isoLocus_iff.mp le_rfl
    infer_instance
  calc
    _ = U.toScheme.ord (U.ι.functionFieldMap (f.functionFieldMap a)) z :=
      (ord_functionFieldMap U.ι _ z).symm
    _ = U.toScheme.ord ((U.ι ≫ f).functionFieldMap a) z := by
      rw [functionFieldMap_comp, CommRingCat.comp_apply]
    _ = _ := ord_functionFieldMap (U.ι ≫ f) a z

end AlgebraicGeometry.Scheme.Hom
