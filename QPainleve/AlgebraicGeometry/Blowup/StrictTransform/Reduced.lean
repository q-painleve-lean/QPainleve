/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Reduced total transforms under blowups

The reduced total transform of a reduced closed subscheme containing the center
is the union of the strict transform and the reduced exceptional divisor.
When the exceptional divisor itself is reduced, the union is cut out by the
product of the two ideal sheaves. The strict transform is the schematic closure
described by `ker_blowupMap_subschemeι_eq_map_comap`.
-/

public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} (I D : X.IdealSheafData)

local notation "π" => I.blowupToBase
local notation "E" => I.comap I.blowupToBase
local notation "S" => Scheme.Hom.ker (I.blowupMap D.subschemeι)

/-- The strict transform of a reduced closed subscheme is cut out by the vanishing
ideal of the closure of its inverse image off the exceptional divisor. -/
theorem ker_blowupMap_subschemeι_eq_vanishingIdeal [IsReduced D.subscheme] :
    S = vanishingIdeal (.closure (((D.comap π).support : Set I.blowup) \ (E).support)) := by
  let j := Scheme.Opens.ι (E).support.compl
  have hj : IsOpenImmersion (j ≫ π) := by
    dsimp only [j]
    rw [compl_support_comap, ← morphismRestrict_ι]
    infer_instance
  have hD : vanishingIdeal D.support = D :=
    vanishingIdeal_support.trans ((isReduced_subscheme_iff_radical_eq D).mp inferInstance)
  have hjD : ((D.comap π).comap j) =
      vanishingIdeal ((D.comap π).support.preimage j.continuous) := by
    rw [← comap_comp, ← hD, comap_vanishingIdeal_of_isOpenImmersion]
    congr 1
    apply SetLike.coe_injective
    simp only [support_comap, Closeds.coe_preimage, ← Set.preimage_comp]
    rfl
  rw [ker_blowupMap_subschemeι_eq_map_comap, hjD, map_vanishingIdeal,
    Closeds.coe_preimage, Set.image_preimage_eq_inter_range,
    Scheme.Opens.range_ι, Closeds.coe_compl, Set.sdiff_eq]

/-- The strict transform of a reduced closed subscheme is reduced. -/
theorem isReduced_subscheme_ker_blowupMap [IsReduced D.subscheme] :
    IsReduced (S).subscheme := by
  rw [ker_blowupMap_subschemeι_eq_vanishingIdeal]
  infer_instance

/-- The strict transform of the union of two reduced closed subschemes is the union
of their strict transforms, with the scheme-theoretic ideal of the union. -/
theorem ker_blowupMap_subschemeι_inf (A B : X.IdealSheafData)
    [IsReduced A.subscheme] [IsReduced B.subscheme] :
    (I.blowupMap (A ⊓ B).subschemeι).ker =
      (I.blowupMap A.subschemeι).ker ⊓ (I.blowupMap B.subschemeι).ker := by
  have hA : vanishingIdeal A.support = A :=
    vanishingIdeal_support.trans (A.isReduced_subscheme_iff_radical_eq.mp inferInstance)
  have hB : vanishingIdeal B.support = B :=
    vanishingIdeal_support.trans (B.isReduced_subscheme_iff_radical_eq.mp inferInstance)
  have hAB : A ⊓ B = vanishingIdeal (A.support ⊔ B.support) := by
    rw [vanishingIdeal_sup, hA, hB]
  have : IsReduced (A ⊓ B).subscheme := by rw [hAB]; infer_instance
  have hs : (A ⊓ B).support = A.support ⊔ B.support := by
    rw [hAB]
    exact SetLike.coe_injective (coe_support_vanishingIdeal _)
  rw [ker_blowupMap_subschemeι_eq_vanishingIdeal,
    ker_blowupMap_subschemeι_eq_vanishingIdeal I A,
    ker_blowupMap_subschemeι_eq_vanishingIdeal I B, ← vanishingIdeal_sup]
  congr 1
  apply SetLike.coe_injective
  simp only [Closeds.coe_closure, Closeds.coe_sup, support_comap, hs,
    Closeds.coe_preimage, Set.preimage_union, Set.union_sdiff_distrib, closure_union]

/-- If a reduced closed subscheme contains the blowup center and the exceptional
divisor is reduced, the ideal of the reduced total transform is the product of
the strict-transform ideal and the exceptional ideal. -/
theorem radical_comap_blowupToBase_eq_ker_blowupMap_subschemeι_mul
    [IsReduced D.subscheme] [IsReduced (E).subscheme] (hDI : D ≤ I) :
    (D.comap π).radical = S * E := by
  let Z := (D.comap π).support
  have hE : vanishingIdeal (E).support = E :=
    vanishingIdeal_support.trans ((isReduced_subscheme_iff_radical_eq E).mp inferInstance)
  have hS := ker_blowupMap_subschemeι_eq_vanishingIdeal I D
  have hZ : Closeds.closure ((Z : Set I.blowup) \ (E).support) ⊔ (E).support = Z := by
    apply SetLike.coe_injective
    rw [Closeds.coe_sup, Closeds.coe_closure]
    have hsub : ((E).support : Set I.blowup) ⊆ Z :=
      SetLike.coe_subset_coe.mpr (support_antitone (comap_mono π hDI))
    refine Set.Subset.antisymm (Set.union_subset
      (closure_minimal Set.sdiff_subset Z.isClosed) hsub) ?_
    calc (Z : Set I.blowup) = _ := (Set.sdiff_union_of_subset hsub).symm
      _ ⊆ _ := Set.union_subset_union_left _ subset_closure
  calc
    (D.comap π).radical = vanishingIdeal Z := vanishingIdeal_support.symm
    _ = S * E := by
      rw [← inf_ker_blowupMap_subschemeι_exceptional, ← hZ, vanishingIdeal_sup, ← hS, hE]

end AlgebraicGeometry.Scheme.IdealSheafData
