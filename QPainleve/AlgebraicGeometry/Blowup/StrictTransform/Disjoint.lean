/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Disjoint
public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Composition

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality

/-!
# Strict transforms under interchange of disjoint blowups

The canonical interchange of disjoint blowups identifies the strict transforms
of any closed subscheme. It also identifies the boundary ideals obtained by
adjoining the exceptional divisor at each step, as in blowups at boundary nodes.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- Interchanging blowups at disjoint centers identifies the iterated strict
transforms as closed subschemes. In each order the second center carries its
full scheme-theoretic inverse-image structure. -/
theorem comap_ker_blowupMap_blowupCommOfDisjoint (I J D : X.IdealSheafData)
    (h : Disjoint (I.support : Set X) (J.support : Set X)) :
    let I' := I.comap J.blowupToBase
    let J' := J.comap I.blowupToBase
    (I'.blowupMap (J.blowupMap D.subschemeι).ker.subschemeι).ker.comap
      (I.blowupCommOfDisjoint J h).hom =
      (J'.blowupMap (I.blowupMap D.subschemeι).ker.subschemeι).ker := by
  let I' := I.comap J.blowupToBase
  let J' := J.comap I.blowupToBase
  let a := J'.blowupToBase ≫ I.blowupToBase
  let b := I'.blowupToBase ≫ J.blowupToBase
  let e := I.blowupCommOfDisjoint J h
  let V := b ⁻¹ᵁ I.support.compl ⊓ b ⁻¹ᵁ J.support.compl
  have hbase : e.hom ≫ b = a := by simp [e, a, b, I', J']
  have hV : e.hom ⁻¹ᵁ V = a ⁻¹ᵁ J.support.compl ⊓ a ⁻¹ᵁ I.support.compl := by
    dsimp only [V]
    rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hbase,
      inf_comm]
  have : IsLocallyNoetherian J.blowup := LocallyOfFiniteType.isLocallyNoetherian J.blowupToBase
  have : IsLocallyNoetherian I'.blowup := LocallyOfFiniteType.isLocallyNoetherian I'.blowupToBase
  dsimp only
  rw [ker_blowupMap_ker_blowupMap, ker_blowupMap_ker_blowupMap]
  have ha : J'.blowupToBase ⁻¹ᵁ J'.support.compl = a ⁻¹ᵁ J.support.compl := by
    dsimp only [J', a]
    rw [compl_support_comap, Scheme.Hom.comp_preimage]
  have hb : I'.blowupToBase ⁻¹ᵁ I'.support.compl = b ⁻¹ᵁ I.support.compl := by
    dsimp only [I', b]
    rw [compl_support_comap, Scheme.Hom.comp_preimage]
  rw [ha, hb]
  rw [comap_map_of_isPullback_of_isOpenImmersion _ (isPullback_morphismRestrict e.hom V).flip,
    ← comap_comp, morphismRestrict_ι, ← comap_comp, Category.assoc, hbase, comap_comp, hV]

/-- If the support of a factor is disjoint from the center, taking a strict
transform of the product pulls back that factor unchanged as a total transform. -/
theorem ker_blowupMap_mul_of_disjoint (I D E : X.IdealSheafData)
    (h : Disjoint (I.support : Set X) (E.support : Set X)) :
    (I.blowupMap (D * E).subschemeι).ker =
      (I.blowupMap D.subschemeι).ker * E.comap I.blowupToBase := by
  let b := I.blowupToBase
  let V : I.blowup.Opens := (I.comap b).support.compl
  let W : I.blowup.Opens := (E.comap b).support.compl
  have hp : Disjoint ((I.comap b).support : Set I.blowup) ((E.comap b).support : Set I.blowup) := by
    rw [support_comap, support_comap, TopologicalSpace.Closeds.coe_preimage,
      TopologicalSpace.Closeds.coe_preimage]
    exact h.preimage b
  let U : Bool → I.blowup.Opens := fun i ↦ if i then V else W
  have hU : ⨆ i, U i = ⊤ := by
    apply top_unique
    intro x _
    apply TopologicalSpace.Opens.mem_iSup.mpr
    by_cases hx : x ∈ V
    · exact ⟨true, hx⟩
    · exact ⟨false, fun hxE ↦ Set.disjoint_left.mp hp (not_not.mp hx) hxE⟩
  -- On the exceptional complement both strict transforms equal their total transforms.
  have hV :
      (I.blowupMap (D * E).subschemeι).ker.comap V.ι =
        ((I.blowupMap D.subschemeι).ker * E.comap b).comap V.ι := by
    rw [comap_mul, comap_ker_blowupMap_subschemeι_exceptionalCompl,
      comap_ker_blowupMap_subschemeι_exceptionalCompl, comap_mul, comap_mul]
  -- On the complement of the other factor, that factor restricts to the unit ideal.
  have hW :
      (I.blowupMap (D * E).subschemeι).ker.comap W.ι =
        ((I.blowupMap D.subschemeι).ker * E.comap b).comap W.ι := by
    have hE : (E.comap b).comap W.ι = ⊤ :=
      (comap_eq_top_iff _ _).mpr (Scheme.Opens.ι_preimage_self W)
    rw [comap_mul, hE, ← one_eq_top, mul_one,
      comap_ker_blowupMap_subschemeι_eq_map_comap_of_isOpenImmersion,
      comap_ker_blowupMap_subschemeι_eq_map_comap_of_isOpenImmersion]
    rw [comap_mul, comap_comp E, hE, ← one_eq_top, mul_one]
  refine ext_of_comap_openCover (I.blowup.openCoverOfIsOpenCover U hU) ?_
  rintro (_ | _)
  · exact hW
  · exact hV

local notation "S[" I "," D "]" =>
  Scheme.Hom.ker (IdealSheafData.blowupMap I (IdealSheafData.subschemeι D))

/-- Under the interchange of disjoint centers, adjoining the exceptional divisor of
the second center commutes with taking the strict transform at the first center. -/
theorem comap_ker_blowupMap_adjoin_exceptional_blowupCommOfDisjoint
    (I J D : X.IdealSheafData) (h : Disjoint (I.support : Set X) (J.support : Set X)) :
    let I' := I.comap J.blowupToBase
    let J' := J.comap I.blowupToBase
    let D₂ := S[J,D] * J.comap J.blowupToBase
    (S[I',D₂]).comap (I.blowupCommOfDisjoint J h).hom =
      S[J',S[I,D]] * J'.comap J'.blowupToBase := by
  dsimp only
  have : IsLocallyNoetherian J.blowup := LocallyOfFiniteType.isLocallyNoetherian J.blowupToBase
  have hI : Disjoint (((I.comap J.blowupToBase).support) : Set J.blowup)
      ((J.comap J.blowupToBase).support : Set J.blowup) := by
    simpa only [support_comap, TopologicalSpace.Closeds.coe_preimage] using
      h.preimage J.blowupToBase
  rw [ker_blowupMap_mul_of_disjoint _ _ _ hI, comap_mul,
    comap_ker_blowupMap_blowupCommOfDisjoint I J D h]
  congr 1
  rw [← comap_comp, blowupCommOfDisjoint_hom_blowupToBase, comap_comap_blowupMap]

/-- The comparison of disjoint blowups identifies the strict transform after a reduced
total transform with the reduced total transform after a strict transform. -/
theorem comap_ker_blowupMap_reduced_total_blowupCommOfDisjoint
    (I J D : X.IdealSheafData) [IsReduced D.subscheme]
    (h : Disjoint (I.support : Set X) (J.support : Set X))
    (hJ : D ≤ J) (hJ' : S[I,D] ≤ J.comap I.blowupToBase)
    [IsReduced (J.comap J.blowupToBase).subscheme]
    [IsReduced ((J.comap I.blowupToBase).comap (J.comap I.blowupToBase).blowupToBase).subscheme] :
    let I' := I.comap J.blowupToBase
    let J' := J.comap I.blowupToBase
    (S[I',(D.comap J.blowupToBase).radical]).comap (I.blowupCommOfDisjoint J h).hom =
      ((S[I,D]).comap J'.blowupToBase).radical := by
  dsimp only
  have := I.isReduced_subscheme_ker_blowupMap D
  rw [J.radical_comap_blowupToBase_eq_ker_blowupMap_subschemeι_mul D hJ,
    (J.comap I.blowupToBase).radical_comap_blowupToBase_eq_ker_blowupMap_subschemeι_mul _ hJ']
  exact comap_ker_blowupMap_adjoin_exceptional_blowupCommOfDisjoint I J D h

/-- Interchanging blowups at disjoint centers identifies the boundaries obtained
by adjoining one copy of the exceptional divisor to the strict transform at
each step. The equality is on the ideals, including the exceptional components. -/
theorem comap_ker_blowupMap_mul_exceptional_blowupCommOfDisjoint (I J D : X.IdealSheafData)
    (h : Disjoint (I.support : Set X) (J.support : Set X)) :
    let I' := I.comap J.blowupToBase
    let J' := J.comap I.blowupToBase
    let D₁ := S[I,D] * I.comap I.blowupToBase
    let D₂ := S[J,D] * J.comap J.blowupToBase
    (S[I',D₂] * I'.comap I'.blowupToBase).comap (I.blowupCommOfDisjoint J h).hom =
      S[J',D₁] * J'.comap J'.blowupToBase := by
  let I' := I.comap J.blowupToBase
  let J' := J.comap I.blowupToBase
  let a := J'.blowupToBase ≫ I.blowupToBase
  let b := I'.blowupToBase ≫ J.blowupToBase
  let e := I.blowupCommOfDisjoint J h
  have hbase : e.hom ≫ b = a := by simp [e, a, b, I', J']
  have : IsLocallyNoetherian I.blowup := LocallyOfFiniteType.isLocallyNoetherian I.blowupToBase
  have : IsLocallyNoetherian J.blowup := LocallyOfFiniteType.isLocallyNoetherian J.blowupToBase
  have hI : Disjoint (I'.support : Set J.blowup)
      ((J.comap J.blowupToBase).support : Set J.blowup) := by
    simp only [I', support_comap, TopologicalSpace.Closeds.coe_preimage]
    exact h.preimage _
  have hJ : Disjoint (J'.support : Set I.blowup)
      ((I.comap I.blowupToBase).support : Set I.blowup) := by
    simp only [J', support_comap, TopologicalSpace.Closeds.coe_preimage]
    exact h.symm.preimage _
  dsimp only
  rw [ker_blowupMap_mul_of_disjoint _ _ _ hI, ker_blowupMap_mul_of_disjoint _ _ _ hJ]
  rw [comap_mul, comap_mul, comap_ker_blowupMap_blowupCommOfDisjoint I J D h]
  simp only [← comap_comp]
  have hbase' : e.hom ≫ I'.blowupToBase ≫ J.blowupToBase = a := by
    simpa only [b, Category.assoc] using hbase
  rw [hbase']
  ac_rfl

end AlgebraicGeometry.Scheme.IdealSheafData
