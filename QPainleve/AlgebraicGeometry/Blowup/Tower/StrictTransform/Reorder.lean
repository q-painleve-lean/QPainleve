/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Basic

import QPainleve.AlgebraicGeometry.Blowup.Tower.IsoLocus
import QPainleve.AlgebraicGeometry.Blowup.Tower.Reorder
import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.RegularCurve
import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Transport
import QPainleve.AlgebraicGeometry.IdealSheaf.ClosedImmersion
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Strict transforms under reordering of closed point blowups

A regular irreducible curve has the same strict transform under any identification of the
final surfaces over the original surface. Consequently moving the first blowup
over a closed point to the front transports the strict-transform coefficients
by the same reindexing as the total exceptional classes. This identifies the
remaining centers on the positive section when a selected center is moved to
the front of a ruled-surface resolution, including infinitely near centers.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y Z : Scheme.{u}} {n m : ℕ} {T : BlowupTower X n Y} {U : BlowupTower X m Z}
  {C : X.IdealSheafData} {k : Type u} [Field k] [PerfectField k]
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]
  [IrreducibleSpace C.subscheme] [TauCeti.AlgebraicGeometry.IsRegular C.subscheme]

omit [TauCeti.AlgebraicGeometry.IsRegular C.subscheme] in
include f in
private theorem genericPoint_mem_isoLocus (hU : IsClosedPointTower X U)
    (hdim : topologicalKrullDim C.subscheme = 1) :
    C.subschemeι (genericPoint C.subscheme) ∈ U.toBase.isoLocus := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  by_contra h
  have hm : C.subschemeι (genericPoint C.subscheme) ∈ U.toBase.centre := by
    simpa only [Scheme.Hom.centre_def, Set.mem_compl_iff, SetLike.mem_coe] using h
  rw [hU.centre_toBase_eq_range_baseCenter f] at hm
  obtain ⟨j, hj⟩ := hm
  have hclosed : IsClosed ({genericPoint C.subscheme} : Set C.subscheme) := by
    rw [← Set.preimage_image_eq {genericPoint C.subscheme} C.subschemeι.isClosedEmbedding.injective,
      Set.image_singleton, ← hj]
    exact (hU.isClosed_baseCenter j).preimage C.subschemeι.continuous
  have hsingle : ({genericPoint C.subscheme} : Set C.subscheme) = Set.univ :=
    hclosed.closure_eq.symm.trans (genericPoint_spec C.subscheme).def
  have : Subsingleton C.subscheme := Set.subsingleton_univ_iff.mp
    (hsingle ▸ Set.subsingleton_singleton)
  have hzero := TauCeti.topologicalKrullDim_eq_zero_iff_subsingleton.mpr this
  exact zero_ne_one (hzero.symm.trans hdim)

include f in
/-- An isomorphism between the final surfaces of two closed point towers over the
same smooth surface identifies the strict transforms of a regular irreducible
curve as closed subschemes. -/
theorem comap_strictTransform_eq_of_iso_over
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower X U) (e : Y ≅ Z)
    (he : e.hom ≫ U.toBase = T.toBase) (hdim : topologicalKrullDim C.subscheme = 1) :
    (U.strictTransform C).comap e.hom = T.strictTransform C := by
  obtain ⟨a, ha⟩ := hT.exists_iso_strictTransform_regularCurve hdim
  obtain ⟨b, hb⟩ := hU.exists_iso_strictTransform_regularCurve hdim
  let s := a.inv ≫ (T.strictTransform C).subschemeι ≫ e.hom
  let t := b.inv ≫ (U.strictTransform C).subschemeι
  have hs : s ≫ U.toBase = C.subschemeι := by
    simp only [s, Category.assoc, he, ← ha, Iso.inv_hom_id_assoc]
  have ht : t ≫ U.toBase = C.subschemeι := by
    simp only [t, Category.assoc, ← hb, Iso.inv_hom_id_assoc]
  have hx := genericPoint_mem_isoLocus f hU hdim
  have hsη : U.toBase (s (genericPoint C.subscheme)) = C.subschemeι (genericPoint C.subscheme) :=
    congrArg (fun g : C.subscheme ⟶ X ↦ g (genericPoint C.subscheme)) hs
  have htη : U.toBase (t (genericPoint C.subscheme)) = C.subschemeι (genericPoint C.subscheme) :=
    congrArg (fun g : C.subscheme ⟶ X ↦ g (genericPoint C.subscheme)) ht
  have hsU : s (genericPoint C.subscheme) ∈ U.toBase ⁻¹' (U.toBase.isoLocus : Set X) := by
    rwa [Set.mem_preimage, hsη]
  have htU : t (genericPoint C.subscheme) ∈ U.toBase ⁻¹' (U.toBase.isoLocus : Set X) := by
    rwa [Set.mem_preimage, htη]
  have hη := U.toBase.injOn_preimage_isoLocus hsU htU (hsη.trans htη.symm)
  have : IsIntegral C.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsClosedImmersion s := inferInstanceAs (IsClosedImmersion
    (a.inv ≫ (T.strictTransform C).subschemeι ≫ e.hom))
  have : IsClosedImmersion t := inferInstanceAs (IsClosedImmersion
    (b.inv ≫ (U.strictTransform C).subschemeι))
  have hk : s.ker = t.ker := by
    rw [s.ker_eq_vanishingIdeal_closure_genericPoint,
      t.ker_eq_vanishingIdeal_closure_genericPoint, hη]
  have hk' : ((T.strictTransform C).subschemeι ≫ e.hom).ker = U.strictTransform C := by
    simpa only [s, t, Scheme.Hom.ker_comp_of_isIso, ker_subschemeι] using hk
  rw [← hk', Scheme.Hom.comap_ker_comp_of_isClosedImmersion, ker_subschemeι]

variable [IsIntegral X] [IsNoetherian X]

include f in
/-- When the first blowup over a point is moved to the front, the strict-transform
coefficients of a regular irreducible Cartier curve are reindexed by that move. -/
theorem strictTransformCoefficients_move_to_front
    {T : BlowupTower X (n + 1) Y} {I : X.IdealSheafData}
    {V : BlowupTower I.blowup n Z}
    (hT : IsClosedPointTower X T) (hV : IsClosedPointTower X ((BlowupTower.nil.snoc I).append V))
    (e : Y ≅ Z) (j : Fin (n + 1))
    (he : e.hom ≫ V.toBase ≫ I.blowupToBase = T.toBase)
    (hE : pullback e.hom (pullback V.toBase I.blowupExceptionalClass) = T.exceptionalClass j)
    (hTail : ∀ l, pullback e.hom (V.exceptionalClass l) = T.exceptionalClass (j.succAbove l))
    (hC : C.IsEffectiveCartier) (hdim : topologicalKrullDim C.subscheme = 1) :
    hV.strictTransformCoefficients C =
      Fin.addCases (fun _ : Fin 1 ↦ hT.strictTransformCoefficients C j)
        (hT.strictTransformCoefficients C ∘ j.succAbove) := by
  let W := (BlowupTower.nil.snoc I).append V
  have hbase : e.hom ≫ W.toBase = T.toBase := by
    simpa only [W, toBase_append, toBase_snoc, toBase_nil, Category.comp_id, Category.assoc]
      using he
  have hinv : e.inv ≫ T.toBase = W.toBase := by
    rw [← hbase, Iso.inv_hom_id_assoc]
  have hgeom := hV.comap_strictTransform_eq_of_iso_over f hT e.symm hinv hdim
  let h₁ := hT.isEffectiveCartier_strictTransform f hC
  let h₂ := hV.isEffectiveCartier_strictTransform f hC
  have hclass : pullback e.inv (mk h₁.toInvertibleSheaf) = mk h₂.toInvertibleSheaf :=
    (h₁.pullback_mk_toInvertibleSheaf (h₁.comap e.inv)).trans
      (mk_toInvertibleSheaf_congr _ _ hgeom)
  let a := Additive.ofMul (mk hC.toInvertibleSheaf)⁻¹
  let x := hT.strictTransformCoefficients C
  let y : Fin (1 + n) → ℤ := Fin.addCases (fun _ : Fin 1 ↦ x j) (x ∘ j.succAbove)
  have h := T.pullback_picardHom_move_to_front j e he hE hTail a x
  have hmark : ((W.picardMarking hV f) (a, y)).toMul =
      ((W.picardMarking hV f) (a, hV.strictTransformCoefficients C)).toMul := by
    rw [W.picardMarking_apply hV f (a, y), ← h, ← T.picardMarking_apply hT f,
      hT.picardMarking_strictTransform f hC, hV.picardMarking_strictTransform f hC,
      toMul_ofMul, toMul_ofMul, pullback_inv, hclass]
  exact (congrArg Prod.snd ((W.picardMarking hV f).injective
    (Additive.toMul.injective hmark))).symm

include f in
/-- If a chosen blowup has been moved to the front, the tail sees precisely the
original strict-transform coefficients at all the other centers. Its initial
ideal is the strict transform on the first blowup. -/
theorem strictTransformCoefficients_tail_move_to_front
    {T : BlowupTower X (n + 1) Y} {I : X.IdealSheafData}
    {V : BlowupTower I.blowup n Z}
    (hT : IsClosedPointTower X T) (hI : IsClosedPointTower X (BlowupTower.nil.snoc I))
    (hV : IsClosedPointTower I.blowup V) (e : Y ≅ Z) (j : Fin (n + 1))
    (he : e.hom ≫ V.toBase ≫ I.blowupToBase = T.toBase)
    (hE : pullback e.hom (pullback V.toBase I.blowupExceptionalClass) = T.exceptionalClass j)
    (hTail : ∀ l, pullback e.hom (V.exceptionalClass l) = T.exceptionalClass (j.succAbove l))
    (hC : C.IsEffectiveCartier) (hdim : topologicalKrullDim C.subscheme = 1) :
    hV.strictTransformCoefficients (I.blowupMap C.subschemeι).ker =
      hT.strictTransformCoefficients C ∘ j.succAbove := by
  funext l
  have h := hT.strictTransformCoefficients_move_to_front f (hI.append hV) e j he hE hTail hC hdim
  have happend := strictTransformCoefficients_append_natAdd hI hV C l
  rw [strictTransform_snoc, strictTransform_nil] at happend
  exact happend.symm.trans ((congrFun h (l.natAdd 1)).trans (Fin.addCases_right l))

end QPainleve.BlowupTower.IsClosedPointTower
