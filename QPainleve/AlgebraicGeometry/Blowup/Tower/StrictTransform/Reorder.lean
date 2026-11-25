/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Basic

import QPainleve.AlgebraicGeometry.Blowup.Tower.Reorder
import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.RegularCurve

/-!
# Strict transforms under reordering of closed point blowups

Moving the first blowup over a closed point to the front reindexes the
strict-transform coefficients by the same permutation as the total exceptional
classes. This identifies the remaining centers on the positive section when a
selected center is moved to the front of a ruled-surface resolution, including
infinitely near centers.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y Z : Scheme.{u}} {n : ℕ}
  {C : X.IdealSheafData} {k : Type u} [Field k] [PerfectField k]
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]
  [IrreducibleSpace C.subscheme] [TauCeti.AlgebraicGeometry.IsRegular C.subscheme]

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
