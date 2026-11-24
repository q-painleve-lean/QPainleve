/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Boundary
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Node
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Log canonical classes of nodal point blowup towers

The reduced total boundary accounts for one copy of each component, and the
remaining multiplicities of the total transform form the ramification ideal.
Consequently the logarithmic canonical class pulls back under the tower.
This is the anticanonical boundary calculation for the toric blowups of
[Gross, Hacking and Keel, §1][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S1
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsNodalBoundaryTower

open LineBundleClass

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [IsIntegral X] [IsNoetherian X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] {D : X.IdealSheafData}
  {n : ℕ} {T : BlowupTower X n Y}
  (hT : IsNodalBoundaryTower D (X ↘ Spec (.of k)) (𝟙 X) T)
  (hD : D.IsEffectiveCartier)
  (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ Spec (.of k)))

local notation "s" => (X ↘ Spec (CommRingCat.of k))
local notation "K(" Z ")" => mk (canonicalBundle k Z 2)

include hD hN in
/-- On a nodal tower, the total boundary ideal is the reduced total boundary
ideal times the ramification ideal of the projection. -/
theorem comap_toBase_eq_radical_mul_ramification :
    D.comap T.toBase =
      (D.comap T.toBase).radical * hT.isClosedPointTower.ramificationIdealSheafToBase k := by
  induction hT with
  | nil =>
    have : IsReduced D.subscheme := hN.isReduced
    rw [toBase_nil, comap_id, IsClosedPointTower.ramificationIdealSheafToBase_nil,
      mul_top, D.isReduced_subscheme_iff_radical_eq.mp inferInstance]
  | @snoc m Z U I hU p hp hI hn ih =>
    let P := (D.comap U.toBase).radical
    let t := U.toBase ≫ s
    have : SmoothOfRelativeDimension 2 t := hU.isClosedPointTower.smoothOfRelativeDimension s
    have : IsIntegral Z := hU.isClosedPointTower.isIntegral s
    have : IsProper U.toBase := U.isProper_toBase
    have : QuasiCompact t := inferInstanceAs (QuasiCompact (U.toBase ≫ s))
    obtain ⟨hP, hNP⟩ := radical_comap_toBase hU hD hN
    have hn' : P.IsNodeOfReducedBoundary t p := by
      simpa only [P, t, isNodeOfReducedBoundary_radical, Category.comp_id] using hn
    have hstep := hP.comap_blowupToBase_eq_radical_mul_exceptional_of_node hNP hp hn'
    dsimp only at hstep
    rw [← Z.ker_fromSpecResidueField_eq_vanishingIdeal, ← hI] at hstep
    have hsupport : ((D.comap U.toBase).comap I.blowupToBase).radical =
        (P.comap I.blowupToBase).radical := by
      rw [← vanishingIdeal_support, ← vanishingIdeal_support (I := P.comap _)]
      simp only [support_comap, P, support_radical]
    rw [IsClosedPointTower.ramificationIdealSheafToBase_snoc, toBase_snoc, comap_comp, hsupport]
    calc
      _ = (P.comap I.blowupToBase) *
          (hU.isClosedPointTower.ramificationIdealSheafToBase k).comap I.blowupToBase := by
        rw [ih, comap_mul]
      _ = ((P.comap I.blowupToBase).radical * I.comap I.blowupToBase) *
          (hU.isClosedPointTower.ramificationIdealSheafToBase k).comap I.blowupToBase :=
        congrArg (· * _) hstep
      _ = _ := mul_assoc _ _ _

/-- The log canonical class with the reduced total boundary is the pullback
of the log canonical class of the original pair. -/
theorem logCanonicalClass_radical_comap_toBase :
    letI : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ s⟩
    letI : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
      hT.isClosedPointTower.smoothOfRelativeDimension s
    K(Y) * (mk (hT.radical_comap_toBase hD hN).1.toInvertibleSheaf)⁻¹ =
      pullback T.toBase (K(X) * (mk hD.toInvertibleSheaf)⁻¹) := by
  let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ s⟩
  let : T.toBase.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
    hT.isClosedPointTower.smoothOfRelativeDimension s
  let hRam := hT.isClosedPointTower.isEffectiveCartier_ramificationIdealSheafToBase k
  let hR := (hT.radical_comap_toBase hD hN).1
  let hTot := hT.isClosedPointTower.isEffectiveCartier_totalTransform s hD
  have hProd := TauCeti.isEffectiveCartier_mul hR hRam
  have hIdeal := hT.comap_toBase_eq_radical_mul_ramification hD hN
  have hPic : pullback T.toBase (mk hD.toInvertibleSheaf) =
      mk hR.toInvertibleSheaf * mk hRam.toInvertibleSheaf := by
    rw [hD.pullback_mk_toInvertibleSheaf hTot,
      mk_toInvertibleSheaf_congr hTot hProd hIdeal, mk_toInvertibleSheaf_mul]
  have hRamEq := hT.isClosedPointTower.ramificationIdealSheafToBase_def k
  have hK := mk_canonicalBundle_eq_pullback_mul_inv_ramification k T.toBase 2 (hRamEq ▸ hRam)
  rw [← mk_toInvertibleSheaf_congr hRam _ hRamEq] at hK
  rw [hK, pullback_mul, pullback_inv, hPic, mul_inv_rev]
  ac_rfl

/-- A nodal tower has anticanonical reduced total boundary exactly when its base
boundary is anticanonical. -/
theorem canonicalClass_radical_comap_toBase_iff :
    letI : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ s⟩
    letI : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
      hT.isClosedPointTower.smoothOfRelativeDimension s
    mk (hT.radical_comap_toBase hD hN).1.toInvertibleSheaf = K(Y) ↔
      mk hD.toInvertibleSheaf = K(X) := by
  rw [eq_comm (a := mk (hT.radical_comap_toBase hD hN).1.toInvertibleSheaf), ← mul_inv_eq_one,
    hT.logCanonicalClass_radical_comap_toBase hD hN]
  rw [← pullback_one T.toBase, (hT.isClosedPointTower.injective_pullback_toBase s).eq_iff,
    mul_inv_eq_one, eq_comm]

end QPainleve.BlowupTower.IsNodalBoundaryTower
