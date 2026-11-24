/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Logarithmic.Basic

/-!
# Images of the centers of a logarithmic point tower

If pulling back a top form with poles along an effective Cartier divisor introduces
no zeros, every center projects to the original pole support. This applies to
infinitely near centers as well as proper centers.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}
  (k : Type u) [Field k] [PerfectField k] [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] [IsIntegral X] [IsNoetherian X]
  {D : X.IdealSheafData}

/-- If the total transform of the pole ideal is contained in the ramification ideal,
every center of the tower has its image on the original pole divisor. -/
theorem range_baseCenter_subset_support_of_totalTransform_le_ramification
    (hT : IsClosedPointTower X T) (hD : D.IsEffectiveCartier)
    (h : D.comap T.toBase ≤ hT.ramificationIdealSheafToBase k) :
    Set.range hT.baseCenter ⊆ (D.support : Set X) := by
  rintro _ ⟨j, rfl⟩
  induction hT with
  | nil => exact j.elim0
  | @snoc m W U I hU p hp hI ih =>
    have hstep := hU.poleIdeal_snoc_of_totalTransform_le_ramification k hD p hp hI h
    refine Fin.lastCases ?_ (fun l ↦ ?_) j
    · have hmem : p ∈ (D.comap U.toBase).support :=
        support_antitone (le_colon _ _) hstep.2.1
      rw [support_comap, ← SetLike.mem_coe, Closeds.coe_preimage, Set.mem_preimage] at hmem
      simpa only [baseCenter_snoc_last, lastCenter_eq _ p hp hI] using hmem
    · have hV : IsClosedPointTower W (BlowupTower.nil.snoc I) := .snoc .nil p hp hI
      have hprefix := hU.totalTransform_le_ramification_of_append k hD hV
        (by simpa only [append_snoc, append_nil] using h)
      simpa only [baseCenter_snoc_castSucc] using ih hprefix l

end QPainleve.BlowupTower.IsClosedPointTower
