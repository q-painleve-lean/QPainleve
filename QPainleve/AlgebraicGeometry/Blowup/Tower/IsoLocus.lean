/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

import QPainleve.AlgebraicGeometry.Blowup.Point.Fiber
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus

/-!
# The isomorphism locus of a closed point tower on a smooth surface

The projection is an isomorphism precisely away from the images of the successive centers.
This criterion counts the images of infinitely near centers in the same way as proper centers.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

/-- The centre of a closed point blowup tower on a smooth surface is exactly the set of
projected centers. -/
theorem centre_toBase_eq_range_baseCenter {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f] :
    T.toBase.centre = Set.range hT.baseCenter := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  induction hT with
  | nil =>
    rw [toBase_nil, (Scheme.Hom.centre_eq_empty_iff (𝟙 X)).mpr inferInstance, Set.range_eq_empty]
  | @snoc n W U I hU p hp hI ih =>
    let s := U.toBase ≫ f
    have : SmoothOfRelativeDimension 2 s := hU.smoothOfRelativeDimension f
    have : Smooth s := SmoothOfRelativeDimension.smooth 2 s
    have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian s
    have : IsRegularLocalRing (W.presheaf.stalk p) := isRegularLocalRing_stalk_of_smooth s p
    have : IsRegular W := IsRegular.of_smooth s
    have : IsProper U.toBase := U.isProper_toBase
    have hpdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq s 2).mp
      inferInstance).2 p hp
    have hJ := hI.trans (W.ker_fromSpecResidueField_eq_vanishingIdeal p)
    have : Surjective I.blowupToBase := hJ ▸ surjective_blowupToBase_point hp hpdim
    have hc : I.blowupToBase.centre = {p} := hJ ▸ centre_blowupToBase_closed_point hp hpdim
    have hcenters : (hU.snoc p hp hI).baseCenter = Fin.snoc hU.baseCenter (U.toBase p) := by
      funext j
      refine Fin.lastCases ?_ (fun l ↦ ?_) j
      · simp only [baseCenter_snoc_last, lastCenter_eq _ p hp hI, Fin.snoc_last]
      · simp only [baseCenter_snoc_castSucc, Fin.snoc_castSucc]
    rw [toBase_snoc, Scheme.Hom.centre_comp, ih, hc, Set.image_singleton, hcenters,
      Fin.range_snoc, Set.insert_eq, Set.union_comm]

end QPainleve.BlowupTower.IsClosedPointTower
