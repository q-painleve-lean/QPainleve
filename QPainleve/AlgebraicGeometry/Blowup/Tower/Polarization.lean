/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Contraction
public import TauCeti.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Morphisms.Modification.Polarization
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Descent from a common polarization on a blowup resolution

A curve on a common resolution is exceptional for a projection exactly when the
pullback of an ample class from that projection's target has degree zero on the curve.
Equal pullbacks therefore identify the sets of exceptional curves and the two targets.
-/

public section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [PerfectField k] {X Y V W : Scheme.{u}} {m n : ℕ}
  {T : BlowupTower X m V} {U : BlowupTower Y n W}

local notation "S" => Spec (CommRingCat.of k)

variable [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))] [IsIntegral X] [IsIntegral Y]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]

/-- Two closed-point blowup towers on the same resolution with equal pullbacks of ample
classes have uniquely isomorphic targets, compatibly with the projections and the field. -/
theorem existsUnique_iso_over_of_pullback_eq
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Y U)
    (e : V ≅ W) (hbase : T.toBase ≫ (X ↘ S) = e.hom ≫ U.toBase ≫ (Y ↘ S))
    {a : LineBundleClass X} {b : LineBundleClass Y} (ha : a.IsAmple) (hb : b.IsAmple)
    (h : pullback T.toBase a = pullback (e.hom ≫ U.toBase) b) :
    ∃! d : X ≅ Y, T.toBase ≫ d.hom = e.hom ≫ U.toBase ∧ d.hom ≫ (Y ↘ S) = X ↘ S := by
  let : V.Over S := ⟨T.toBase ≫ (X ↘ S)⟩
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  have : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ S)
  have := T.isProper_toBase
  have : IsProper (V ↘ S) := inferInstanceAs (IsProper (T.toBase ≫ (X ↘ S)))
  have : IsIntegral V := hT.isIntegral (X ↘ S)
  have : IsIntegral W := hU.isIntegral (Y ↘ S)
  have : T.toBase.IsOver S := ⟨rfl⟩
  have : (e.hom ≫ U.toBase).IsOver S := ⟨(Category.assoc _ _ _).trans hbase.symm⟩
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsRegular X := IsRegular.of_smooth (X ↘ S)
  have : IsRegular Y := IsRegular.of_smooth (Y ↘ S)
  have : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
  have : IsModification U.toBase := hU.isModification_of_smoothOfRelativeDimension_two (Y ↘ S)
  have : SmoothOfRelativeDimension 2 (V ↘ S) := hT.smoothOfRelativeDimension (X ↘ S)
  have hV := topologicalKrullDim_eq_of_smoothOfRelativeDimension (V ↘ S) (n := 2)
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have hY := topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y ↘ S) (n := 2)
  have : IsModification e.hom := IsModification.of_isIso _
  have hc : (e.hom ≫ U.toBase).centre = U.toBase.centre := by
    rw [Scheme.Hom.centre_comp, e.hom.centre_eq_empty_iff.mpr inferInstance, Set.image_empty,
      Set.union_empty]
  refine hT.existsUnique_iso_over_of_eq_exceptional_divisors hU e (X ↘ S) (Y ↘ S) ?_ hbase
  intro x hx
  let p : CodimensionOnePoint V := ⟨x, hx⟩
  have hTdeg :=
    T.toBase.mem_centre_iff_intersectionNumber_pullback_eq_zero (k := k) hV hX.le p ha
  have hUdeg :=
    (e.hom ≫ U.toBase).mem_centre_iff_intersectionNumber_pullback_eq_zero (k := k) hV hY.le p hb
  rw [h, ← hUdeg, hc, Scheme.Hom.comp_apply] at hTdeg
  exact hTdeg

end QPainleve.BlowupTower.IsClosedPointTower
