/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.RegularCurve

import QPainleve.AlgebraicGeometry.Blowup.Tower.IsoLocus
import QPainleve.AlgebraicGeometry.IdealSheaf.ClosedImmersion
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension

/-!
# Regular components of a pulled-back pole divisor

A regular boundary curve survives in the pole divisor of a logarithmic
point-blowup tower. Its generic point lies outside the ramification support.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [IsIntegral X] {n : ℕ} {T : BlowupTower X n Y} {D C : X.IdealSheafData}
  [IsIntegral C.subscheme] [TauCeti.AlgebraicGeometry.IsRegular C.subscheme]

/-- The strict transform of a regular boundary curve lies in the pole divisor
of the tower. Since that strict transform is reduced, the containment holds
scheme-theoretically. -/
theorem le_strictTransform_of_pole_eq (hT : IsClosedPointTower X T)
    (hdim : topologicalKrullDim C.subscheme = 1) (hDC : D ≤ C)
    {E : Y.IdealSheafData} (hpole : D.comap T.toBase = E * hT.ramificationIdealSheafToBase k) :
    E ≤ T.strictTransform C := by
  let f := X ↘ Spec (CommRingCat.of k)
  let : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let C' := T.strictTransform C
  obtain ⟨e, he⟩ := hT.exists_iso_strictTransform_regularCurve hdim
  let : IsIntegral C'.subscheme := IsIntegral.of_isIso e.inv
  let y := C'.subschemeι (genericPoint C'.subscheme)
  have hy : T.toBase y = C.subschemeι (genericPoint C.subscheme) := by
    rw [← Scheme.Hom.comp_apply, ← he, Scheme.Hom.comp_apply,
      genericPoint_eq_of_isOpenImmersion e.hom]
  have hdimX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have hcodim := C.subschemeι.coheight_apply_genericPoint_eq_one_of_dim_eq_two
    k hdimX hdim
  have hram : y ∉ (hT.ramificationIdealSheafToBase k).support := by
    rw [← SetLike.mem_coe, hT.support_ramificationIdealSheafToBase k,
      Set.mem_preimage, hT.centre_toBase_eq_range_baseCenter f, hy]
    rintro ⟨j, hj⟩
    have h := coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) f
      (hT.isClosed_baseCenter j)
    rw [hj, hcodim] at h
    exact (by decide : (1 : ℕ∞) ≠ 2) h
  have htotal : y ∈ (D.comap T.toBase).support := by
    rw [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage, hy]
    apply support_antitone hDC
    rw [← SetLike.mem_coe, ← C.range_subschemeι]
    exact Set.mem_range_self _
  have hyE : y ∈ E.support := by
    rw [← SetLike.mem_coe, hpole, support_mul, Closeds.coe_sup, Set.mem_union] at htotal
    exact htotal.resolve_right hram
  suffices h : E ≤ C' from h
  rw [← C'.ker_subschemeι, C'.subschemeι.ker_eq_vanishingIdeal_closure_genericPoint,
    ← le_support_iff_le_vanishingIdeal]
  exact closure_minimal (Set.singleton_subset_iff.mpr hyE) E.support.isClosed

end QPainleve.BlowupTower.IsClosedPointTower
