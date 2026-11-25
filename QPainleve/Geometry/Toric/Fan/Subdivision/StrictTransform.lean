/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Basic
public import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision

import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.PointClosure
import QPainleve.Geometry.Toric.Fan.Smooth

/-!
# Strict transforms of shared rays on point resolutions

Two point resolutions projecting through a common toric subdivision identify
the strict transforms of any shared ray divisor. The generic point of the ray
on the subdivision lifts to a generic point common to both strict transforms.
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ Ω : Fan i}

local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "π[" s "]" => FanHom.algebraicMap (Fan.IsSubdivision.toFanHom s)

private theorem rayBoundaryPoint_ne_baseCenter
    {Y : Scheme} {n : ℕ} {T : BlowupTower X[Φ] n Y}
    (hT : IsClosedPointTower X[Φ] T) (hΦ : Φ.IsRegular) (hN : finrank ℤ N = 2)
    (ρ : Φ.Ray) (j : Fin n) :
    (Φ.rayBoundaryPoint hΦ ρ).val ≠ hT.baseCenter j := by
  let : Nonempty Φ.cones := ⟨ρ.toCone⟩
  let f := Φ.algebraicRealizationStructureMap
  let : SmoothOfRelativeDimension 2 f :=
    hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  let : IsLocallyNoetherian X[Φ] := LocallyOfFiniteType.isLocallyNoetherian f
  have hc := coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) f
    (hT.isClosed_baseCenter j)
  intro he
  have h := (Φ.rayBoundaryPoint hΦ ρ).property
  rw [he, hc] at h
  norm_num at h

/-- Point towers on two regular toric surfaces that project through a common
subdivision have the same strict transforms of the divisors of a shared ray,
under the isomorphism of their resolving surfaces. -/
theorem IsSubdivision.comap_strictTransform_rayBoundaryIdeal
    {Y Z : Scheme} {m n : ℕ} {T : BlowupTower X[Φ] m Y} {U : BlowupTower X[Ψ] n Z}
    (s : Ω.IsSubdivision Φ) (t : Ω.IsSubdivision Ψ)
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hΩ : Ω.IsRegular) (hN : finrank ℤ N = 2)
    (hT : IsClosedPointTower X[Φ] T) (hU : IsClosedPointTower X[Ψ] U)
    (g : Y ⟶ X[Ω]) [Surjective g] (e : Y ≅ Z)
    (hg : g ≫ π[s] = T.toBase) (hg' : g ≫ π[t] = e.hom ≫ U.toBase)
    (ρ : Φ.Ray) (ρ' : Ψ.Ray) (hρ : ρ.primitiveGenerator = ρ'.primitiveGenerator) :
    (U.strictTransform (Ψ.rayBoundaryIdeal hΨ ρ')).comap e.hom =
      T.strictTransform (Φ.rayBoundaryIdeal hΦ ρ) := by
  have hray : s.liftRay ρ = t.liftRay ρ' := Ray.primitiveGenerator_injective (by
    rw [s.primitiveGenerator_liftRay, t.primitiveGenerator_liftRay, hρ])
  obtain ⟨y, hy⟩ := g.surjective (Ω.rayBoundaryPoint hΩ (s.liftRay ρ)).val
  have hsrc : T.toBase y = (Φ.rayBoundaryPoint hΦ ρ).val := by
    rw [← hg, Scheme.Hom.comp_apply, hy, s.algebraicMap_rayBoundaryPoint_liftRay hΩ hΦ]
  have htgt : U.toBase (e.hom y) = (Ψ.rayBoundaryPoint hΨ ρ').val := by
    rw [← Scheme.Hom.comp_apply, ← hg', Scheme.Hom.comp_apply, hy, hray,
      t.algebraicMap_rayBoundaryPoint_liftRay hΩ hΨ]
  have hT' := hT.strictTransform_vanishingIdeal_closure_singleton y
    (fun j ↦ hsrc ▸ rayBoundaryPoint_ne_baseCenter hT hΦ hN ρ j)
  have hU' := hU.strictTransform_vanishingIdeal_closure_singleton (e.hom y)
    (fun j ↦ htgt ▸ rayBoundaryPoint_ne_baseCenter hU hΨ hN ρ' j)
  rw [hsrc, ← Φ.rayBoundaryIdeal_def hΦ] at hT'
  rw [htgt, ← Ψ.rayBoundaryIdeal_def hΨ] at hU'
  rw [hT', hU', comap_vanishingIdeal_closure_singleton_apply]

end TauCeti.Toric.Fan
