/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Presentation.Basic
public import QPainleve.SignedClusterModularGroup.Realization.Presentation

import QPainleve.Geometry.Toric.Fan.Logarithmic.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Presentation.Canonical
import QPainleve.SignedClusterModularGroup.Realization.Boundary
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Anticanonical marked fibers

A marked nodal fiber supplies the actual toric presentation of its boundary
ideal. In particular, each such fiber with Cartier boundary is anticanonical.
This allows the anticanonical equality to be applied at the centers selected
by a boundary period argument.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative
open Module (Basis)
open QPainleve.BlowupTower QPainleve.CharacterTorus
open TauCeti.AlgebraicGeometry TauCeti.Toric TauCeti.Toric.Fan
open Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation.HasNodalModel

open GeometricRealization (Point)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "A[" r "]" => (Fin r → ℤ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ A[r])
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {b : Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n] {L γ : Type}
  [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}
  {Q : CompleteToricPresentation i b r L γ} {c : Point Centers[r]}
  {M : MarkedSurface ℂ n H XTor[r]}

/-- The ordered nodal model of a marked fiber gives a toric presentation
of its actual boundary ideal. -/
theorem hasToricPresentation (h : Q.HasNodalModel c M) :
    (D[M]).HasToricPresentation (M.surface ↘ S) b i := by
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  obtain ⟨p, Y, d, T, e, hT, hp⟩ := (Q.hasNodalModel_iff c M).mp h
  refine ToricPresentation.hasToricPresentation
    ⟨Q.fan, Q.regular, Q.complete, Q.rays, _, d, Y, T, hT, e.symm,
      ?_, ?_⟩
  · simpa only [Iso.symm_hom, Category.assoc] using
      (congrArg (· ≫ M.surface ↘ S) hp).symm.trans p.projection_over
  · rw [← radical_comap_of_isOpenImmersion, ← comap_comp, Iso.symm_hom, ← hp]
    have hR := radical_eq_comap_internalBlowupBoundary_of_support_eq b Q.rays _
      (Iso.refl _) (by simpa only [Iso.refl_hom, comap_id] using p.support_comap)
    simpa only [Iso.refl_hom, comap_id] using hR

/-- The Cartier boundary of an ordered marked nodal fiber is anticanonical. -/
theorem canonicalClass (h : Q.HasNodalModel c M) (hD : (D[M]).IsEffectiveCartier) :
    letI : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
    LineBundleClass.mk hD.toInvertibleSheaf =
      LineBundleClass.mk (canonicalBundle ℂ M.surface 2) := by
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : IsIntegral M.surface := M.integral
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : IsNoetherian M.surface := isNoetherian_of_finiteType (M.surface ↘ S)
  let : PrestableFamily ((D[M]).subscheme ↘ S) := M.prestable_boundaryImage
  exact h.hasToricPresentation.canonicalClass hD (by
    rw [← over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne)

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation.HasNodalModel
