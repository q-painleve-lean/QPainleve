/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.NumberedRays
public import QPainleve.SignedClusterModularGroup.Realization.Presentation

import QPainleve.Geometry.Toric.Fan.Presentation.Genus
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import TauCeti.LinearAlgebra.Matrix.Dual

/-!
# Constancy of the marked boundary in a toric presentation

The common auxiliary Picard marking determines the surviving rays of a nodal
contraction. The orientation and the chosen initial component fix the order
of the rays, giving the same marked boundary classes at every center with a
nodal model.
-/

public section

open AlgebraicGeometry CategoryTheory Module
open QPainleve.CharacterTorus
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}

variable (Q : CompleteToricPresentation i b r L γ)

local instance : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance : NeZero Q.length := Q.neZero
local instance : PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

/-- The Picard intersection form of the toric surface with one exceptional summand
per center is right-separating. -/
theorem separatingRight_auxiliaryPicardForm
    [Q.fan.algebraicRealization.IsProjectiveOver ℂ]
    [SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S)] :
    (LinearMap.BilinForm.prod (Chow.intersectionBilinForm ℂ Q.fan.algebraicRealization)
      (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))).SeparatingRight := by
  let : IsRationalOver (Q.fan.algebraicRealization ↘ S) := Q.isRationalOver_fan
  have hperf := Chow.isPerfPair_intersectionBilinForm_of_isRationalOver ℂ Q.fan.algebraicRealization
  refine LinearMap.BilinForm.separatingRight_prod_iff.mpr ⟨hperf.separatingRight, ?_⟩
  intro y hy
  exact (dotProductBilin_isPerfPair ℤ (Fin r)).separatingRight y
    (fun x ↦ by simpa only [LinearMap.neg_apply, neg_eq_zero] using hy x)

private theorem exists_nodalContraction {c : GeometricRealization.Point Centers[r]}
    {M : MarkedSurface ℂ n H XTor[r]} (h : Q.HasNodalModel c M) (hD : D[M].IsEffectiveCartier) :
    ∃ p : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c] M,
      p.IsNodalContraction := by
  let : IsIntegral M.surface := M.integral
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : PrestableFamily (D[M].subscheme ↘ S) := M.prestable_boundaryImage
  obtain ⟨p, _, _, T, e, hT, he⟩ := (Q.hasNodalModel_iff c M).mp h
  exact ⟨p, hD, h.hasToricPresentation.genus_blowupComponent_eq_zero hD, _, _, T, hT, e, he.symm⟩

/-- Two marked nodal models of one complete toric presentation have the same
boundary class at every label. This holds also for repeated centers and cycles
with one or two components. -/
theorem boundaryClass_eq_of_matching_nodal_models {c d : GeometricRealization.Point Centers[r]}
    {M P : MarkedSurface ℂ n H XTor[r]} (hc : Q.HasNodalModel c M) (hd : Q.HasNodalModel d P)
    (hM : D[M].IsEffectiveCartier) (hP : D[P].IsEffectiveCartier) :
    M.boundaryClass hM = P.boundaryClass hP := by
  let : Q.fan.algebraicRealization.IsProjectiveOver ℂ :=
    Q.fan.isProjectiveOver_algebraicRealization_of_isComplete Q.regular Q.complete b
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  let : SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S) := by
    rw [← hN, Q.fan.algebraicRealization_over]
    exact Q.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Q.regular
  obtain ⟨p, hp⟩ := Q.exists_nodalContraction hc hM
  obtain ⟨q, hq⟩ := Q.exists_nodalContraction hd hP
  have hrays := p.numberedBoundaryRays_eq_of_nodalContractions q hp hq
    Q.separatingRight_auxiliaryPicardForm
  exact p.boundaryClass_eq_of_range_numberedBoundaryRays_eq q hp hq
    (Q.inclusion_injective hc) (congrArg (fun e : ZMod n ↪ Q.fan.Ray ↦ Set.range e) hrays)

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
