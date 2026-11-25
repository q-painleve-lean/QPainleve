/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.NumberedRays
public import QPainleve.SignedClusterModularGroup.Realization.Presentation

import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.LinearAlgebra.BilinearForm.Prod
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

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}

variable (Q : CompleteToricPresentation i b r L γ)

local instance : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance : NeZero Q.length := Q.neZero
local instance : PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

/-- The complete regular toric model is a smooth surface over ℂ. -/
theorem smoothOfRelativeDimension_fan :
    SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S) := by
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  rw [← hN, Q.fan.algebraicRealization_over]
  exact Q.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Q.regular

/-- The Picard intersection form of the toric surface with one exceptional summand
per center is perfect. -/
theorem isPerfPair_auxiliaryPicardForm
    [Q.fan.algebraicRealization.IsProjectiveOver ℂ]
    [SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S)] :
    (LinearMap.BilinForm.prod (Chow.intersectionBilinForm ℂ Q.fan.algebraicRealization)
      (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))).IsPerfPair := by
  let : IsRationalOver (Q.fan.algebraicRealization ↘ S) := Q.isRationalOver_fan
  refine LinearMap.BilinForm.isPerfPair_prod_iff.mpr
    ⟨Chow.isPerfPair_intersectionBilinForm_of_isRationalOver ℂ Q.fan.algebraicRealization, ?_⟩
  convert LinearMap.IsPerfPair.compl₁₂
    (dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ))
    (LinearEquiv.neg ℤ) (LinearEquiv.refl ℤ _) using 1
  ext x y
  simp

local notation "Fiber[" c "," M "]" =>
  ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion
    (pointsEquiv ℂ (Fin r → ℤ) (Subtype.mk (Over.Hom.left c) (Over.w c))) M

local instance instProjectiveFan : Q.fan.algebraicRealization.IsProjectiveOver ℂ :=
  Q.fan.isProjectiveOver_algebraicRealization_of_isComplete Q.regular Q.complete b

local instance instSmoothFan : SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S) := by
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  rw [← hN, Q.fan.algebraicRealization_over]
  exact Q.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Q.regular

/-- A complete toric presentation determines its surviving rays in boundary order
at every nodal contraction, including at repeated centers. -/
theorem numberedBoundaryRays_eq_of_nodalContractions {c d : GeometricRealization.Point Centers[r]}
    {M P : MarkedSurface ℂ n H XTor[r]} {p : Fiber[c,M]} {q : Fiber[d,P]}
    (hp : p.IsNodalContraction) (hq : q.IsNodalContraction) :
    p.numberedBoundaryRays hp.cartier = q.numberedBoundaryRays hq.cartier := by
  exact p.numberedBoundaryRays_eq_of_nodalContractions q hp hq
    Q.isPerfPair_auxiliaryPicardForm.separatingRight

/-- Two marked nodal models of one complete toric presentation have the same
boundary class at every label. This holds also for repeated centers and cycles
with one or two components. -/
theorem boundaryClass_eq_of_matching_nodal_models {c d : GeometricRealization.Point Centers[r]}
    {M P : MarkedSurface ℂ n H XTor[r]} (hc : Q.HasNodalModel c M) (hd : Q.HasNodalModel d P)
    (hM : D[M].IsEffectiveCartier) (hP : D[P].IsEffectiveCartier) :
    M.boundaryClass hM = P.boundaryClass hP := by
  obtain ⟨p, hp⟩ := hc.exists_isNodalContraction hM
  obtain ⟨q, hq⟩ := hd.exists_isNodalContraction hP
  have hrays := Q.numberedBoundaryRays_eq_of_nodalContractions hp hq
  exact p.boundaryClass_eq_of_range_numberedBoundaryRays_eq q hp hq
    (Q.inclusion_injective hc) (congrArg (fun e : ZMod n ↪ Q.fan.Ray ↦ Set.range e) hrays)

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
